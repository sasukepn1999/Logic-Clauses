import os
import sys

"""Đọc dữ liệu từ file_name

Trả về danh sách các sự kiên, luật, truy vấn
"""
def ReadData(file_name):
	if not os.path.exists(file_name):
		return None

	inpfile = open(file_name, "r")
	inp = inpfile.readlines()
	inpfile.close()

	string = ""
	for i in range(len(inp)):
		line = inp[i].replace(' ', '')
		line = line.replace('\t', '')
		if len(line) > 0 and line[0] == '%':
			line = ""
		if len(line) > 1 and line[0] == '/' and line[1] == '*':
			line = ""
		string = string + line

	string = string.replace('\n', '')
	string = string[0 : len(string) - 1]

	data = list(string.split('.'))
	return data

def isLowerCase(char):
	return ('a' <= char and char <= 'z')

def isUpperCase(char):
	return ('A' <= char and char <= 'Z')

def inAlphabet(char):
	return isLowerCase(char) or isUpperCase(char)

#	Kiểm tra có phải 1 sự kiện
def isPredicate(string):
	if string.count('(') == 1 and string.count(')') == 1 and string[len(string) - 1] == ')' and string[0] != '(':
		for i in range(len(string)):
			if string [i] == '(':
				return True
			if not inAlphabet(string[i]) and string[i] != '_' and not ('0' <= string[i] and string[i] <= '9'):
				print("fgdgdfg",string)
				break

	return False

#	Tách 1 sự kiện
def Predicate(string):
	string = string[:len(string) - 1]
	string = string.replace('(', ',')
	result = list(string.split(','))
	return result

# 	Kiểm tra có phải biểu thức logic so sánh 
# 	Vế trái   phép so sánh logic   vế phải
def isExpressionLogic(string):
	if string.count('(') == 0 and string.count(')') == 0 and len(string) > 0:
		return True

	return False

#	Tách biểu thức logic so sánh
def ExpressionLogic(string):
	exp = ""
	for i in range(len(string)):
		if not inAlphabet(string[i]):
			exp = exp + string[i]
		elif len(exp) > 0:
			break;

	result = [exp]
	result.extend(string.split(exp))

	return result

#	Xóa cặp ngoặc đóng mở thừa ngoài cùng
def DeleteBracket(string):
	first = 0
	while first < len(string) and string[first] == '(':
		first += 1

	last = len(string)
	while last > 0 and string[last - 1] == ')':
		last -= 1

	value = 0
	i = first + 1
	while first > 0 and i < last:
		if string[i] == '(':
			value += 1
		elif string[i] == ')':
			value -= 1

		if value < 0:
			first -= 1
			value = 0
		i += 1

	while first > 0:
		string = string[1:len(string) - 1]
		first -= 1

	return string

#	Sao chép dữ liệu từ mảng 2 chiều
def copyList2D(list2D):
	result = []
	for line in list2D:
		predicate = []
		for element in line:
			predicate.append(element)
		result.append(predicate)
	return result

#	Chuẩn hóa các luật về dạng p1 ^ p2 ^ ... => Q
#	Đầu vào:
#		q là list gồm Q, p1, p2,...
#		p, r là biểu thức thỏa p ^ r ^ p1 ^ p2 ^ ... => Q
#	Gọi đệ quy, tách theo mức độ ưu tiên OR -> AND
#		Dừng lại khi p, r là vị từ cơ sở hoặc biểu thức logic so sánh
def Standardized(q, p, r):
	global rules
	p = DeleteBracket(p)

	if isPredicate(p) or isExpressionLogic(p):
		if isPredicate(p):
			res = Predicate(p)
		else:
			res = ExpressionLogic(p)

		tmpQ = copyList2D(q)
		tmpQ.append(res)
		if (r == ""):
			if rules.count(tmpQ) == 0:
				rules.append(tmpQ)
			return

		Standardized(tmpQ, r, "")
		return

	# 	OR(;)
	value = 0
	pre = 0
	for i in range(0, len(p)):
		if p[i] == '(':
			value += 1
		elif p[i] == ')':
			value -= 1
		elif p[i] == ';' and value == 0:
			p1 = p[pre:i]
			p2 = r
			pre = i + 1
			tmpQ = copyList2D(q)
			Standardized(tmpQ, p1, p2)

	if pre != 0:
		p1 = p[pre:len(p)]
		p2 = r
		tmpQ = copyList2D(q)
		Standardized(tmpQ, p1, p2)
		return

	#	AND(,)
	value = 0
	for i in range(0, len(p)):
		if p[i] == '(':
			value += 1
		elif p[i] == ')':
			value -= 1
		elif p[i] == ',' and value == 0:
			p1 = p[0:i]
			p2 = p[i + 1: len(p)]
			if r != "":
				p2 = p2 + "," + r
			tmpQ = copyList2D(q)
			Standardized(tmpQ, p1, p2)
			return

	return

#	Phân loại dữ liệu
def Classify(data):
	global predicates_base
	global predicates
	global facts
	global rules
	global queries

	for string in data:
		if ":-" in string:
			rule = list(string.split(":-"))
			q = Predicate(rule[0])
			if predicates.count(q[0]) == 0:
				predicates.append(q[0])
			Standardized([Predicate(rule[0])], rule[1], "")
		elif "?-" in string:
			string = string[2:len(string)]
			query = Predicate(string)
			queries.append(query)
		else:
			fact = Predicate(string)
			facts.append(fact)
			if predicates_base.count(fact[0]) == 0:
				predicates_base.append(fact[0])

	char = '*'
	for i1 in range(len(rules)):
		for i2 in range(len(rules[i1])):
			for i3 in range(1, len(rules[i1][i2])):
				const = rules[i1][i2][i3]
				if len(const) > 0 and const[len(const) - 1] == char:
					continue

				for j1 in range(i1):
					if rules[i1][0][0] == rules[j1][0][0]:
						continue
					for j2 in range(len(rules[j1])):
						for j3 in range(1, len(rules[j1][j2])):
							if const == rules[j1][j2][j3]:
								const = const + char

				if len(const) > 0 and const[len(const) - 1] == char:
					for i4 in range(len(rules[i1][i2]) - 1, i3 - 1, -1):
						if rules[i1][i2][i3] == rules[i1][i2][i4]:
							rules[i1][i2][i4] = const

	# outrules = open("rules.txt", "w")
	# for line in rules:
	# 	outrules.write(str(line) + "\n")
	# outrules.close()

	return

#	Kiểm tra 1 chuỗi có phải là biến
def isVariable(string):
	return isUpperCase(string[0]) or string == "_"

#	Kiểm tra 1 chuỗi có phải là hằng
def isConstant(string):
	return isLowerCase(string[0]) or string.count('\'') == 2

#	Thay các giá trị tương ứng của các biến từ theta vào vị từ q
#		q = father(X, Y);	theta = {x : "philip"}
#		=> q = father(philip, Y)
def Subst(q, theta):
	for i in range(1, len(q)):
		if len(q[i]) > 0 and isUpperCase(q[i][0]):
			string = theta.get(q[i])
			if string != None:
				q[i] = string

	return
		
#	Suy diễn lùi (dùng dfs)
#	Đầu vào:
#		goal: danh sách câu hỏi cần kiểm chứng
#		theta: danh sách các biến đã được thay thế và giá trị tương ứng
def BackwardChaining(goal, theta):
	global facts
	global rules
	global predicates_base
	global answer

	if len(goal) == 0:
		res = theta.copy()
		answer.append(res)
		return

	# print(goal)
	# print(theta, "\n")

	#	Ưu tiên các vị từ thay vì phép toán logic so sánh
	if goal[0][0] == "\\=":
		for i in range(len(goal) - 1, 0, -1):
			if goal[i][0] != "\\=":
				tmp = goal[0]
				goal[0] = goal[i]
				goal[i] = tmp
				break

	# 	Lấy 1 vị từ cần chứng minh ra khỏi goal
	q = goal[0]
	Subst(q, theta)
	goal = goal[1:len(goal)]

	#	Vị từ cần chứng minh thuộc tập cơ sở
	
	if q[0] == "\\=":
		new_theta = theta.copy()
		new_list_goal = copyList2D(goal)
		if q[1] != q[2]:
			BackwardChaining(new_list_goal, new_theta)
		return

	if q[0] in predicates_base:
		if q in facts:
			new_theta = theta.copy()
			new_list_goal = copyList2D(goal)
			BackwardChaining(new_list_goal, new_theta)
		else:
			for line in facts:
				if q[0] == line[0]:
					new_theta = theta.copy()
					new_list_goal = copyList2D(goal)
					check = True
					for i in range(1, len(q)):
						if isConstant(q[i]):
							if q[i] == line[i]:
								continue
							check = False
							break
						if new_theta.get(q[i], None) == None:
							new_theta[q[i]] = line[i]
						else:
							check = False
							break
					if not check:
						continue

					BackwardChaining(new_list_goal, new_theta)
		return

	#	Vị từ cần chứng minh được xây dừng từ tập cơ sở
	else:
		for line in rules:
			if q[0] == line[0][0]:
				new_list_goal = copyList2D(goal)
				new_theta = theta.copy()
				for i in range(1, len(line)):
					new_goal = line[i].copy()
					for j in range(1, len(new_goal)):
						for k in range(1, len(line[0])):
							if new_goal[j] == line[0][k]:
								new_goal[j] = q[k]
									
					if new_list_goal.count(new_goal) == 0:
						new_list_goal.append(new_goal)
				BackwardChaining(new_list_goal, new_theta)
		return

	return

#	Trả lời các truy vấn
#	Đầu vào:
#		index: thứ tự câu truy vấn
#		query: câu truy vấn
#		output: đầu ra
def Answer(index, query, output):
	global predicates_base
	global predicates
	global answer

	new_query = query.copy()
	_query = query.copy()

	#	In ra câu truy vấn
	stringQ = str(index) + " ?- " + query[0] + "("
	stringQ = stringQ + query[1]
	for line in query[2:]:
		stringQ = stringQ + ", " + line
	stringQ = stringQ + ")."
	print(stringQ)

	output.write(stringQ + "\n")

	#	Vị từ cần chứng minh không thuộc cơ sở tri thức
	if predicates_base.count(query[0]) == 0 and predicates.count(query[0]) == 0:
		print("false.\n")
		output.write("false\n\n")
		return

	#	Chuẩn hóa câu truy vấn và tạo danh sách các biến ứng với các hằng của câu truy vấn 
	count = 0
	theta = {}		#	dictionary
	if predicates_base.count(query[0]) > 0:
		for i in range(1, len(query)):
			if isConstant(query[i]):
				theta[query[i]] = query[i]
				count += 1
			else:
				if query[i] == "_":
					count += 1
	else:
		for line in rules:
			if query[0] == line[0][0]:
				for i in range(1, len(query)):
					if isConstant(query[i]):
						theta[line[0][i]] = query[i]
						count += 1
					else:
						new_query[i] = line[0][i]
						if query[i] == "_":
							count += 1
					query[i] = line[0][i]
				break

	#	Gọi câu truy vấn
	answer = []
	goal = [query]
	BackwardChaining(goal, theta)

	#	Trả lời câu truy vấn

	#	Câu truy vấn không chứa biến
	if count == len(_query) - 1:
		if len(answer) > 0:
			out = "true.\n\n"
		else:
			out = "false.\n\n"
		print(out, end = "")
		output.write(out)

	#	Câu truy vấn chứa biến
	else:
		res = []
		for line in answer:
			new_res = []
			for i in range(1, len(new_query)):
				if isVariable(new_query[i]) and _query[i] != "_":
					new_res.append(_query[i] + " = " + line.get(new_query[i], ""))

			if new_res != []: # and res.count(new_res) == 0:
				res.append(new_res)

		out = ""
		for index, line in enumerate(res, 1):
			for i in range(len(line) - 1):
				out = out + line[i] + " , "

			out = out + line[len(line) - 1]

			if index != len(res):
				out = out + " ;\n"
			else:
				out = out + ".\n"

		if len(res) == 0:
			out = out + ".\n"
		print(out)

		output.write(out + "\n")
		return

	return

#	Luồng xử lý chính
def Process():
	global queries

	if len(sys.argv) > 2:
		print("Usage:", sys.argv[0], "input_file_name or", sys.argv[0])
		return

	if len(sys.argv) == 2:
		file_name = sys.argv[1]
	else:
		file_name = input("input_file_name = ")

	data = ReadData(file_name)

	if data == None:
		print("\nFiles does not exist!")
		return
	print()
	
	# data = ReadData("input1.txt")

	# outfile = open("kb.txt", "w")
	# for i in data:
	# 	outfile.write(i + "\n")
	# outfile.close()

	Classify(data)

	output = open("output.txt", "w")
	for index, query in enumerate(queries, 1):
		Answer(index, query, output)
	output.close()

	return

#	biến toàn cục
predicates_base = []
predicates = []
facts = []
rules = []
queries = []
answer = []

#	hàm main()
if __name__ == '__main__':
	Process()