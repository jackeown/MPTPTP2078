%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:06:55 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   37 ( 122 expanded)
%              Number of clauses        :   26 (  57 expanded)
%              Number of leaves         :    5 (  28 expanded)
%              Depth                    :    8
%              Number of atoms          :  182 ( 690 expanded)
%              Number of equality atoms :   59 ( 232 expanded)
%              Maximal formula depth    :   25 (   5 average)
%              Maximal clause size      :   44 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t141_funct_2,conjecture,(
    ! [X1,X2] : r1_tarski(k1_funct_2(X1,X2),k4_partfun1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t141_funct_2)).

fof(d2_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k1_funct_2(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ? [X5] :
              ( v1_relat_1(X5)
              & v1_funct_1(X5)
              & X4 = X5
              & k1_relat_1(X5) = X1
              & r1_tarski(k2_relat_1(X5),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_funct_2)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(d5_partfun1,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_partfun1(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ? [X5] :
              ( v1_relat_1(X5)
              & v1_funct_1(X5)
              & X4 = X5
              & r1_tarski(k1_relat_1(X5),X1)
              & r1_tarski(k2_relat_1(X5),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_partfun1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2] : r1_tarski(k1_funct_2(X1,X2),k4_partfun1(X1,X2)) ),
    inference(assume_negation,[status(cth)],[t141_funct_2])).

fof(c_0_6,plain,(
    ! [X14,X15,X16,X17,X19,X20,X21,X22,X23,X25] :
      ( ( v1_relat_1(esk2_4(X14,X15,X16,X17))
        | ~ r2_hidden(X17,X16)
        | X16 != k1_funct_2(X14,X15) )
      & ( v1_funct_1(esk2_4(X14,X15,X16,X17))
        | ~ r2_hidden(X17,X16)
        | X16 != k1_funct_2(X14,X15) )
      & ( X17 = esk2_4(X14,X15,X16,X17)
        | ~ r2_hidden(X17,X16)
        | X16 != k1_funct_2(X14,X15) )
      & ( k1_relat_1(esk2_4(X14,X15,X16,X17)) = X14
        | ~ r2_hidden(X17,X16)
        | X16 != k1_funct_2(X14,X15) )
      & ( r1_tarski(k2_relat_1(esk2_4(X14,X15,X16,X17)),X15)
        | ~ r2_hidden(X17,X16)
        | X16 != k1_funct_2(X14,X15) )
      & ( ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20)
        | X19 != X20
        | k1_relat_1(X20) != X14
        | ~ r1_tarski(k2_relat_1(X20),X15)
        | r2_hidden(X19,X16)
        | X16 != k1_funct_2(X14,X15) )
      & ( ~ r2_hidden(esk3_3(X21,X22,X23),X23)
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25)
        | esk3_3(X21,X22,X23) != X25
        | k1_relat_1(X25) != X21
        | ~ r1_tarski(k2_relat_1(X25),X22)
        | X23 = k1_funct_2(X21,X22) )
      & ( v1_relat_1(esk4_3(X21,X22,X23))
        | r2_hidden(esk3_3(X21,X22,X23),X23)
        | X23 = k1_funct_2(X21,X22) )
      & ( v1_funct_1(esk4_3(X21,X22,X23))
        | r2_hidden(esk3_3(X21,X22,X23),X23)
        | X23 = k1_funct_2(X21,X22) )
      & ( esk3_3(X21,X22,X23) = esk4_3(X21,X22,X23)
        | r2_hidden(esk3_3(X21,X22,X23),X23)
        | X23 = k1_funct_2(X21,X22) )
      & ( k1_relat_1(esk4_3(X21,X22,X23)) = X21
        | r2_hidden(esk3_3(X21,X22,X23),X23)
        | X23 = k1_funct_2(X21,X22) )
      & ( r1_tarski(k2_relat_1(esk4_3(X21,X22,X23)),X22)
        | r2_hidden(esk3_3(X21,X22,X23),X23)
        | X23 = k1_funct_2(X21,X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_funct_2])])])])])])).

fof(c_0_7,negated_conjecture,(
    ~ r1_tarski(k1_funct_2(esk8_0,esk9_0),k4_partfun1(esk8_0,esk9_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

fof(c_0_8,plain,(
    ! [X6,X7,X8,X9,X10] :
      ( ( ~ r1_tarski(X6,X7)
        | ~ r2_hidden(X8,X6)
        | r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_2(X9,X10),X9)
        | r1_tarski(X9,X10) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | r1_tarski(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_9,plain,(
    ! [X27,X28,X29,X30,X32,X33,X34,X35,X36,X38] :
      ( ( v1_relat_1(esk5_4(X27,X28,X29,X30))
        | ~ r2_hidden(X30,X29)
        | X29 != k4_partfun1(X27,X28) )
      & ( v1_funct_1(esk5_4(X27,X28,X29,X30))
        | ~ r2_hidden(X30,X29)
        | X29 != k4_partfun1(X27,X28) )
      & ( X30 = esk5_4(X27,X28,X29,X30)
        | ~ r2_hidden(X30,X29)
        | X29 != k4_partfun1(X27,X28) )
      & ( r1_tarski(k1_relat_1(esk5_4(X27,X28,X29,X30)),X27)
        | ~ r2_hidden(X30,X29)
        | X29 != k4_partfun1(X27,X28) )
      & ( r1_tarski(k2_relat_1(esk5_4(X27,X28,X29,X30)),X28)
        | ~ r2_hidden(X30,X29)
        | X29 != k4_partfun1(X27,X28) )
      & ( ~ v1_relat_1(X33)
        | ~ v1_funct_1(X33)
        | X32 != X33
        | ~ r1_tarski(k1_relat_1(X33),X27)
        | ~ r1_tarski(k2_relat_1(X33),X28)
        | r2_hidden(X32,X29)
        | X29 != k4_partfun1(X27,X28) )
      & ( ~ r2_hidden(esk6_3(X34,X35,X36),X36)
        | ~ v1_relat_1(X38)
        | ~ v1_funct_1(X38)
        | esk6_3(X34,X35,X36) != X38
        | ~ r1_tarski(k1_relat_1(X38),X34)
        | ~ r1_tarski(k2_relat_1(X38),X35)
        | X36 = k4_partfun1(X34,X35) )
      & ( v1_relat_1(esk7_3(X34,X35,X36))
        | r2_hidden(esk6_3(X34,X35,X36),X36)
        | X36 = k4_partfun1(X34,X35) )
      & ( v1_funct_1(esk7_3(X34,X35,X36))
        | r2_hidden(esk6_3(X34,X35,X36),X36)
        | X36 = k4_partfun1(X34,X35) )
      & ( esk6_3(X34,X35,X36) = esk7_3(X34,X35,X36)
        | r2_hidden(esk6_3(X34,X35,X36),X36)
        | X36 = k4_partfun1(X34,X35) )
      & ( r1_tarski(k1_relat_1(esk7_3(X34,X35,X36)),X34)
        | r2_hidden(esk6_3(X34,X35,X36),X36)
        | X36 = k4_partfun1(X34,X35) )
      & ( r1_tarski(k2_relat_1(esk7_3(X34,X35,X36)),X35)
        | r2_hidden(esk6_3(X34,X35,X36),X36)
        | X36 = k4_partfun1(X34,X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_partfun1])])])])])])).

fof(c_0_10,plain,(
    ! [X12,X13] :
      ( ( r1_tarski(X12,X13)
        | X12 != X13 )
      & ( r1_tarski(X13,X12)
        | X12 != X13 )
      & ( ~ r1_tarski(X12,X13)
        | ~ r1_tarski(X13,X12)
        | X12 = X13 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_11,plain,
    ( X1 = esk2_4(X2,X3,X4,X1)
    | ~ r2_hidden(X1,X4)
    | X4 != k1_funct_2(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,negated_conjecture,
    ( ~ r1_tarski(k1_funct_2(esk8_0,esk9_0),k4_partfun1(esk8_0,esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( r2_hidden(X2,X5)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | X2 != X1
    | ~ r1_tarski(k1_relat_1(X1),X3)
    | ~ r1_tarski(k2_relat_1(X1),X4)
    | X5 != k4_partfun1(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( r1_tarski(k2_relat_1(esk2_4(X1,X2,X3,X4)),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_17,plain,
    ( esk2_4(X1,X2,k1_funct_2(X1,X2),X3) = X3
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(esk1_2(k1_funct_2(esk8_0,esk9_0),k4_partfun1(esk8_0,esk9_0)),k1_funct_2(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_19,plain,
    ( k1_relat_1(esk2_4(X1,X2,X3,X4)) = X1
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_20,plain,
    ( v1_funct_1(esk2_4(X1,X2,X3,X4))
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_21,plain,
    ( v1_relat_1(esk2_4(X1,X2,X3,X4))
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,k4_partfun1(X2,X3))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X3) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_14])])).

cnf(c_0_23,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( r1_tarski(k2_relat_1(esk2_4(X1,X2,k1_funct_2(X1,X2),X3)),X2)
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_16])).

cnf(c_0_25,negated_conjecture,
    ( esk2_4(esk8_0,esk9_0,k1_funct_2(esk8_0,esk9_0),esk1_2(k1_funct_2(esk8_0,esk9_0),k4_partfun1(esk8_0,esk9_0))) = esk1_2(k1_funct_2(esk8_0,esk9_0),k4_partfun1(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_26,plain,
    ( k1_relat_1(esk2_4(X1,X2,k1_funct_2(X1,X2),X3)) = X1
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( v1_funct_1(esk2_4(X1,X2,k1_funct_2(X1,X2),X3))
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( v1_relat_1(esk2_4(X1,X2,k1_funct_2(X1,X2),X3))
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,k4_partfun1(k1_relat_1(X1),X2))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk1_2(k1_funct_2(esk8_0,esk9_0),k4_partfun1(esk8_0,esk9_0))),esk9_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_18]),c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( k1_relat_1(esk1_2(k1_funct_2(esk8_0,esk9_0),k4_partfun1(esk8_0,esk9_0))) = esk8_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_18]),c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( v1_funct_1(esk1_2(k1_funct_2(esk8_0,esk9_0),k4_partfun1(esk8_0,esk9_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_18]),c_0_25])).

cnf(c_0_33,negated_conjecture,
    ( v1_relat_1(esk1_2(k1_funct_2(esk8_0,esk9_0),k4_partfun1(esk8_0,esk9_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_18]),c_0_25])).

cnf(c_0_34,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk1_2(k1_funct_2(esk8_0,esk9_0),k4_partfun1(esk8_0,esk9_0)),k4_partfun1(esk8_0,esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31]),c_0_32]),c_0_33])])).

cnf(c_0_36,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_12]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.32  % Computer   : n003.cluster.edu
% 0.14/0.32  % Model      : x86_64 x86_64
% 0.14/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.32  % Memory     : 8042.1875MB
% 0.14/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.32  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 20:48:42 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.33  # Version: 2.5pre002
% 0.14/0.33  # No SInE strategy applied
% 0.14/0.33  # Trying AutoSched0 for 299 seconds
% 0.19/0.36  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S080I
% 0.19/0.36  # and selection function SelectCQIArNXTEqFirst.
% 0.19/0.36  #
% 0.19/0.36  # Preprocessing time       : 0.028 s
% 0.19/0.36  # Presaturation interreduction done
% 0.19/0.36  
% 0.19/0.36  # Proof found!
% 0.19/0.36  # SZS status Theorem
% 0.19/0.36  # SZS output start CNFRefutation
% 0.19/0.36  fof(t141_funct_2, conjecture, ![X1, X2]:r1_tarski(k1_funct_2(X1,X2),k4_partfun1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t141_funct_2)).
% 0.19/0.36  fof(d2_funct_2, axiom, ![X1, X2, X3]:(X3=k1_funct_2(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:((((v1_relat_1(X5)&v1_funct_1(X5))&X4=X5)&k1_relat_1(X5)=X1)&r1_tarski(k2_relat_1(X5),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_funct_2)).
% 0.19/0.36  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.36  fof(d5_partfun1, axiom, ![X1, X2, X3]:(X3=k4_partfun1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:((((v1_relat_1(X5)&v1_funct_1(X5))&X4=X5)&r1_tarski(k1_relat_1(X5),X1))&r1_tarski(k2_relat_1(X5),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_partfun1)).
% 0.19/0.36  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.36  fof(c_0_5, negated_conjecture, ~(![X1, X2]:r1_tarski(k1_funct_2(X1,X2),k4_partfun1(X1,X2))), inference(assume_negation,[status(cth)],[t141_funct_2])).
% 0.19/0.36  fof(c_0_6, plain, ![X14, X15, X16, X17, X19, X20, X21, X22, X23, X25]:(((((((v1_relat_1(esk2_4(X14,X15,X16,X17))|~r2_hidden(X17,X16)|X16!=k1_funct_2(X14,X15))&(v1_funct_1(esk2_4(X14,X15,X16,X17))|~r2_hidden(X17,X16)|X16!=k1_funct_2(X14,X15)))&(X17=esk2_4(X14,X15,X16,X17)|~r2_hidden(X17,X16)|X16!=k1_funct_2(X14,X15)))&(k1_relat_1(esk2_4(X14,X15,X16,X17))=X14|~r2_hidden(X17,X16)|X16!=k1_funct_2(X14,X15)))&(r1_tarski(k2_relat_1(esk2_4(X14,X15,X16,X17)),X15)|~r2_hidden(X17,X16)|X16!=k1_funct_2(X14,X15)))&(~v1_relat_1(X20)|~v1_funct_1(X20)|X19!=X20|k1_relat_1(X20)!=X14|~r1_tarski(k2_relat_1(X20),X15)|r2_hidden(X19,X16)|X16!=k1_funct_2(X14,X15)))&((~r2_hidden(esk3_3(X21,X22,X23),X23)|(~v1_relat_1(X25)|~v1_funct_1(X25)|esk3_3(X21,X22,X23)!=X25|k1_relat_1(X25)!=X21|~r1_tarski(k2_relat_1(X25),X22))|X23=k1_funct_2(X21,X22))&(((((v1_relat_1(esk4_3(X21,X22,X23))|r2_hidden(esk3_3(X21,X22,X23),X23)|X23=k1_funct_2(X21,X22))&(v1_funct_1(esk4_3(X21,X22,X23))|r2_hidden(esk3_3(X21,X22,X23),X23)|X23=k1_funct_2(X21,X22)))&(esk3_3(X21,X22,X23)=esk4_3(X21,X22,X23)|r2_hidden(esk3_3(X21,X22,X23),X23)|X23=k1_funct_2(X21,X22)))&(k1_relat_1(esk4_3(X21,X22,X23))=X21|r2_hidden(esk3_3(X21,X22,X23),X23)|X23=k1_funct_2(X21,X22)))&(r1_tarski(k2_relat_1(esk4_3(X21,X22,X23)),X22)|r2_hidden(esk3_3(X21,X22,X23),X23)|X23=k1_funct_2(X21,X22))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_funct_2])])])])])])).
% 0.19/0.36  fof(c_0_7, negated_conjecture, ~r1_tarski(k1_funct_2(esk8_0,esk9_0),k4_partfun1(esk8_0,esk9_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).
% 0.19/0.36  fof(c_0_8, plain, ![X6, X7, X8, X9, X10]:((~r1_tarski(X6,X7)|(~r2_hidden(X8,X6)|r2_hidden(X8,X7)))&((r2_hidden(esk1_2(X9,X10),X9)|r1_tarski(X9,X10))&(~r2_hidden(esk1_2(X9,X10),X10)|r1_tarski(X9,X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.36  fof(c_0_9, plain, ![X27, X28, X29, X30, X32, X33, X34, X35, X36, X38]:(((((((v1_relat_1(esk5_4(X27,X28,X29,X30))|~r2_hidden(X30,X29)|X29!=k4_partfun1(X27,X28))&(v1_funct_1(esk5_4(X27,X28,X29,X30))|~r2_hidden(X30,X29)|X29!=k4_partfun1(X27,X28)))&(X30=esk5_4(X27,X28,X29,X30)|~r2_hidden(X30,X29)|X29!=k4_partfun1(X27,X28)))&(r1_tarski(k1_relat_1(esk5_4(X27,X28,X29,X30)),X27)|~r2_hidden(X30,X29)|X29!=k4_partfun1(X27,X28)))&(r1_tarski(k2_relat_1(esk5_4(X27,X28,X29,X30)),X28)|~r2_hidden(X30,X29)|X29!=k4_partfun1(X27,X28)))&(~v1_relat_1(X33)|~v1_funct_1(X33)|X32!=X33|~r1_tarski(k1_relat_1(X33),X27)|~r1_tarski(k2_relat_1(X33),X28)|r2_hidden(X32,X29)|X29!=k4_partfun1(X27,X28)))&((~r2_hidden(esk6_3(X34,X35,X36),X36)|(~v1_relat_1(X38)|~v1_funct_1(X38)|esk6_3(X34,X35,X36)!=X38|~r1_tarski(k1_relat_1(X38),X34)|~r1_tarski(k2_relat_1(X38),X35))|X36=k4_partfun1(X34,X35))&(((((v1_relat_1(esk7_3(X34,X35,X36))|r2_hidden(esk6_3(X34,X35,X36),X36)|X36=k4_partfun1(X34,X35))&(v1_funct_1(esk7_3(X34,X35,X36))|r2_hidden(esk6_3(X34,X35,X36),X36)|X36=k4_partfun1(X34,X35)))&(esk6_3(X34,X35,X36)=esk7_3(X34,X35,X36)|r2_hidden(esk6_3(X34,X35,X36),X36)|X36=k4_partfun1(X34,X35)))&(r1_tarski(k1_relat_1(esk7_3(X34,X35,X36)),X34)|r2_hidden(esk6_3(X34,X35,X36),X36)|X36=k4_partfun1(X34,X35)))&(r1_tarski(k2_relat_1(esk7_3(X34,X35,X36)),X35)|r2_hidden(esk6_3(X34,X35,X36),X36)|X36=k4_partfun1(X34,X35))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_partfun1])])])])])])).
% 0.19/0.36  fof(c_0_10, plain, ![X12, X13]:(((r1_tarski(X12,X13)|X12!=X13)&(r1_tarski(X13,X12)|X12!=X13))&(~r1_tarski(X12,X13)|~r1_tarski(X13,X12)|X12=X13)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.36  cnf(c_0_11, plain, (X1=esk2_4(X2,X3,X4,X1)|~r2_hidden(X1,X4)|X4!=k1_funct_2(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.36  cnf(c_0_12, negated_conjecture, (~r1_tarski(k1_funct_2(esk8_0,esk9_0),k4_partfun1(esk8_0,esk9_0))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.36  cnf(c_0_13, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.36  cnf(c_0_14, plain, (r2_hidden(X2,X5)|~v1_relat_1(X1)|~v1_funct_1(X1)|X2!=X1|~r1_tarski(k1_relat_1(X1),X3)|~r1_tarski(k2_relat_1(X1),X4)|X5!=k4_partfun1(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.36  cnf(c_0_15, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.36  cnf(c_0_16, plain, (r1_tarski(k2_relat_1(esk2_4(X1,X2,X3,X4)),X2)|~r2_hidden(X4,X3)|X3!=k1_funct_2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.36  cnf(c_0_17, plain, (esk2_4(X1,X2,k1_funct_2(X1,X2),X3)=X3|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_11])).
% 0.19/0.36  cnf(c_0_18, negated_conjecture, (r2_hidden(esk1_2(k1_funct_2(esk8_0,esk9_0),k4_partfun1(esk8_0,esk9_0)),k1_funct_2(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.19/0.36  cnf(c_0_19, plain, (k1_relat_1(esk2_4(X1,X2,X3,X4))=X1|~r2_hidden(X4,X3)|X3!=k1_funct_2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.36  cnf(c_0_20, plain, (v1_funct_1(esk2_4(X1,X2,X3,X4))|~r2_hidden(X4,X3)|X3!=k1_funct_2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.36  cnf(c_0_21, plain, (v1_relat_1(esk2_4(X1,X2,X3,X4))|~r2_hidden(X4,X3)|X3!=k1_funct_2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.36  cnf(c_0_22, plain, (r2_hidden(X1,k4_partfun1(X2,X3))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X3)), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_14])])).
% 0.19/0.36  cnf(c_0_23, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_15])).
% 0.19/0.36  cnf(c_0_24, plain, (r1_tarski(k2_relat_1(esk2_4(X1,X2,k1_funct_2(X1,X2),X3)),X2)|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_16])).
% 0.19/0.36  cnf(c_0_25, negated_conjecture, (esk2_4(esk8_0,esk9_0,k1_funct_2(esk8_0,esk9_0),esk1_2(k1_funct_2(esk8_0,esk9_0),k4_partfun1(esk8_0,esk9_0)))=esk1_2(k1_funct_2(esk8_0,esk9_0),k4_partfun1(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.19/0.36  cnf(c_0_26, plain, (k1_relat_1(esk2_4(X1,X2,k1_funct_2(X1,X2),X3))=X1|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_19])).
% 0.19/0.36  cnf(c_0_27, plain, (v1_funct_1(esk2_4(X1,X2,k1_funct_2(X1,X2),X3))|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_20])).
% 0.19/0.36  cnf(c_0_28, plain, (v1_relat_1(esk2_4(X1,X2,k1_funct_2(X1,X2),X3))|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_21])).
% 0.19/0.36  cnf(c_0_29, plain, (r2_hidden(X1,k4_partfun1(k1_relat_1(X1),X2))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.19/0.36  cnf(c_0_30, negated_conjecture, (r1_tarski(k2_relat_1(esk1_2(k1_funct_2(esk8_0,esk9_0),k4_partfun1(esk8_0,esk9_0))),esk9_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_18]), c_0_25])).
% 0.19/0.36  cnf(c_0_31, negated_conjecture, (k1_relat_1(esk1_2(k1_funct_2(esk8_0,esk9_0),k4_partfun1(esk8_0,esk9_0)))=esk8_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_18]), c_0_25])).
% 0.19/0.36  cnf(c_0_32, negated_conjecture, (v1_funct_1(esk1_2(k1_funct_2(esk8_0,esk9_0),k4_partfun1(esk8_0,esk9_0)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_18]), c_0_25])).
% 0.19/0.36  cnf(c_0_33, negated_conjecture, (v1_relat_1(esk1_2(k1_funct_2(esk8_0,esk9_0),k4_partfun1(esk8_0,esk9_0)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_18]), c_0_25])).
% 0.19/0.36  cnf(c_0_34, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.36  cnf(c_0_35, negated_conjecture, (r2_hidden(esk1_2(k1_funct_2(esk8_0,esk9_0),k4_partfun1(esk8_0,esk9_0)),k4_partfun1(esk8_0,esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31]), c_0_32]), c_0_33])])).
% 0.19/0.36  cnf(c_0_36, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_12]), ['proof']).
% 0.19/0.36  # SZS output end CNFRefutation
% 0.19/0.36  # Proof object total steps             : 37
% 0.19/0.36  # Proof object clause steps            : 26
% 0.19/0.36  # Proof object formula steps           : 11
% 0.19/0.36  # Proof object conjectures             : 12
% 0.19/0.36  # Proof object clause conjectures      : 9
% 0.19/0.36  # Proof object formula conjectures     : 3
% 0.19/0.36  # Proof object initial clauses used    : 10
% 0.19/0.36  # Proof object initial formulas used   : 5
% 0.19/0.36  # Proof object generating inferences   : 9
% 0.19/0.36  # Proof object simplifying inferences  : 17
% 0.19/0.36  # Training examples: 0 positive, 0 negative
% 0.19/0.36  # Parsed axioms                        : 5
% 0.19/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.36  # Initial clauses                      : 31
% 0.19/0.36  # Removed in clause preprocessing      : 0
% 0.19/0.36  # Initial clauses in saturation        : 31
% 0.19/0.36  # Processed clauses                    : 79
% 0.19/0.36  # ...of these trivial                  : 0
% 0.19/0.36  # ...subsumed                          : 1
% 0.19/0.36  # ...remaining for further processing  : 78
% 0.19/0.36  # Other redundant clauses eliminated   : 19
% 0.19/0.36  # Clauses deleted for lack of memory   : 0
% 0.19/0.36  # Backward-subsumed                    : 0
% 0.19/0.36  # Backward-rewritten                   : 0
% 0.19/0.36  # Generated clauses                    : 58
% 0.19/0.36  # ...of the previous two non-trivial   : 54
% 0.19/0.36  # Contextual simplify-reflections      : 0
% 0.19/0.36  # Paramodulations                      : 42
% 0.19/0.36  # Factorizations                       : 0
% 0.19/0.36  # Equation resolutions                 : 19
% 0.19/0.36  # Propositional unsat checks           : 0
% 0.19/0.36  #    Propositional check models        : 0
% 0.19/0.36  #    Propositional check unsatisfiable : 0
% 0.19/0.36  #    Propositional clauses             : 0
% 0.19/0.36  #    Propositional clauses after purity: 0
% 0.19/0.36  #    Propositional unsat core size     : 0
% 0.19/0.36  #    Propositional preprocessing time  : 0.000
% 0.19/0.36  #    Propositional encoding time       : 0.000
% 0.19/0.36  #    Propositional solver time         : 0.000
% 0.19/0.36  #    Success case prop preproc time    : 0.000
% 0.19/0.36  #    Success case prop encoding time   : 0.000
% 0.19/0.36  #    Success case prop solver time     : 0.000
% 0.19/0.36  # Current number of processed clauses  : 32
% 0.19/0.36  #    Positive orientable unit clauses  : 10
% 0.19/0.36  #    Positive unorientable unit clauses: 0
% 0.19/0.36  #    Negative unit clauses             : 1
% 0.19/0.36  #    Non-unit-clauses                  : 21
% 0.19/0.36  # Current number of unprocessed clauses: 31
% 0.19/0.36  # ...number of literals in the above   : 81
% 0.19/0.36  # Current number of archived formulas  : 0
% 0.19/0.36  # Current number of archived clauses   : 30
% 0.19/0.36  # Clause-clause subsumption calls (NU) : 190
% 0.19/0.36  # Rec. Clause-clause subsumption calls : 100
% 0.19/0.36  # Non-unit clause-clause subsumptions  : 1
% 0.19/0.36  # Unit Clause-clause subsumption calls : 0
% 0.19/0.36  # Rewrite failures with RHS unbound    : 0
% 0.19/0.36  # BW rewrite match attempts            : 2
% 0.19/0.36  # BW rewrite match successes           : 0
% 0.19/0.36  # Condensation attempts                : 0
% 0.19/0.36  # Condensation successes               : 0
% 0.19/0.36  # Termbank termtop insertions          : 3538
% 0.19/0.36  
% 0.19/0.36  # -------------------------------------------------
% 0.19/0.36  # User time                : 0.031 s
% 0.19/0.36  # System time              : 0.004 s
% 0.19/0.36  # Total time               : 0.035 s
% 0.19/0.36  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
