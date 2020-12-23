%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:52:56 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 117 expanded)
%              Number of clauses        :   35 (  53 expanded)
%              Number of leaves         :    4 (  27 expanded)
%              Depth                    :    9
%              Number of atoms          :  153 ( 435 expanded)
%              Number of equality atoms :   72 ( 222 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t14_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( k1_relat_1(X2) = k1_tarski(X1)
       => k2_relat_1(X2) = k1_tarski(k1_funct_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

fof(d5_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( X2 = k2_relat_1(X1)
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                  & X3 = k1_funct_1(X1,X4) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

fof(c_0_4,plain,(
    ! [X5,X6,X7,X8,X9,X10] :
      ( ( ~ r2_hidden(X7,X6)
        | X7 = X5
        | X6 != k1_tarski(X5) )
      & ( X8 != X5
        | r2_hidden(X8,X6)
        | X6 != k1_tarski(X5) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | esk1_2(X9,X10) != X9
        | X10 = k1_tarski(X9) )
      & ( r2_hidden(esk1_2(X9,X10),X10)
        | esk1_2(X9,X10) = X9
        | X10 = k1_tarski(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_5,plain,(
    ! [X12] : k2_tarski(X12,X12) = k1_tarski(X12) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ( k1_relat_1(X2) = k1_tarski(X1)
         => k2_relat_1(X2) = k1_tarski(k1_funct_1(X2,X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t14_funct_1])).

fof(c_0_7,plain,(
    ! [X16,X17,X18,X20,X21,X22,X24] :
      ( ( r2_hidden(esk3_3(X16,X17,X18),k1_relat_1(X16))
        | ~ r2_hidden(X18,X17)
        | X17 != k2_relat_1(X16)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) )
      & ( X18 = k1_funct_1(X16,esk3_3(X16,X17,X18))
        | ~ r2_hidden(X18,X17)
        | X17 != k2_relat_1(X16)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) )
      & ( ~ r2_hidden(X21,k1_relat_1(X16))
        | X20 != k1_funct_1(X16,X21)
        | r2_hidden(X20,X17)
        | X17 != k2_relat_1(X16)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) )
      & ( ~ r2_hidden(esk4_2(X16,X22),X22)
        | ~ r2_hidden(X24,k1_relat_1(X16))
        | esk4_2(X16,X22) != k1_funct_1(X16,X24)
        | X22 = k2_relat_1(X16)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) )
      & ( r2_hidden(esk5_2(X16,X22),k1_relat_1(X16))
        | r2_hidden(esk4_2(X16,X22),X22)
        | X22 = k2_relat_1(X16)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) )
      & ( esk4_2(X16,X22) = k1_funct_1(X16,esk5_2(X16,X22))
        | r2_hidden(esk4_2(X16,X22),X22)
        | X22 = k2_relat_1(X16)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

cnf(c_0_8,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_9,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_10,negated_conjecture,
    ( v1_relat_1(esk7_0)
    & v1_funct_1(esk7_0)
    & k1_relat_1(esk7_0) = k1_tarski(esk6_0)
    & k2_relat_1(esk7_0) != k1_tarski(k1_funct_1(esk7_0,esk6_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

cnf(c_0_11,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),k1_relat_1(X1))
    | ~ r2_hidden(X3,X2)
    | X2 != k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( X1 = k1_funct_1(X2,esk3_3(X2,X3,X1))
    | ~ r2_hidden(X1,X3)
    | X3 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( X1 = X3
    | X2 != k2_tarski(X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( k1_relat_1(esk7_0) = k1_tarski(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( r2_hidden(esk3_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | esk1_2(X1,X2) = X1
    | X2 = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_19,plain,
    ( k1_funct_1(X1,esk3_3(X1,k2_relat_1(X1),X2)) = X2
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k2_tarski(X2,X2)) ),
    inference(er,[status(thm)],[c_0_13])).

cnf(c_0_21,negated_conjecture,
    ( k1_relat_1(esk7_0) = k2_tarski(esk6_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_14,c_0_9])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk3_3(esk7_0,k2_relat_1(esk7_0),X1),k1_relat_1(esk7_0))
    | ~ r2_hidden(X1,k2_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])])).

cnf(c_0_23,plain,
    ( X2 = k2_tarski(X1,X1)
    | esk1_2(X1,X2) = X1
    | r2_hidden(esk1_2(X1,X2),X2) ),
    inference(rw,[status(thm)],[c_0_18,c_0_9])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_25,negated_conjecture,
    ( k1_funct_1(esk7_0,esk3_3(esk7_0,k2_relat_1(esk7_0),X1)) = X1
    | ~ r2_hidden(X1,k2_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_16]),c_0_17])])).

cnf(c_0_26,negated_conjecture,
    ( X1 = esk6_0
    | ~ r2_hidden(X1,k1_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( esk1_2(X1,k2_relat_1(esk7_0)) = X1
    | k2_tarski(X1,X1) = k2_relat_1(esk7_0)
    | r2_hidden(esk3_3(esk7_0,k2_relat_1(esk7_0),esk1_2(X1,k2_relat_1(esk7_0))),k1_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_28,plain,
    ( r2_hidden(X3,X4)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | X4 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X2) ),
    inference(rw,[status(thm)],[c_0_24,c_0_9])).

cnf(c_0_30,negated_conjecture,
    ( k2_relat_1(esk7_0) != k1_tarski(k1_funct_1(esk7_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_31,negated_conjecture,
    ( k1_funct_1(esk7_0,esk3_3(esk7_0,k2_relat_1(esk7_0),esk1_2(X1,k2_relat_1(esk7_0)))) = esk1_2(X1,k2_relat_1(esk7_0))
    | esk1_2(X1,k2_relat_1(esk7_0)) = X1
    | k2_tarski(X1,X1) = k2_relat_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_23])).

cnf(c_0_32,negated_conjecture,
    ( esk3_3(esk7_0,k2_relat_1(esk7_0),esk1_2(X1,k2_relat_1(esk7_0))) = esk6_0
    | k2_tarski(X1,X1) = k2_relat_1(esk7_0)
    | esk1_2(X1,k2_relat_1(esk7_0)) = X1 ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_33,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_28])])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,k2_tarski(X1,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_29])])).

cnf(c_0_35,plain,
    ( X2 = k1_tarski(X1)
    | ~ r2_hidden(esk1_2(X1,X2),X2)
    | esk1_2(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_36,negated_conjecture,
    ( k2_relat_1(esk7_0) != k2_tarski(k1_funct_1(esk7_0,esk6_0),k1_funct_1(esk7_0,esk6_0)) ),
    inference(rw,[status(thm)],[c_0_30,c_0_9])).

cnf(c_0_37,negated_conjecture,
    ( esk1_2(X1,k2_relat_1(esk7_0)) = k1_funct_1(esk7_0,esk6_0)
    | k2_tarski(X1,X1) = k2_relat_1(esk7_0)
    | esk1_2(X1,k2_relat_1(esk7_0)) = X1 ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk7_0,X1),k2_relat_1(esk7_0))
    | ~ r2_hidden(X1,k1_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_16]),c_0_17])])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk6_0,k1_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_21])).

cnf(c_0_40,plain,
    ( X2 = k2_tarski(X1,X1)
    | esk1_2(X1,X2) != X1
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(rw,[status(thm)],[c_0_35,c_0_9])).

cnf(c_0_41,negated_conjecture,
    ( esk1_2(k1_funct_1(esk7_0,esk6_0),k2_relat_1(esk7_0)) = k1_funct_1(esk7_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk7_0,esk6_0),k2_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_43,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])]),c_0_36]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:55:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.51  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S053I
% 0.20/0.51  # and selection function HSelectMinInfpos.
% 0.20/0.51  #
% 0.20/0.51  # Preprocessing time       : 0.027 s
% 0.20/0.51  # Presaturation interreduction done
% 0.20/0.51  
% 0.20/0.51  # Proof found!
% 0.20/0.51  # SZS status Theorem
% 0.20/0.51  # SZS output start CNFRefutation
% 0.20/0.51  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 0.20/0.51  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.20/0.51  fof(t14_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(k1_relat_1(X2)=k1_tarski(X1)=>k2_relat_1(X2)=k1_tarski(k1_funct_1(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 0.20/0.51  fof(d5_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 0.20/0.51  fof(c_0_4, plain, ![X5, X6, X7, X8, X9, X10]:(((~r2_hidden(X7,X6)|X7=X5|X6!=k1_tarski(X5))&(X8!=X5|r2_hidden(X8,X6)|X6!=k1_tarski(X5)))&((~r2_hidden(esk1_2(X9,X10),X10)|esk1_2(X9,X10)!=X9|X10=k1_tarski(X9))&(r2_hidden(esk1_2(X9,X10),X10)|esk1_2(X9,X10)=X9|X10=k1_tarski(X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.20/0.51  fof(c_0_5, plain, ![X12]:k2_tarski(X12,X12)=k1_tarski(X12), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.20/0.51  fof(c_0_6, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(k1_relat_1(X2)=k1_tarski(X1)=>k2_relat_1(X2)=k1_tarski(k1_funct_1(X2,X1))))), inference(assume_negation,[status(cth)],[t14_funct_1])).
% 0.20/0.51  fof(c_0_7, plain, ![X16, X17, X18, X20, X21, X22, X24]:((((r2_hidden(esk3_3(X16,X17,X18),k1_relat_1(X16))|~r2_hidden(X18,X17)|X17!=k2_relat_1(X16)|(~v1_relat_1(X16)|~v1_funct_1(X16)))&(X18=k1_funct_1(X16,esk3_3(X16,X17,X18))|~r2_hidden(X18,X17)|X17!=k2_relat_1(X16)|(~v1_relat_1(X16)|~v1_funct_1(X16))))&(~r2_hidden(X21,k1_relat_1(X16))|X20!=k1_funct_1(X16,X21)|r2_hidden(X20,X17)|X17!=k2_relat_1(X16)|(~v1_relat_1(X16)|~v1_funct_1(X16))))&((~r2_hidden(esk4_2(X16,X22),X22)|(~r2_hidden(X24,k1_relat_1(X16))|esk4_2(X16,X22)!=k1_funct_1(X16,X24))|X22=k2_relat_1(X16)|(~v1_relat_1(X16)|~v1_funct_1(X16)))&((r2_hidden(esk5_2(X16,X22),k1_relat_1(X16))|r2_hidden(esk4_2(X16,X22),X22)|X22=k2_relat_1(X16)|(~v1_relat_1(X16)|~v1_funct_1(X16)))&(esk4_2(X16,X22)=k1_funct_1(X16,esk5_2(X16,X22))|r2_hidden(esk4_2(X16,X22),X22)|X22=k2_relat_1(X16)|(~v1_relat_1(X16)|~v1_funct_1(X16)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).
% 0.20/0.51  cnf(c_0_8, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.20/0.51  cnf(c_0_9, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.20/0.51  fof(c_0_10, negated_conjecture, ((v1_relat_1(esk7_0)&v1_funct_1(esk7_0))&(k1_relat_1(esk7_0)=k1_tarski(esk6_0)&k2_relat_1(esk7_0)!=k1_tarski(k1_funct_1(esk7_0,esk6_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).
% 0.20/0.51  cnf(c_0_11, plain, (r2_hidden(esk3_3(X1,X2,X3),k1_relat_1(X1))|~r2_hidden(X3,X2)|X2!=k2_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.51  cnf(c_0_12, plain, (X1=k1_funct_1(X2,esk3_3(X2,X3,X1))|~r2_hidden(X1,X3)|X3!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.51  cnf(c_0_13, plain, (X1=X3|X2!=k2_tarski(X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_8, c_0_9])).
% 0.20/0.51  cnf(c_0_14, negated_conjecture, (k1_relat_1(esk7_0)=k1_tarski(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.51  cnf(c_0_15, plain, (r2_hidden(esk3_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_11])).
% 0.20/0.51  cnf(c_0_16, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.51  cnf(c_0_17, negated_conjecture, (v1_relat_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.51  cnf(c_0_18, plain, (r2_hidden(esk1_2(X1,X2),X2)|esk1_2(X1,X2)=X1|X2=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.20/0.51  cnf(c_0_19, plain, (k1_funct_1(X1,esk3_3(X1,k2_relat_1(X1),X2))=X2|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_12])).
% 0.20/0.51  cnf(c_0_20, plain, (X1=X2|~r2_hidden(X1,k2_tarski(X2,X2))), inference(er,[status(thm)],[c_0_13])).
% 0.20/0.51  cnf(c_0_21, negated_conjecture, (k1_relat_1(esk7_0)=k2_tarski(esk6_0,esk6_0)), inference(rw,[status(thm)],[c_0_14, c_0_9])).
% 0.20/0.51  cnf(c_0_22, negated_conjecture, (r2_hidden(esk3_3(esk7_0,k2_relat_1(esk7_0),X1),k1_relat_1(esk7_0))|~r2_hidden(X1,k2_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17])])).
% 0.20/0.51  cnf(c_0_23, plain, (X2=k2_tarski(X1,X1)|esk1_2(X1,X2)=X1|r2_hidden(esk1_2(X1,X2),X2)), inference(rw,[status(thm)],[c_0_18, c_0_9])).
% 0.20/0.51  cnf(c_0_24, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.20/0.51  cnf(c_0_25, negated_conjecture, (k1_funct_1(esk7_0,esk3_3(esk7_0,k2_relat_1(esk7_0),X1))=X1|~r2_hidden(X1,k2_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_16]), c_0_17])])).
% 0.20/0.51  cnf(c_0_26, negated_conjecture, (X1=esk6_0|~r2_hidden(X1,k1_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.20/0.51  cnf(c_0_27, negated_conjecture, (esk1_2(X1,k2_relat_1(esk7_0))=X1|k2_tarski(X1,X1)=k2_relat_1(esk7_0)|r2_hidden(esk3_3(esk7_0,k2_relat_1(esk7_0),esk1_2(X1,k2_relat_1(esk7_0))),k1_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.20/0.51  cnf(c_0_28, plain, (r2_hidden(X3,X4)|~r2_hidden(X1,k1_relat_1(X2))|X3!=k1_funct_1(X2,X1)|X4!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.51  cnf(c_0_29, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X2,X2)), inference(rw,[status(thm)],[c_0_24, c_0_9])).
% 0.20/0.51  cnf(c_0_30, negated_conjecture, (k2_relat_1(esk7_0)!=k1_tarski(k1_funct_1(esk7_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.51  cnf(c_0_31, negated_conjecture, (k1_funct_1(esk7_0,esk3_3(esk7_0,k2_relat_1(esk7_0),esk1_2(X1,k2_relat_1(esk7_0))))=esk1_2(X1,k2_relat_1(esk7_0))|esk1_2(X1,k2_relat_1(esk7_0))=X1|k2_tarski(X1,X1)=k2_relat_1(esk7_0)), inference(spm,[status(thm)],[c_0_25, c_0_23])).
% 0.20/0.51  cnf(c_0_32, negated_conjecture, (esk3_3(esk7_0,k2_relat_1(esk7_0),esk1_2(X1,k2_relat_1(esk7_0)))=esk6_0|k2_tarski(X1,X1)=k2_relat_1(esk7_0)|esk1_2(X1,k2_relat_1(esk7_0))=X1), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.20/0.51  cnf(c_0_33, plain, (r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k1_relat_1(X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_28])])).
% 0.20/0.51  cnf(c_0_34, plain, (r2_hidden(X1,k2_tarski(X1,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_29])])).
% 0.20/0.51  cnf(c_0_35, plain, (X2=k1_tarski(X1)|~r2_hidden(esk1_2(X1,X2),X2)|esk1_2(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.20/0.51  cnf(c_0_36, negated_conjecture, (k2_relat_1(esk7_0)!=k2_tarski(k1_funct_1(esk7_0,esk6_0),k1_funct_1(esk7_0,esk6_0))), inference(rw,[status(thm)],[c_0_30, c_0_9])).
% 0.20/0.51  cnf(c_0_37, negated_conjecture, (esk1_2(X1,k2_relat_1(esk7_0))=k1_funct_1(esk7_0,esk6_0)|k2_tarski(X1,X1)=k2_relat_1(esk7_0)|esk1_2(X1,k2_relat_1(esk7_0))=X1), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.20/0.51  cnf(c_0_38, negated_conjecture, (r2_hidden(k1_funct_1(esk7_0,X1),k2_relat_1(esk7_0))|~r2_hidden(X1,k1_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_16]), c_0_17])])).
% 0.20/0.51  cnf(c_0_39, negated_conjecture, (r2_hidden(esk6_0,k1_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_34, c_0_21])).
% 0.20/0.51  cnf(c_0_40, plain, (X2=k2_tarski(X1,X1)|esk1_2(X1,X2)!=X1|~r2_hidden(esk1_2(X1,X2),X2)), inference(rw,[status(thm)],[c_0_35, c_0_9])).
% 0.20/0.51  cnf(c_0_41, negated_conjecture, (esk1_2(k1_funct_1(esk7_0,esk6_0),k2_relat_1(esk7_0))=k1_funct_1(esk7_0,esk6_0)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.20/0.51  cnf(c_0_42, negated_conjecture, (r2_hidden(k1_funct_1(esk7_0,esk6_0),k2_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.20/0.51  cnf(c_0_43, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42])]), c_0_36]), ['proof']).
% 0.20/0.51  # SZS output end CNFRefutation
% 0.20/0.51  # Proof object total steps             : 44
% 0.20/0.51  # Proof object clause steps            : 35
% 0.20/0.51  # Proof object formula steps           : 9
% 0.20/0.51  # Proof object conjectures             : 21
% 0.20/0.51  # Proof object clause conjectures      : 18
% 0.20/0.51  # Proof object formula conjectures     : 3
% 0.20/0.51  # Proof object initial clauses used    : 12
% 0.20/0.51  # Proof object initial formulas used   : 4
% 0.20/0.51  # Proof object generating inferences   : 12
% 0.20/0.51  # Proof object simplifying inferences  : 22
% 0.20/0.51  # Training examples: 0 positive, 0 negative
% 0.20/0.51  # Parsed axioms                        : 5
% 0.20/0.51  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.51  # Initial clauses                      : 16
% 0.20/0.51  # Removed in clause preprocessing      : 1
% 0.20/0.51  # Initial clauses in saturation        : 15
% 0.20/0.51  # Processed clauses                    : 525
% 0.20/0.51  # ...of these trivial                  : 0
% 0.20/0.51  # ...subsumed                          : 301
% 0.20/0.51  # ...remaining for further processing  : 224
% 0.20/0.51  # Other redundant clauses eliminated   : 247
% 0.20/0.51  # Clauses deleted for lack of memory   : 0
% 0.20/0.51  # Backward-subsumed                    : 12
% 0.20/0.51  # Backward-rewritten                   : 14
% 0.20/0.51  # Generated clauses                    : 4373
% 0.20/0.51  # ...of the previous two non-trivial   : 3736
% 0.20/0.51  # Contextual simplify-reflections      : 5
% 0.20/0.51  # Paramodulations                      : 3853
% 0.20/0.51  # Factorizations                       : 275
% 0.20/0.51  # Equation resolutions                 : 247
% 0.20/0.51  # Propositional unsat checks           : 0
% 0.20/0.51  #    Propositional check models        : 0
% 0.20/0.51  #    Propositional check unsatisfiable : 0
% 0.20/0.51  #    Propositional clauses             : 0
% 0.20/0.51  #    Propositional clauses after purity: 0
% 0.20/0.51  #    Propositional unsat core size     : 0
% 0.20/0.51  #    Propositional preprocessing time  : 0.000
% 0.20/0.51  #    Propositional encoding time       : 0.000
% 0.20/0.51  #    Propositional solver time         : 0.000
% 0.20/0.51  #    Success case prop preproc time    : 0.000
% 0.20/0.51  #    Success case prop encoding time   : 0.000
% 0.20/0.51  #    Success case prop solver time     : 0.000
% 0.20/0.51  # Current number of processed clauses  : 178
% 0.20/0.51  #    Positive orientable unit clauses  : 9
% 0.20/0.51  #    Positive unorientable unit clauses: 0
% 0.20/0.51  #    Negative unit clauses             : 1
% 0.20/0.51  #    Non-unit-clauses                  : 168
% 0.20/0.51  # Current number of unprocessed clauses: 3226
% 0.20/0.51  # ...number of literals in the above   : 23840
% 0.20/0.51  # Current number of archived formulas  : 0
% 0.20/0.51  # Current number of archived clauses   : 42
% 0.20/0.51  # Clause-clause subsumption calls (NU) : 4996
% 0.20/0.51  # Rec. Clause-clause subsumption calls : 1121
% 0.20/0.51  # Non-unit clause-clause subsumptions  : 243
% 0.20/0.51  # Unit Clause-clause subsumption calls : 16
% 0.20/0.51  # Rewrite failures with RHS unbound    : 0
% 0.20/0.51  # BW rewrite match attempts            : 15
% 0.20/0.51  # BW rewrite match successes           : 4
% 0.20/0.51  # Condensation attempts                : 0
% 0.20/0.51  # Condensation successes               : 0
% 0.20/0.51  # Termbank termtop insertions          : 117073
% 0.20/0.51  
% 0.20/0.51  # -------------------------------------------------
% 0.20/0.51  # User time                : 0.160 s
% 0.20/0.51  # System time              : 0.008 s
% 0.20/0.51  # Total time               : 0.168 s
% 0.20/0.51  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
