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
% DateTime   : Thu Dec  3 10:52:12 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 127 expanded)
%              Number of clauses        :   29 (  59 expanded)
%              Number of leaves         :    8 (  31 expanded)
%              Depth                    :   10
%              Number of atoms          :  112 ( 334 expanded)
%              Number of equality atoms :   32 ( 104 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t204_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> r2_hidden(X2,k11_relat_1(X3,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(t205_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X1,k1_relat_1(X2))
      <=> k11_relat_1(X2,X1) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

fof(t1_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k5_xboole_0(X2,X3))
    <=> ~ ( r2_hidden(X1,X2)
        <=> r2_hidden(X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(c_0_8,plain,(
    ! [X14] : k4_xboole_0(X14,k1_xboole_0) = X14 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_9,plain,(
    ! [X12,X13] : k4_xboole_0(X12,X13) = k5_xboole_0(X12,k3_xboole_0(X12,X13)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_10,plain,(
    ! [X26,X27,X28] :
      ( ( ~ r2_hidden(k4_tarski(X26,X27),X28)
        | r2_hidden(X27,k11_relat_1(X28,X26))
        | ~ v1_relat_1(X28) )
      & ( ~ r2_hidden(X27,k11_relat_1(X28,X26))
        | r2_hidden(k4_tarski(X26,X27),X28)
        | ~ v1_relat_1(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t204_relat_1])])])).

fof(c_0_11,plain,(
    ! [X10] :
      ( X10 = k1_xboole_0
      | r2_hidden(esk1_1(X10),X10) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( r2_hidden(X1,k1_relat_1(X2))
        <=> k11_relat_1(X2,X1) != k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t205_relat_1])).

fof(c_0_13,plain,(
    ! [X7,X8,X9] :
      ( ( ~ r2_hidden(X7,X8)
        | ~ r2_hidden(X7,X9)
        | ~ r2_hidden(X7,k5_xboole_0(X8,X9)) )
      & ( r2_hidden(X7,X8)
        | r2_hidden(X7,X9)
        | ~ r2_hidden(X7,k5_xboole_0(X8,X9)) )
      & ( ~ r2_hidden(X7,X8)
        | r2_hidden(X7,X9)
        | r2_hidden(X7,k5_xboole_0(X8,X9)) )
      & ( ~ r2_hidden(X7,X9)
        | r2_hidden(X7,X8)
        | r2_hidden(X7,k5_xboole_0(X8,X9)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).

cnf(c_0_14,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_16,plain,(
    ! [X15,X16,X17,X19,X20,X21,X22,X24] :
      ( ( ~ r2_hidden(X17,X16)
        | r2_hidden(k4_tarski(X17,esk2_3(X15,X16,X17)),X15)
        | X16 != k1_relat_1(X15) )
      & ( ~ r2_hidden(k4_tarski(X19,X20),X15)
        | r2_hidden(X19,X16)
        | X16 != k1_relat_1(X15) )
      & ( ~ r2_hidden(esk3_2(X21,X22),X22)
        | ~ r2_hidden(k4_tarski(esk3_2(X21,X22),X24),X21)
        | X22 = k1_relat_1(X21) )
      & ( r2_hidden(esk3_2(X21,X22),X22)
        | r2_hidden(k4_tarski(esk3_2(X21,X22),esk4_2(X21,X22)),X21)
        | X22 = k1_relat_1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

cnf(c_0_17,plain,
    ( r2_hidden(k4_tarski(X3,X1),X2)
    | ~ r2_hidden(X1,k11_relat_1(X2,X3))
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_19,negated_conjecture,
    ( v1_relat_1(esk6_0)
    & ( ~ r2_hidden(esk5_0,k1_relat_1(esk6_0))
      | k11_relat_1(esk6_0,esk5_0) = k1_xboole_0 )
    & ( r2_hidden(esk5_0,k1_relat_1(esk6_0))
      | k11_relat_1(esk6_0,esk5_0) != k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

fof(c_0_20,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_21,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( k11_relat_1(X1,X2) = k1_xboole_0
    | r2_hidden(k4_tarski(X2,esk1_1(k11_relat_1(X1,X2))),X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,k1_xboole_0))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2) ),
    inference(er,[status(thm)],[c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( k11_relat_1(esk6_0,X1) = k1_xboole_0
    | r2_hidden(k4_tarski(X1,esk1_1(k11_relat_1(esk6_0,X1))),esk6_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,k5_xboole_0(X3,X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_31,plain,
    ( k5_xboole_0(X1,k3_xboole_0(k1_xboole_0,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_22,c_0_26])).

cnf(c_0_32,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(k1_xboole_0,X2))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_26])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk5_0,k1_relat_1(esk6_0))
    | k11_relat_1(esk6_0,esk5_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_34,negated_conjecture,
    ( k11_relat_1(esk6_0,X1) = k1_xboole_0
    | r2_hidden(X1,k1_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_35,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(k1_xboole_0,X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])).

cnf(c_0_36,negated_conjecture,
    ( k11_relat_1(esk6_0,esk5_0) = k1_xboole_0
    | ~ r2_hidden(esk5_0,k1_relat_1(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk5_0,k1_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_38,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_35,c_0_18])).

cnf(c_0_39,plain,
    ( r2_hidden(k4_tarski(X1,esk2_3(X3,X2,X1)),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_40,plain,
    ( r2_hidden(X2,k11_relat_1(X3,X1))
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_41,negated_conjecture,
    ( k11_relat_1(esk6_0,esk5_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_37])])).

cnf(c_0_42,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_35,c_0_38])).

cnf(c_0_43,plain,
    ( r2_hidden(k4_tarski(X1,esk2_3(X2,k1_relat_1(X2),X1)),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk5_0,X1),esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_25])]),c_0_42])).

cnf(c_0_45,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_37]),c_0_44]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.32  % Computer   : n013.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 16:37:24 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  # Version: 2.5pre002
% 0.12/0.32  # No SInE strategy applied
% 0.12/0.32  # Trying AutoSched0 for 299 seconds
% 0.18/0.36  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S03FN
% 0.18/0.36  # and selection function PSelectLComplex.
% 0.18/0.36  #
% 0.18/0.36  # Preprocessing time       : 0.027 s
% 0.18/0.36  # Presaturation interreduction done
% 0.18/0.36  
% 0.18/0.36  # Proof found!
% 0.18/0.36  # SZS status Theorem
% 0.18/0.36  # SZS output start CNFRefutation
% 0.18/0.36  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 0.18/0.36  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.18/0.36  fof(t204_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)<=>r2_hidden(X2,k11_relat_1(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t204_relat_1)).
% 0.18/0.36  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.18/0.36  fof(t205_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(r2_hidden(X1,k1_relat_1(X2))<=>k11_relat_1(X2,X1)!=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 0.18/0.36  fof(t1_xboole_0, axiom, ![X1, X2, X3]:(r2_hidden(X1,k5_xboole_0(X2,X3))<=>~((r2_hidden(X1,X2)<=>r2_hidden(X1,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 0.18/0.36  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 0.18/0.36  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.18/0.36  fof(c_0_8, plain, ![X14]:k4_xboole_0(X14,k1_xboole_0)=X14, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.18/0.36  fof(c_0_9, plain, ![X12, X13]:k4_xboole_0(X12,X13)=k5_xboole_0(X12,k3_xboole_0(X12,X13)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.18/0.36  fof(c_0_10, plain, ![X26, X27, X28]:((~r2_hidden(k4_tarski(X26,X27),X28)|r2_hidden(X27,k11_relat_1(X28,X26))|~v1_relat_1(X28))&(~r2_hidden(X27,k11_relat_1(X28,X26))|r2_hidden(k4_tarski(X26,X27),X28)|~v1_relat_1(X28))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t204_relat_1])])])).
% 0.18/0.36  fof(c_0_11, plain, ![X10]:(X10=k1_xboole_0|r2_hidden(esk1_1(X10),X10)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.18/0.36  fof(c_0_12, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(r2_hidden(X1,k1_relat_1(X2))<=>k11_relat_1(X2,X1)!=k1_xboole_0))), inference(assume_negation,[status(cth)],[t205_relat_1])).
% 0.18/0.36  fof(c_0_13, plain, ![X7, X8, X9]:(((~r2_hidden(X7,X8)|~r2_hidden(X7,X9)|~r2_hidden(X7,k5_xboole_0(X8,X9)))&(r2_hidden(X7,X8)|r2_hidden(X7,X9)|~r2_hidden(X7,k5_xboole_0(X8,X9))))&((~r2_hidden(X7,X8)|r2_hidden(X7,X9)|r2_hidden(X7,k5_xboole_0(X8,X9)))&(~r2_hidden(X7,X9)|r2_hidden(X7,X8)|r2_hidden(X7,k5_xboole_0(X8,X9))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).
% 0.18/0.36  cnf(c_0_14, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.18/0.36  cnf(c_0_15, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.18/0.36  fof(c_0_16, plain, ![X15, X16, X17, X19, X20, X21, X22, X24]:(((~r2_hidden(X17,X16)|r2_hidden(k4_tarski(X17,esk2_3(X15,X16,X17)),X15)|X16!=k1_relat_1(X15))&(~r2_hidden(k4_tarski(X19,X20),X15)|r2_hidden(X19,X16)|X16!=k1_relat_1(X15)))&((~r2_hidden(esk3_2(X21,X22),X22)|~r2_hidden(k4_tarski(esk3_2(X21,X22),X24),X21)|X22=k1_relat_1(X21))&(r2_hidden(esk3_2(X21,X22),X22)|r2_hidden(k4_tarski(esk3_2(X21,X22),esk4_2(X21,X22)),X21)|X22=k1_relat_1(X21)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 0.18/0.36  cnf(c_0_17, plain, (r2_hidden(k4_tarski(X3,X1),X2)|~r2_hidden(X1,k11_relat_1(X2,X3))|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.36  cnf(c_0_18, plain, (X1=k1_xboole_0|r2_hidden(esk1_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.36  fof(c_0_19, negated_conjecture, (v1_relat_1(esk6_0)&((~r2_hidden(esk5_0,k1_relat_1(esk6_0))|k11_relat_1(esk6_0,esk5_0)=k1_xboole_0)&(r2_hidden(esk5_0,k1_relat_1(esk6_0))|k11_relat_1(esk6_0,esk5_0)!=k1_xboole_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 0.18/0.36  fof(c_0_20, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.18/0.36  cnf(c_0_21, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r2_hidden(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.36  cnf(c_0_22, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 0.18/0.36  cnf(c_0_23, plain, (r2_hidden(X1,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.36  cnf(c_0_24, plain, (k11_relat_1(X1,X2)=k1_xboole_0|r2_hidden(k4_tarski(X2,esk1_1(k11_relat_1(X1,X2))),X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.18/0.36  cnf(c_0_25, negated_conjecture, (v1_relat_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.18/0.36  cnf(c_0_26, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.36  cnf(c_0_27, plain, (~r2_hidden(X1,k3_xboole_0(X2,k1_xboole_0))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.18/0.36  cnf(c_0_28, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)), inference(er,[status(thm)],[c_0_23])).
% 0.18/0.36  cnf(c_0_29, negated_conjecture, (k11_relat_1(esk6_0,X1)=k1_xboole_0|r2_hidden(k4_tarski(X1,esk1_1(k11_relat_1(esk6_0,X1))),esk6_0)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.18/0.36  cnf(c_0_30, plain, (r2_hidden(X1,X3)|r2_hidden(X1,k5_xboole_0(X3,X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.36  cnf(c_0_31, plain, (k5_xboole_0(X1,k3_xboole_0(k1_xboole_0,X1))=X1), inference(spm,[status(thm)],[c_0_22, c_0_26])).
% 0.18/0.36  cnf(c_0_32, plain, (~r2_hidden(X1,k3_xboole_0(k1_xboole_0,X2))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_27, c_0_26])).
% 0.18/0.36  cnf(c_0_33, negated_conjecture, (r2_hidden(esk5_0,k1_relat_1(esk6_0))|k11_relat_1(esk6_0,esk5_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.18/0.36  cnf(c_0_34, negated_conjecture, (k11_relat_1(esk6_0,X1)=k1_xboole_0|r2_hidden(X1,k1_relat_1(esk6_0))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.18/0.36  cnf(c_0_35, plain, (~r2_hidden(X1,k3_xboole_0(k1_xboole_0,X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])).
% 0.18/0.36  cnf(c_0_36, negated_conjecture, (k11_relat_1(esk6_0,esk5_0)=k1_xboole_0|~r2_hidden(esk5_0,k1_relat_1(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.18/0.36  cnf(c_0_37, negated_conjecture, (r2_hidden(esk5_0,k1_relat_1(esk6_0))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.18/0.36  cnf(c_0_38, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_35, c_0_18])).
% 0.18/0.36  cnf(c_0_39, plain, (r2_hidden(k4_tarski(X1,esk2_3(X3,X2,X1)),X3)|~r2_hidden(X1,X2)|X2!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.36  cnf(c_0_40, plain, (r2_hidden(X2,k11_relat_1(X3,X1))|~r2_hidden(k4_tarski(X1,X2),X3)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.36  cnf(c_0_41, negated_conjecture, (k11_relat_1(esk6_0,esk5_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_37])])).
% 0.18/0.36  cnf(c_0_42, plain, (~r2_hidden(X1,k1_xboole_0)), inference(rw,[status(thm)],[c_0_35, c_0_38])).
% 0.18/0.36  cnf(c_0_43, plain, (r2_hidden(k4_tarski(X1,esk2_3(X2,k1_relat_1(X2),X1)),X2)|~r2_hidden(X1,k1_relat_1(X2))), inference(er,[status(thm)],[c_0_39])).
% 0.18/0.36  cnf(c_0_44, negated_conjecture, (~r2_hidden(k4_tarski(esk5_0,X1),esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_25])]), c_0_42])).
% 0.18/0.36  cnf(c_0_45, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_37]), c_0_44]), ['proof']).
% 0.18/0.36  # SZS output end CNFRefutation
% 0.18/0.36  # Proof object total steps             : 46
% 0.18/0.36  # Proof object clause steps            : 29
% 0.18/0.36  # Proof object formula steps           : 17
% 0.18/0.36  # Proof object conjectures             : 12
% 0.18/0.36  # Proof object clause conjectures      : 9
% 0.18/0.36  # Proof object formula conjectures     : 3
% 0.18/0.36  # Proof object initial clauses used    : 13
% 0.18/0.36  # Proof object initial formulas used   : 8
% 0.18/0.36  # Proof object generating inferences   : 11
% 0.18/0.36  # Proof object simplifying inferences  : 11
% 0.18/0.36  # Training examples: 0 positive, 0 negative
% 0.18/0.36  # Parsed axioms                        : 8
% 0.18/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.36  # Initial clauses                      : 17
% 0.18/0.36  # Removed in clause preprocessing      : 1
% 0.18/0.36  # Initial clauses in saturation        : 16
% 0.18/0.36  # Processed clauses                    : 101
% 0.18/0.36  # ...of these trivial                  : 2
% 0.18/0.36  # ...subsumed                          : 32
% 0.18/0.36  # ...remaining for further processing  : 66
% 0.18/0.36  # Other redundant clauses eliminated   : 2
% 0.18/0.36  # Clauses deleted for lack of memory   : 0
% 0.18/0.36  # Backward-subsumed                    : 0
% 0.18/0.36  # Backward-rewritten                   : 13
% 0.18/0.36  # Generated clauses                    : 157
% 0.18/0.36  # ...of the previous two non-trivial   : 141
% 0.18/0.36  # Contextual simplify-reflections      : 2
% 0.18/0.36  # Paramodulations                      : 151
% 0.18/0.36  # Factorizations                       : 4
% 0.18/0.36  # Equation resolutions                 : 2
% 0.18/0.36  # Propositional unsat checks           : 0
% 0.18/0.36  #    Propositional check models        : 0
% 0.18/0.36  #    Propositional check unsatisfiable : 0
% 0.18/0.36  #    Propositional clauses             : 0
% 0.18/0.36  #    Propositional clauses after purity: 0
% 0.18/0.36  #    Propositional unsat core size     : 0
% 0.18/0.36  #    Propositional preprocessing time  : 0.000
% 0.18/0.36  #    Propositional encoding time       : 0.000
% 0.18/0.36  #    Propositional solver time         : 0.000
% 0.18/0.36  #    Success case prop preproc time    : 0.000
% 0.18/0.36  #    Success case prop encoding time   : 0.000
% 0.18/0.36  #    Success case prop solver time     : 0.000
% 0.18/0.36  # Current number of processed clauses  : 35
% 0.18/0.36  #    Positive orientable unit clauses  : 8
% 0.18/0.36  #    Positive unorientable unit clauses: 1
% 0.18/0.36  #    Negative unit clauses             : 2
% 0.18/0.36  #    Non-unit-clauses                  : 24
% 0.18/0.36  # Current number of unprocessed clauses: 65
% 0.18/0.36  # ...number of literals in the above   : 204
% 0.18/0.36  # Current number of archived formulas  : 0
% 0.18/0.36  # Current number of archived clauses   : 30
% 0.18/0.36  # Clause-clause subsumption calls (NU) : 125
% 0.18/0.36  # Rec. Clause-clause subsumption calls : 100
% 0.18/0.36  # Non-unit clause-clause subsumptions  : 19
% 0.18/0.36  # Unit Clause-clause subsumption calls : 34
% 0.18/0.36  # Rewrite failures with RHS unbound    : 0
% 0.18/0.36  # BW rewrite match attempts            : 18
% 0.18/0.36  # BW rewrite match successes           : 13
% 0.18/0.36  # Condensation attempts                : 0
% 0.18/0.36  # Condensation successes               : 0
% 0.18/0.36  # Termbank termtop insertions          : 3363
% 0.18/0.36  
% 0.18/0.36  # -------------------------------------------------
% 0.18/0.36  # User time                : 0.026 s
% 0.18/0.36  # System time              : 0.009 s
% 0.18/0.36  # Total time               : 0.035 s
% 0.18/0.36  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
