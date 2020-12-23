%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:52:18 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   39 ( 127 expanded)
%              Number of clauses        :   26 (  61 expanded)
%              Number of leaves         :    6 (  29 expanded)
%              Depth                    :   10
%              Number of atoms          :  115 ( 470 expanded)
%              Number of equality atoms :   31 ( 133 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(t205_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X1,k1_relat_1(X2))
      <=> k11_relat_1(X2,X1) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

fof(t204_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> r2_hidden(X2,k11_relat_1(X3,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(c_0_6,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11,X12] :
      ( ( r2_hidden(X8,X5)
        | ~ r2_hidden(X8,X7)
        | X7 != k4_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X8,X6)
        | ~ r2_hidden(X8,X7)
        | X7 != k4_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X5)
        | r2_hidden(X9,X6)
        | r2_hidden(X9,X7)
        | X7 != k4_xboole_0(X5,X6) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X11)
        | X12 = k4_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k4_xboole_0(X10,X11) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X11)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k4_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

cnf(c_0_7,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_8,plain,(
    ! [X16] : k4_xboole_0(X16,k1_xboole_0) = X16 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_9,plain,(
    ! [X17,X18,X19,X21,X22,X23,X24,X26] :
      ( ( ~ r2_hidden(X19,X18)
        | r2_hidden(k4_tarski(X19,esk3_3(X17,X18,X19)),X17)
        | X18 != k1_relat_1(X17) )
      & ( ~ r2_hidden(k4_tarski(X21,X22),X17)
        | r2_hidden(X21,X18)
        | X18 != k1_relat_1(X17) )
      & ( ~ r2_hidden(esk4_2(X23,X24),X24)
        | ~ r2_hidden(k4_tarski(esk4_2(X23,X24),X26),X23)
        | X24 = k1_relat_1(X23) )
      & ( r2_hidden(esk4_2(X23,X24),X24)
        | r2_hidden(k4_tarski(esk4_2(X23,X24),esk5_2(X23,X24)),X23)
        | X24 = k1_relat_1(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

cnf(c_0_10,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( r2_hidden(k4_tarski(X1,esk3_3(X3,X2,X1)),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( r2_hidden(X1,k1_relat_1(X2))
        <=> k11_relat_1(X2,X1) != k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t205_relat_1])).

cnf(c_0_14,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_15,plain,
    ( r2_hidden(k4_tarski(X1,esk3_3(X2,k1_relat_1(X2),X1)),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_12])).

fof(c_0_16,plain,(
    ! [X28,X29,X30] :
      ( ( ~ r2_hidden(k4_tarski(X28,X29),X30)
        | r2_hidden(X29,k11_relat_1(X30,X28))
        | ~ v1_relat_1(X30) )
      & ( ~ r2_hidden(X29,k11_relat_1(X30,X28))
        | r2_hidden(k4_tarski(X28,X29),X30)
        | ~ v1_relat_1(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t204_relat_1])])])).

fof(c_0_17,negated_conjecture,
    ( v1_relat_1(esk7_0)
    & ( ~ r2_hidden(esk6_0,k1_relat_1(esk7_0))
      | k11_relat_1(esk7_0,esk6_0) = k1_xboole_0 )
    & ( r2_hidden(esk6_0,k1_relat_1(esk7_0))
      | k11_relat_1(esk7_0,esk6_0) != k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_19,plain,(
    ! [X14] :
      ( X14 = k1_xboole_0
      | r2_hidden(esk2_1(X14),X14) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_20,plain,
    ( ~ r2_hidden(k4_tarski(X1,esk3_3(k1_xboole_0,k1_relat_1(k1_xboole_0),X1)),X2)
    | ~ r2_hidden(X1,k1_relat_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_21,plain,
    ( r2_hidden(X2,k11_relat_1(X3,X1))
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( k11_relat_1(esk7_0,esk6_0) = k1_xboole_0
    | ~ r2_hidden(esk6_0,k1_relat_1(esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2) ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( r2_hidden(k4_tarski(X3,X1),X2)
    | ~ r2_hidden(X1,k11_relat_1(X2,X3))
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( ~ r2_hidden(X1,k1_relat_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_15])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(k4_tarski(esk6_0,X1),esk7_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_29,plain,
    ( k11_relat_1(X1,X2) = k1_xboole_0
    | r2_hidden(k4_tarski(X2,esk2_1(k11_relat_1(X1,X2))),X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_30,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_27,c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk3_3(esk7_0,k1_relat_1(esk7_0),esk6_0),k1_xboole_0)
    | ~ r2_hidden(esk6_0,k1_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_15])).

cnf(c_0_32,negated_conjecture,
    ( k11_relat_1(esk7_0,X1) = k1_xboole_0
    | r2_hidden(k4_tarski(X1,esk2_1(k11_relat_1(esk7_0,X1))),esk7_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_23])).

cnf(c_0_33,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_27,c_0_30])).

cnf(c_0_34,negated_conjecture,
    ( ~ r2_hidden(esk3_3(esk7_0,k1_relat_1(esk7_0),esk6_0),X1)
    | ~ r2_hidden(esk6_0,k1_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk6_0,k1_relat_1(esk7_0))
    | k11_relat_1(esk7_0,esk6_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_36,negated_conjecture,
    ( k11_relat_1(esk7_0,esk6_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_32]),c_0_33])).

cnf(c_0_37,negated_conjecture,
    ( ~ r2_hidden(esk6_0,k1_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_36])]),c_0_37]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:30:01 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SOS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.027 s
% 0.20/0.38  # Presaturation interreduction done
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.20/0.38  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 0.20/0.38  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 0.20/0.38  fof(t205_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(r2_hidden(X1,k1_relat_1(X2))<=>k11_relat_1(X2,X1)!=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t205_relat_1)).
% 0.20/0.38  fof(t204_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)<=>r2_hidden(X2,k11_relat_1(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t204_relat_1)).
% 0.20/0.38  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.20/0.38  fof(c_0_6, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X8,X5)|~r2_hidden(X8,X7)|X7!=k4_xboole_0(X5,X6))&(~r2_hidden(X8,X6)|~r2_hidden(X8,X7)|X7!=k4_xboole_0(X5,X6)))&(~r2_hidden(X9,X5)|r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k4_xboole_0(X5,X6)))&((~r2_hidden(esk1_3(X10,X11,X12),X12)|(~r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k4_xboole_0(X10,X11))&((r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k4_xboole_0(X10,X11))&(~r2_hidden(esk1_3(X10,X11,X12),X11)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k4_xboole_0(X10,X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.20/0.38  cnf(c_0_7, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.38  fof(c_0_8, plain, ![X16]:k4_xboole_0(X16,k1_xboole_0)=X16, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.20/0.38  fof(c_0_9, plain, ![X17, X18, X19, X21, X22, X23, X24, X26]:(((~r2_hidden(X19,X18)|r2_hidden(k4_tarski(X19,esk3_3(X17,X18,X19)),X17)|X18!=k1_relat_1(X17))&(~r2_hidden(k4_tarski(X21,X22),X17)|r2_hidden(X21,X18)|X18!=k1_relat_1(X17)))&((~r2_hidden(esk4_2(X23,X24),X24)|~r2_hidden(k4_tarski(esk4_2(X23,X24),X26),X23)|X24=k1_relat_1(X23))&(r2_hidden(esk4_2(X23,X24),X24)|r2_hidden(k4_tarski(esk4_2(X23,X24),esk5_2(X23,X24)),X23)|X24=k1_relat_1(X23)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 0.20/0.38  cnf(c_0_10, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_7])).
% 0.20/0.38  cnf(c_0_11, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.38  cnf(c_0_12, plain, (r2_hidden(k4_tarski(X1,esk3_3(X3,X2,X1)),X3)|~r2_hidden(X1,X2)|X2!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.38  fof(c_0_13, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(r2_hidden(X1,k1_relat_1(X2))<=>k11_relat_1(X2,X1)!=k1_xboole_0))), inference(assume_negation,[status(cth)],[t205_relat_1])).
% 0.20/0.38  cnf(c_0_14, plain, (~r2_hidden(X1,k1_xboole_0)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.20/0.38  cnf(c_0_15, plain, (r2_hidden(k4_tarski(X1,esk3_3(X2,k1_relat_1(X2),X1)),X2)|~r2_hidden(X1,k1_relat_1(X2))), inference(er,[status(thm)],[c_0_12])).
% 0.20/0.38  fof(c_0_16, plain, ![X28, X29, X30]:((~r2_hidden(k4_tarski(X28,X29),X30)|r2_hidden(X29,k11_relat_1(X30,X28))|~v1_relat_1(X30))&(~r2_hidden(X29,k11_relat_1(X30,X28))|r2_hidden(k4_tarski(X28,X29),X30)|~v1_relat_1(X30))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t204_relat_1])])])).
% 0.20/0.38  fof(c_0_17, negated_conjecture, (v1_relat_1(esk7_0)&((~r2_hidden(esk6_0,k1_relat_1(esk7_0))|k11_relat_1(esk7_0,esk6_0)=k1_xboole_0)&(r2_hidden(esk6_0,k1_relat_1(esk7_0))|k11_relat_1(esk7_0,esk6_0)!=k1_xboole_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 0.20/0.38  cnf(c_0_18, plain, (r2_hidden(X1,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.38  fof(c_0_19, plain, ![X14]:(X14=k1_xboole_0|r2_hidden(esk2_1(X14),X14)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.20/0.38  cnf(c_0_20, plain, (~r2_hidden(k4_tarski(X1,esk3_3(k1_xboole_0,k1_relat_1(k1_xboole_0),X1)),X2)|~r2_hidden(X1,k1_relat_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.20/0.38  cnf(c_0_21, plain, (r2_hidden(X2,k11_relat_1(X3,X1))|~r2_hidden(k4_tarski(X1,X2),X3)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.38  cnf(c_0_22, negated_conjecture, (k11_relat_1(esk7_0,esk6_0)=k1_xboole_0|~r2_hidden(esk6_0,k1_relat_1(esk7_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.38  cnf(c_0_23, negated_conjecture, (v1_relat_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.38  cnf(c_0_24, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)), inference(er,[status(thm)],[c_0_18])).
% 0.20/0.38  cnf(c_0_25, plain, (r2_hidden(k4_tarski(X3,X1),X2)|~r2_hidden(X1,k11_relat_1(X2,X3))|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.38  cnf(c_0_26, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.38  cnf(c_0_27, plain, (~r2_hidden(X1,k1_relat_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_20, c_0_15])).
% 0.20/0.38  cnf(c_0_28, negated_conjecture, (r2_hidden(X1,k1_xboole_0)|~r2_hidden(k4_tarski(esk6_0,X1),esk7_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23])]), c_0_24])).
% 0.20/0.38  cnf(c_0_29, plain, (k11_relat_1(X1,X2)=k1_xboole_0|r2_hidden(k4_tarski(X2,esk2_1(k11_relat_1(X1,X2))),X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.20/0.38  cnf(c_0_30, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_27, c_0_26])).
% 0.20/0.38  cnf(c_0_31, negated_conjecture, (r2_hidden(esk3_3(esk7_0,k1_relat_1(esk7_0),esk6_0),k1_xboole_0)|~r2_hidden(esk6_0,k1_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_28, c_0_15])).
% 0.20/0.38  cnf(c_0_32, negated_conjecture, (k11_relat_1(esk7_0,X1)=k1_xboole_0|r2_hidden(k4_tarski(X1,esk2_1(k11_relat_1(esk7_0,X1))),esk7_0)), inference(spm,[status(thm)],[c_0_29, c_0_23])).
% 0.20/0.38  cnf(c_0_33, plain, (~r2_hidden(X1,k1_xboole_0)), inference(rw,[status(thm)],[c_0_27, c_0_30])).
% 0.20/0.38  cnf(c_0_34, negated_conjecture, (~r2_hidden(esk3_3(esk7_0,k1_relat_1(esk7_0),esk6_0),X1)|~r2_hidden(esk6_0,k1_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_14, c_0_31])).
% 0.20/0.38  cnf(c_0_35, negated_conjecture, (r2_hidden(esk6_0,k1_relat_1(esk7_0))|k11_relat_1(esk7_0,esk6_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.38  cnf(c_0_36, negated_conjecture, (k11_relat_1(esk7_0,esk6_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_32]), c_0_33])).
% 0.20/0.38  cnf(c_0_37, negated_conjecture, (~r2_hidden(esk6_0,k1_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_34, c_0_31])).
% 0.20/0.38  cnf(c_0_38, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_36])]), c_0_37]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 39
% 0.20/0.38  # Proof object clause steps            : 26
% 0.20/0.38  # Proof object formula steps           : 13
% 0.20/0.38  # Proof object conjectures             : 13
% 0.20/0.38  # Proof object clause conjectures      : 10
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 10
% 0.20/0.38  # Proof object initial formulas used   : 6
% 0.20/0.38  # Proof object generating inferences   : 11
% 0.20/0.38  # Proof object simplifying inferences  : 11
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 6
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 17
% 0.20/0.38  # Removed in clause preprocessing      : 0
% 0.20/0.38  # Initial clauses in saturation        : 17
% 0.20/0.38  # Processed clauses                    : 80
% 0.20/0.38  # ...of these trivial                  : 1
% 0.20/0.38  # ...subsumed                          : 17
% 0.20/0.38  # ...remaining for further processing  : 62
% 0.20/0.38  # Other redundant clauses eliminated   : 5
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 1
% 0.20/0.38  # Backward-rewritten                   : 3
% 0.20/0.38  # Generated clauses                    : 116
% 0.20/0.38  # ...of the previous two non-trivial   : 99
% 0.20/0.38  # Contextual simplify-reflections      : 1
% 0.20/0.38  # Paramodulations                      : 109
% 0.20/0.38  # Factorizations                       : 2
% 0.20/0.38  # Equation resolutions                 : 5
% 0.20/0.38  # Propositional unsat checks           : 0
% 0.20/0.38  #    Propositional check models        : 0
% 0.20/0.38  #    Propositional check unsatisfiable : 0
% 0.20/0.38  #    Propositional clauses             : 0
% 0.20/0.38  #    Propositional clauses after purity: 0
% 0.20/0.38  #    Propositional unsat core size     : 0
% 0.20/0.38  #    Propositional preprocessing time  : 0.000
% 0.20/0.38  #    Propositional encoding time       : 0.000
% 0.20/0.38  #    Propositional solver time         : 0.000
% 0.20/0.38  #    Success case prop preproc time    : 0.000
% 0.20/0.38  #    Success case prop encoding time   : 0.000
% 0.20/0.38  #    Success case prop solver time     : 0.000
% 0.20/0.38  # Current number of processed clauses  : 36
% 0.20/0.38  #    Positive orientable unit clauses  : 6
% 0.20/0.38  #    Positive unorientable unit clauses: 0
% 0.20/0.38  #    Negative unit clauses             : 2
% 0.20/0.38  #    Non-unit-clauses                  : 28
% 0.20/0.38  # Current number of unprocessed clauses: 49
% 0.20/0.38  # ...number of literals in the above   : 146
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 21
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 93
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 67
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 3
% 0.20/0.38  # Unit Clause-clause subsumption calls : 34
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 6
% 0.20/0.38  # BW rewrite match successes           : 2
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 2784
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.031 s
% 0.20/0.38  # System time              : 0.003 s
% 0.20/0.38  # Total time               : 0.034 s
% 0.20/0.38  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
