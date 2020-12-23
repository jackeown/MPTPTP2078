%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:52:17 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 306 expanded)
%              Number of clauses        :   36 ( 154 expanded)
%              Number of leaves         :    7 (  73 expanded)
%              Depth                    :   16
%              Number of atoms          :  139 (1095 expanded)
%              Number of equality atoms :   38 ( 237 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   1 average)

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

fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(t204_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> r2_hidden(X2,k11_relat_1(X3,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

fof(t205_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X1,k1_relat_1(X2))
      <=> k11_relat_1(X2,X1) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

fof(c_0_7,plain,(
    ! [X12,X13,X14,X15,X16,X17] :
      ( ( ~ r2_hidden(X14,X13)
        | X14 = X12
        | X13 != k1_tarski(X12) )
      & ( X15 != X12
        | r2_hidden(X15,X13)
        | X13 != k1_tarski(X12) )
      & ( ~ r2_hidden(esk2_2(X16,X17),X17)
        | esk2_2(X16,X17) != X16
        | X17 = k1_tarski(X16) )
      & ( r2_hidden(esk2_2(X16,X17),X17)
        | esk2_2(X16,X17) = X16
        | X17 = k1_tarski(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_8,plain,(
    ! [X19] : k2_tarski(X19,X19) = k1_tarski(X19) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_9,plain,(
    ! [X5,X6,X8,X9,X10] :
      ( ( r2_hidden(esk1_2(X5,X6),X5)
        | r1_xboole_0(X5,X6) )
      & ( r2_hidden(esk1_2(X5,X6),X6)
        | r1_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X10,X8)
        | ~ r2_hidden(X10,X9)
        | ~ r1_xboole_0(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_10,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X2) ),
    inference(rw,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_15,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X3)
    | ~ r1_xboole_0(X3,X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_16,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_17,plain,(
    ! [X11] : r1_xboole_0(X11,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,k2_tarski(X1,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_14])])).

cnf(c_0_19,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_20,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_xboole_0(X2,k2_tarski(X1,X1)) ),
    inference(spm,[status(thm)],[c_0_12,c_0_18])).

cnf(c_0_22,plain,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

fof(c_0_23,plain,(
    ! [X20,X21,X22,X24,X25,X26,X27,X29] :
      ( ( ~ r2_hidden(X22,X21)
        | r2_hidden(k4_tarski(X22,esk3_3(X20,X21,X22)),X20)
        | X21 != k1_relat_1(X20) )
      & ( ~ r2_hidden(k4_tarski(X24,X25),X20)
        | r2_hidden(X24,X21)
        | X21 != k1_relat_1(X20) )
      & ( ~ r2_hidden(esk4_2(X26,X27),X27)
        | ~ r2_hidden(k4_tarski(esk4_2(X26,X27),X29),X26)
        | X27 = k1_relat_1(X26) )
      & ( r2_hidden(esk4_2(X26,X27),X27)
        | r2_hidden(k4_tarski(esk4_2(X26,X27),esk5_2(X26,X27)),X26)
        | X27 = k1_relat_1(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

cnf(c_0_24,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_25,plain,
    ( r2_hidden(esk4_2(X1,X2),X2)
    | r2_hidden(k4_tarski(esk4_2(X1,X2),esk5_2(X1,X2)),X1)
    | X2 = k1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_26,plain,
    ( X1 = k1_relat_1(k1_xboole_0)
    | r2_hidden(esk4_2(k1_xboole_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

fof(c_0_27,plain,(
    ! [X31,X32,X33] :
      ( ( ~ r2_hidden(k4_tarski(X31,X32),X33)
        | r2_hidden(X32,k11_relat_1(X33,X31))
        | ~ v1_relat_1(X33) )
      & ( ~ r2_hidden(X32,k11_relat_1(X33,X31))
        | r2_hidden(k4_tarski(X31,X32),X33)
        | ~ v1_relat_1(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t204_relat_1])])])).

fof(c_0_28,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( r2_hidden(X1,k1_relat_1(X2))
        <=> k11_relat_1(X2,X1) != k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t205_relat_1])).

cnf(c_0_29,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_24,c_0_26])).

cnf(c_0_30,plain,
    ( r2_hidden(k4_tarski(X3,X1),X2)
    | ~ r2_hidden(X1,k11_relat_1(X2,X3))
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_31,negated_conjecture,
    ( v1_relat_1(esk7_0)
    & ( ~ r2_hidden(esk6_0,k1_relat_1(esk7_0))
      | k11_relat_1(esk7_0,esk6_0) = k1_xboole_0 )
    & ( r2_hidden(esk6_0,k1_relat_1(esk7_0))
      | k11_relat_1(esk7_0,esk6_0) != k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_28])])])).

cnf(c_0_32,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk4_2(k1_xboole_0,X1),X1) ),
    inference(rw,[status(thm)],[c_0_26,c_0_29])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,plain,
    ( r2_hidden(k4_tarski(X1,esk1_2(X2,k11_relat_1(X3,X1))),X3)
    | r1_xboole_0(X2,k11_relat_1(X3,X1))
    | ~ v1_relat_1(X3) ),
    inference(spm,[status(thm)],[c_0_30,c_0_16])).

cnf(c_0_35,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_36,plain,
    ( X1 = k1_xboole_0
    | ~ r2_hidden(esk4_2(k1_xboole_0,X1),X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_32])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2) ),
    inference(er,[status(thm)],[c_0_33])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk1_2(X2,k11_relat_1(esk7_0,X1))),esk7_0)
    | r1_xboole_0(X2,k11_relat_1(esk7_0,X1)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_39,plain,
    ( X1 = k1_xboole_0
    | ~ r1_xboole_0(k2_tarski(esk4_2(k1_xboole_0,X1),esk4_2(k1_xboole_0,X1)),X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_18])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(X1,k1_relat_1(esk7_0))
    | r1_xboole_0(X2,k11_relat_1(esk7_0,X1)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk6_0,k1_relat_1(esk7_0))
    | k11_relat_1(esk7_0,esk6_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_42,negated_conjecture,
    ( k11_relat_1(esk7_0,X1) = k1_xboole_0
    | r2_hidden(X1,k1_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_43,negated_conjecture,
    ( k11_relat_1(esk7_0,esk6_0) = k1_xboole_0
    | ~ r2_hidden(esk6_0,k1_relat_1(esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk6_0,k1_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_45,plain,
    ( r2_hidden(k4_tarski(X1,esk3_3(X3,X2,X1)),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_46,plain,
    ( r2_hidden(X2,k11_relat_1(X3,X1))
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_47,negated_conjecture,
    ( k11_relat_1(esk7_0,esk6_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_44])])).

cnf(c_0_48,plain,
    ( r2_hidden(k4_tarski(X1,esk3_3(X2,k1_relat_1(X2),X1)),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_45])).

cnf(c_0_49,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk6_0,X1),esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_35])]),c_0_24])).

cnf(c_0_50,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_44]),c_0_49]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:30:29 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S03FN
% 0.21/0.38  # and selection function PSelectLComplex.
% 0.21/0.38  #
% 0.21/0.38  # Preprocessing time       : 0.027 s
% 0.21/0.38  # Presaturation interreduction done
% 0.21/0.38  
% 0.21/0.38  # Proof found!
% 0.21/0.38  # SZS status Theorem
% 0.21/0.38  # SZS output start CNFRefutation
% 0.21/0.38  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 0.21/0.38  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.21/0.38  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.21/0.38  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.21/0.38  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 0.21/0.38  fof(t204_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)<=>r2_hidden(X2,k11_relat_1(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t204_relat_1)).
% 0.21/0.38  fof(t205_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(r2_hidden(X1,k1_relat_1(X2))<=>k11_relat_1(X2,X1)!=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t205_relat_1)).
% 0.21/0.38  fof(c_0_7, plain, ![X12, X13, X14, X15, X16, X17]:(((~r2_hidden(X14,X13)|X14=X12|X13!=k1_tarski(X12))&(X15!=X12|r2_hidden(X15,X13)|X13!=k1_tarski(X12)))&((~r2_hidden(esk2_2(X16,X17),X17)|esk2_2(X16,X17)!=X16|X17=k1_tarski(X16))&(r2_hidden(esk2_2(X16,X17),X17)|esk2_2(X16,X17)=X16|X17=k1_tarski(X16)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.21/0.38  fof(c_0_8, plain, ![X19]:k2_tarski(X19,X19)=k1_tarski(X19), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.21/0.38  fof(c_0_9, plain, ![X5, X6, X8, X9, X10]:(((r2_hidden(esk1_2(X5,X6),X5)|r1_xboole_0(X5,X6))&(r2_hidden(esk1_2(X5,X6),X6)|r1_xboole_0(X5,X6)))&(~r2_hidden(X10,X8)|~r2_hidden(X10,X9)|~r1_xboole_0(X8,X9))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.21/0.38  cnf(c_0_10, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.21/0.38  cnf(c_0_11, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.21/0.38  cnf(c_0_12, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.21/0.38  cnf(c_0_13, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.21/0.38  cnf(c_0_14, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X2,X2)), inference(rw,[status(thm)],[c_0_10, c_0_11])).
% 0.21/0.38  cnf(c_0_15, plain, (r1_xboole_0(X1,X2)|~r2_hidden(esk1_2(X1,X2),X3)|~r1_xboole_0(X3,X1)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.21/0.38  cnf(c_0_16, plain, (r2_hidden(esk1_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.21/0.38  fof(c_0_17, plain, ![X11]:r1_xboole_0(X11,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.21/0.38  cnf(c_0_18, plain, (r2_hidden(X1,k2_tarski(X1,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_14])])).
% 0.21/0.38  cnf(c_0_19, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.21/0.38  cnf(c_0_20, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.38  cnf(c_0_21, plain, (~r2_hidden(X1,X2)|~r1_xboole_0(X2,k2_tarski(X1,X1))), inference(spm,[status(thm)],[c_0_12, c_0_18])).
% 0.21/0.38  cnf(c_0_22, plain, (r1_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.21/0.38  fof(c_0_23, plain, ![X20, X21, X22, X24, X25, X26, X27, X29]:(((~r2_hidden(X22,X21)|r2_hidden(k4_tarski(X22,esk3_3(X20,X21,X22)),X20)|X21!=k1_relat_1(X20))&(~r2_hidden(k4_tarski(X24,X25),X20)|r2_hidden(X24,X21)|X21!=k1_relat_1(X20)))&((~r2_hidden(esk4_2(X26,X27),X27)|~r2_hidden(k4_tarski(esk4_2(X26,X27),X29),X26)|X27=k1_relat_1(X26))&(r2_hidden(esk4_2(X26,X27),X27)|r2_hidden(k4_tarski(esk4_2(X26,X27),esk5_2(X26,X27)),X26)|X27=k1_relat_1(X26)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 0.21/0.38  cnf(c_0_24, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.21/0.38  cnf(c_0_25, plain, (r2_hidden(esk4_2(X1,X2),X2)|r2_hidden(k4_tarski(esk4_2(X1,X2),esk5_2(X1,X2)),X1)|X2=k1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.38  cnf(c_0_26, plain, (X1=k1_relat_1(k1_xboole_0)|r2_hidden(esk4_2(k1_xboole_0,X1),X1)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.21/0.38  fof(c_0_27, plain, ![X31, X32, X33]:((~r2_hidden(k4_tarski(X31,X32),X33)|r2_hidden(X32,k11_relat_1(X33,X31))|~v1_relat_1(X33))&(~r2_hidden(X32,k11_relat_1(X33,X31))|r2_hidden(k4_tarski(X31,X32),X33)|~v1_relat_1(X33))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t204_relat_1])])])).
% 0.21/0.38  fof(c_0_28, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(r2_hidden(X1,k1_relat_1(X2))<=>k11_relat_1(X2,X1)!=k1_xboole_0))), inference(assume_negation,[status(cth)],[t205_relat_1])).
% 0.21/0.38  cnf(c_0_29, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_24, c_0_26])).
% 0.21/0.38  cnf(c_0_30, plain, (r2_hidden(k4_tarski(X3,X1),X2)|~r2_hidden(X1,k11_relat_1(X2,X3))|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.21/0.38  fof(c_0_31, negated_conjecture, (v1_relat_1(esk7_0)&((~r2_hidden(esk6_0,k1_relat_1(esk7_0))|k11_relat_1(esk7_0,esk6_0)=k1_xboole_0)&(r2_hidden(esk6_0,k1_relat_1(esk7_0))|k11_relat_1(esk7_0,esk6_0)!=k1_xboole_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_28])])])).
% 0.21/0.38  cnf(c_0_32, plain, (X1=k1_xboole_0|r2_hidden(esk4_2(k1_xboole_0,X1),X1)), inference(rw,[status(thm)],[c_0_26, c_0_29])).
% 0.21/0.38  cnf(c_0_33, plain, (r2_hidden(X1,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.38  cnf(c_0_34, plain, (r2_hidden(k4_tarski(X1,esk1_2(X2,k11_relat_1(X3,X1))),X3)|r1_xboole_0(X2,k11_relat_1(X3,X1))|~v1_relat_1(X3)), inference(spm,[status(thm)],[c_0_30, c_0_16])).
% 0.21/0.38  cnf(c_0_35, negated_conjecture, (v1_relat_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.21/0.38  cnf(c_0_36, plain, (X1=k1_xboole_0|~r2_hidden(esk4_2(k1_xboole_0,X1),X2)|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_12, c_0_32])).
% 0.21/0.38  cnf(c_0_37, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)), inference(er,[status(thm)],[c_0_33])).
% 0.21/0.38  cnf(c_0_38, negated_conjecture, (r2_hidden(k4_tarski(X1,esk1_2(X2,k11_relat_1(esk7_0,X1))),esk7_0)|r1_xboole_0(X2,k11_relat_1(esk7_0,X1))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.21/0.38  cnf(c_0_39, plain, (X1=k1_xboole_0|~r1_xboole_0(k2_tarski(esk4_2(k1_xboole_0,X1),esk4_2(k1_xboole_0,X1)),X1)), inference(spm,[status(thm)],[c_0_36, c_0_18])).
% 0.21/0.38  cnf(c_0_40, negated_conjecture, (r2_hidden(X1,k1_relat_1(esk7_0))|r1_xboole_0(X2,k11_relat_1(esk7_0,X1))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.21/0.38  cnf(c_0_41, negated_conjecture, (r2_hidden(esk6_0,k1_relat_1(esk7_0))|k11_relat_1(esk7_0,esk6_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.21/0.38  cnf(c_0_42, negated_conjecture, (k11_relat_1(esk7_0,X1)=k1_xboole_0|r2_hidden(X1,k1_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.21/0.38  cnf(c_0_43, negated_conjecture, (k11_relat_1(esk7_0,esk6_0)=k1_xboole_0|~r2_hidden(esk6_0,k1_relat_1(esk7_0))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.21/0.38  cnf(c_0_44, negated_conjecture, (r2_hidden(esk6_0,k1_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.21/0.38  cnf(c_0_45, plain, (r2_hidden(k4_tarski(X1,esk3_3(X3,X2,X1)),X3)|~r2_hidden(X1,X2)|X2!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.38  cnf(c_0_46, plain, (r2_hidden(X2,k11_relat_1(X3,X1))|~r2_hidden(k4_tarski(X1,X2),X3)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.21/0.38  cnf(c_0_47, negated_conjecture, (k11_relat_1(esk7_0,esk6_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_44])])).
% 0.21/0.38  cnf(c_0_48, plain, (r2_hidden(k4_tarski(X1,esk3_3(X2,k1_relat_1(X2),X1)),X2)|~r2_hidden(X1,k1_relat_1(X2))), inference(er,[status(thm)],[c_0_45])).
% 0.21/0.38  cnf(c_0_49, negated_conjecture, (~r2_hidden(k4_tarski(esk6_0,X1),esk7_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_35])]), c_0_24])).
% 0.21/0.38  cnf(c_0_50, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_44]), c_0_49]), ['proof']).
% 0.21/0.38  # SZS output end CNFRefutation
% 0.21/0.38  # Proof object total steps             : 51
% 0.21/0.38  # Proof object clause steps            : 36
% 0.21/0.38  # Proof object formula steps           : 15
% 0.21/0.38  # Proof object conjectures             : 13
% 0.21/0.38  # Proof object clause conjectures      : 10
% 0.21/0.38  # Proof object formula conjectures     : 3
% 0.21/0.38  # Proof object initial clauses used    : 14
% 0.21/0.38  # Proof object initial formulas used   : 7
% 0.21/0.38  # Proof object generating inferences   : 16
% 0.21/0.38  # Proof object simplifying inferences  : 12
% 0.21/0.38  # Training examples: 0 positive, 0 negative
% 0.21/0.38  # Parsed axioms                        : 7
% 0.21/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.38  # Initial clauses                      : 18
% 0.21/0.38  # Removed in clause preprocessing      : 1
% 0.21/0.38  # Initial clauses in saturation        : 17
% 0.21/0.38  # Processed clauses                    : 100
% 0.21/0.38  # ...of these trivial                  : 0
% 0.21/0.38  # ...subsumed                          : 21
% 0.21/0.38  # ...remaining for further processing  : 78
% 0.21/0.38  # Other redundant clauses eliminated   : 6
% 0.21/0.38  # Clauses deleted for lack of memory   : 0
% 0.21/0.38  # Backward-subsumed                    : 0
% 0.21/0.38  # Backward-rewritten                   : 3
% 0.21/0.38  # Generated clauses                    : 277
% 0.21/0.38  # ...of the previous two non-trivial   : 240
% 0.21/0.38  # Contextual simplify-reflections      : 0
% 0.21/0.38  # Paramodulations                      : 272
% 0.21/0.38  # Factorizations                       : 0
% 0.21/0.38  # Equation resolutions                 : 6
% 0.21/0.38  # Propositional unsat checks           : 0
% 0.21/0.38  #    Propositional check models        : 0
% 0.21/0.38  #    Propositional check unsatisfiable : 0
% 0.21/0.38  #    Propositional clauses             : 0
% 0.21/0.38  #    Propositional clauses after purity: 0
% 0.21/0.38  #    Propositional unsat core size     : 0
% 0.21/0.38  #    Propositional preprocessing time  : 0.000
% 0.21/0.38  #    Propositional encoding time       : 0.000
% 0.21/0.38  #    Propositional solver time         : 0.000
% 0.21/0.38  #    Success case prop preproc time    : 0.000
% 0.21/0.38  #    Success case prop encoding time   : 0.000
% 0.21/0.38  #    Success case prop solver time     : 0.000
% 0.21/0.38  # Current number of processed clauses  : 54
% 0.21/0.38  #    Positive orientable unit clauses  : 9
% 0.21/0.38  #    Positive unorientable unit clauses: 0
% 0.21/0.38  #    Negative unit clauses             : 2
% 0.21/0.38  #    Non-unit-clauses                  : 43
% 0.21/0.38  # Current number of unprocessed clauses: 172
% 0.21/0.38  # ...number of literals in the above   : 609
% 0.21/0.38  # Current number of archived formulas  : 0
% 0.21/0.38  # Current number of archived clauses   : 21
% 0.21/0.38  # Clause-clause subsumption calls (NU) : 328
% 0.21/0.38  # Rec. Clause-clause subsumption calls : 261
% 0.21/0.38  # Non-unit clause-clause subsumptions  : 14
% 0.21/0.38  # Unit Clause-clause subsumption calls : 17
% 0.21/0.38  # Rewrite failures with RHS unbound    : 0
% 0.21/0.38  # BW rewrite match attempts            : 3
% 0.21/0.38  # BW rewrite match successes           : 2
% 0.21/0.38  # Condensation attempts                : 0
% 0.21/0.38  # Condensation successes               : 0
% 0.21/0.38  # Termbank termtop insertions          : 4626
% 0.21/0.38  
% 0.21/0.38  # -------------------------------------------------
% 0.21/0.38  # User time                : 0.035 s
% 0.21/0.38  # System time              : 0.003 s
% 0.21/0.38  # Total time               : 0.038 s
% 0.21/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
