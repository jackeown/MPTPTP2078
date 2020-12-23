%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:47:10 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 135 expanded)
%              Number of clauses        :   34 (  67 expanded)
%              Number of leaves         :   10 (  33 expanded)
%              Depth                    :   12
%              Number of atoms          :  161 ( 499 expanded)
%              Number of equality atoms :   83 ( 302 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

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

fof(t4_setfam_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(k1_setfam_1(X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).

fof(t11_setfam_1,conjecture,(
    ! [X1] : k1_setfam_1(k1_tarski(X1)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t6_setfam_1,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
         => r1_tarski(X2,X3) )
     => ( X1 = k1_xboole_0
        | r1_tarski(X2,k1_setfam_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_setfam_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(c_0_10,plain,(
    ! [X20,X21,X22,X23,X24,X25,X26,X27,X28,X29] :
      ( ( ~ r2_hidden(X24,X23)
        | X24 = X20
        | X24 = X21
        | X24 = X22
        | X23 != k1_enumset1(X20,X21,X22) )
      & ( X25 != X20
        | r2_hidden(X25,X23)
        | X23 != k1_enumset1(X20,X21,X22) )
      & ( X25 != X21
        | r2_hidden(X25,X23)
        | X23 != k1_enumset1(X20,X21,X22) )
      & ( X25 != X22
        | r2_hidden(X25,X23)
        | X23 != k1_enumset1(X20,X21,X22) )
      & ( esk2_4(X26,X27,X28,X29) != X26
        | ~ r2_hidden(esk2_4(X26,X27,X28,X29),X29)
        | X29 = k1_enumset1(X26,X27,X28) )
      & ( esk2_4(X26,X27,X28,X29) != X27
        | ~ r2_hidden(esk2_4(X26,X27,X28,X29),X29)
        | X29 = k1_enumset1(X26,X27,X28) )
      & ( esk2_4(X26,X27,X28,X29) != X28
        | ~ r2_hidden(esk2_4(X26,X27,X28,X29),X29)
        | X29 = k1_enumset1(X26,X27,X28) )
      & ( r2_hidden(esk2_4(X26,X27,X28,X29),X29)
        | esk2_4(X26,X27,X28,X29) = X26
        | esk2_4(X26,X27,X28,X29) = X27
        | esk2_4(X26,X27,X28,X29) = X28
        | X29 = k1_enumset1(X26,X27,X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

fof(c_0_11,plain,(
    ! [X41,X42,X43] : k2_enumset1(X41,X41,X42,X43) = k1_enumset1(X41,X42,X43) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_12,plain,(
    ! [X6,X7,X8,X9,X10,X11,X12,X13] :
      ( ( r2_hidden(X9,X6)
        | ~ r2_hidden(X9,X8)
        | X8 != k4_xboole_0(X6,X7) )
      & ( ~ r2_hidden(X9,X7)
        | ~ r2_hidden(X9,X8)
        | X8 != k4_xboole_0(X6,X7) )
      & ( ~ r2_hidden(X10,X6)
        | r2_hidden(X10,X7)
        | r2_hidden(X10,X8)
        | X8 != k4_xboole_0(X6,X7) )
      & ( ~ r2_hidden(esk1_3(X11,X12,X13),X13)
        | ~ r2_hidden(esk1_3(X11,X12,X13),X11)
        | r2_hidden(esk1_3(X11,X12,X13),X12)
        | X13 = k4_xboole_0(X11,X12) )
      & ( r2_hidden(esk1_3(X11,X12,X13),X11)
        | r2_hidden(esk1_3(X11,X12,X13),X13)
        | X13 = k4_xboole_0(X11,X12) )
      & ( ~ r2_hidden(esk1_3(X11,X12,X13),X12)
        | r2_hidden(esk1_3(X11,X12,X13),X13)
        | X13 = k4_xboole_0(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

cnf(c_0_13,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X5,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,plain,(
    ! [X17] : k4_xboole_0(X17,k1_xboole_0) = X17 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_17,plain,(
    ! [X46,X47] :
      ( ~ r2_hidden(X46,X47)
      | r1_tarski(k1_setfam_1(X47),X46) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_setfam_1])])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X4,X4,X5,X2) ),
    inference(rw,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X2,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_20,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_22,negated_conjecture,(
    ~ ! [X1] : k1_setfam_1(k1_tarski(X1)) = X1 ),
    inference(assume_negation,[status(cth)],[t11_setfam_1])).

fof(c_0_23,plain,(
    ! [X15,X16] :
      ( ( r1_tarski(X15,X16)
        | X15 != X16 )
      & ( r1_tarski(X16,X15)
        | X15 != X16 )
      & ( ~ r1_tarski(X15,X16)
        | ~ r1_tarski(X16,X15)
        | X15 = X16 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_24,plain,
    ( r1_tarski(k1_setfam_1(X2),X1)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,k2_enumset1(X2,X2,X3,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_18])])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X2,X2,X4,X5) ),
    inference(rw,[status(thm)],[c_0_19,c_0_14])).

fof(c_0_27,plain,(
    ! [X48,X49] :
      ( ( r2_hidden(esk4_2(X48,X49),X48)
        | X48 = k1_xboole_0
        | r1_tarski(X49,k1_setfam_1(X48)) )
      & ( ~ r1_tarski(X49,esk4_2(X48,X49))
        | X48 = k1_xboole_0
        | r1_tarski(X49,k1_setfam_1(X48)) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_setfam_1])])])])).

cnf(c_0_28,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

fof(c_0_29,negated_conjecture,(
    k1_setfam_1(k1_tarski(esk5_0)) != esk5_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_22])])])).

fof(c_0_30,plain,(
    ! [X38] : k2_tarski(X38,X38) = k1_tarski(X38) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_31,plain,(
    ! [X39,X40] : k1_enumset1(X39,X39,X40) = k2_tarski(X39,X40) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_32,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X2,X3)),X3) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,k2_enumset1(X1,X1,X2,X3)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_26])])).

cnf(c_0_35,plain,
    ( r2_hidden(esk4_2(X1,X2),X1)
    | X1 = k1_xboole_0
    | r1_tarski(X2,k1_setfam_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_25])).

cnf(c_0_37,plain,
    ( X1 = X3
    | X1 = X4
    | X1 = X5
    | ~ r2_hidden(X1,X2)
    | X2 != k1_enumset1(X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_38,negated_conjecture,
    ( k1_setfam_1(k1_tarski(esk5_0)) != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_41,plain,
    ( k1_setfam_1(k2_enumset1(X1,X1,X2,X3)) = X3
    | ~ r1_tarski(X3,k1_setfam_1(k2_enumset1(X1,X1,X2,X3))) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,k1_setfam_1(k2_enumset1(X2,X2,X3,X4)))
    | r2_hidden(esk4_2(k2_enumset1(X2,X2,X3,X4),X1),k2_enumset1(X2,X2,X3,X4)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])).

cnf(c_0_43,plain,
    ( X1 = X5
    | X1 = X4
    | X1 = X3
    | X2 != k2_enumset1(X3,X3,X4,X5)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_37,c_0_14])).

cnf(c_0_44,negated_conjecture,
    ( k1_setfam_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)) != esk5_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_39]),c_0_40]),c_0_14])).

cnf(c_0_45,plain,
    ( k1_setfam_1(k2_enumset1(X1,X1,X2,X3)) = X3
    | r2_hidden(esk4_2(k2_enumset1(X1,X1,X2,X3),X3),k2_enumset1(X1,X1,X2,X3)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_46,plain,
    ( X1 = X2
    | X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,k2_enumset1(X4,X4,X3,X2)) ),
    inference(er,[status(thm)],[c_0_43])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk4_2(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk5_0),k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_48,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_49,plain,
    ( X2 = k1_xboole_0
    | r1_tarski(X1,k1_setfam_1(X2))
    | ~ r1_tarski(X1,esk4_2(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_50,negated_conjecture,
    ( esk4_2(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk5_0) = esk5_0 ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_51,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_48])).

cnf(c_0_52,negated_conjecture,
    ( k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0) = k1_xboole_0
    | r1_tarski(esk5_0,k1_setfam_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51])])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(esk5_0,k1_setfam_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_52]),c_0_36])).

cnf(c_0_54,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_53]),c_0_44]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:06:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.19/0.49  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.19/0.49  # and selection function SelectNegativeLiterals.
% 0.19/0.49  #
% 0.19/0.49  # Preprocessing time       : 0.028 s
% 0.19/0.49  # Presaturation interreduction done
% 0.19/0.49  
% 0.19/0.49  # Proof found!
% 0.19/0.49  # SZS status Theorem
% 0.19/0.49  # SZS output start CNFRefutation
% 0.19/0.49  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 0.19/0.49  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.49  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.19/0.49  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 0.19/0.49  fof(t4_setfam_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>r1_tarski(k1_setfam_1(X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_setfam_1)).
% 0.19/0.49  fof(t11_setfam_1, conjecture, ![X1]:k1_setfam_1(k1_tarski(X1))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_setfam_1)).
% 0.19/0.49  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.49  fof(t6_setfam_1, axiom, ![X1, X2]:(![X3]:(r2_hidden(X3,X1)=>r1_tarski(X2,X3))=>(X1=k1_xboole_0|r1_tarski(X2,k1_setfam_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_setfam_1)).
% 0.19/0.49  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.49  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.49  fof(c_0_10, plain, ![X20, X21, X22, X23, X24, X25, X26, X27, X28, X29]:(((~r2_hidden(X24,X23)|(X24=X20|X24=X21|X24=X22)|X23!=k1_enumset1(X20,X21,X22))&(((X25!=X20|r2_hidden(X25,X23)|X23!=k1_enumset1(X20,X21,X22))&(X25!=X21|r2_hidden(X25,X23)|X23!=k1_enumset1(X20,X21,X22)))&(X25!=X22|r2_hidden(X25,X23)|X23!=k1_enumset1(X20,X21,X22))))&((((esk2_4(X26,X27,X28,X29)!=X26|~r2_hidden(esk2_4(X26,X27,X28,X29),X29)|X29=k1_enumset1(X26,X27,X28))&(esk2_4(X26,X27,X28,X29)!=X27|~r2_hidden(esk2_4(X26,X27,X28,X29),X29)|X29=k1_enumset1(X26,X27,X28)))&(esk2_4(X26,X27,X28,X29)!=X28|~r2_hidden(esk2_4(X26,X27,X28,X29),X29)|X29=k1_enumset1(X26,X27,X28)))&(r2_hidden(esk2_4(X26,X27,X28,X29),X29)|(esk2_4(X26,X27,X28,X29)=X26|esk2_4(X26,X27,X28,X29)=X27|esk2_4(X26,X27,X28,X29)=X28)|X29=k1_enumset1(X26,X27,X28)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 0.19/0.49  fof(c_0_11, plain, ![X41, X42, X43]:k2_enumset1(X41,X41,X42,X43)=k1_enumset1(X41,X42,X43), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.19/0.49  fof(c_0_12, plain, ![X6, X7, X8, X9, X10, X11, X12, X13]:((((r2_hidden(X9,X6)|~r2_hidden(X9,X8)|X8!=k4_xboole_0(X6,X7))&(~r2_hidden(X9,X7)|~r2_hidden(X9,X8)|X8!=k4_xboole_0(X6,X7)))&(~r2_hidden(X10,X6)|r2_hidden(X10,X7)|r2_hidden(X10,X8)|X8!=k4_xboole_0(X6,X7)))&((~r2_hidden(esk1_3(X11,X12,X13),X13)|(~r2_hidden(esk1_3(X11,X12,X13),X11)|r2_hidden(esk1_3(X11,X12,X13),X12))|X13=k4_xboole_0(X11,X12))&((r2_hidden(esk1_3(X11,X12,X13),X11)|r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k4_xboole_0(X11,X12))&(~r2_hidden(esk1_3(X11,X12,X13),X12)|r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k4_xboole_0(X11,X12))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.19/0.49  cnf(c_0_13, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X5,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.49  cnf(c_0_14, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.49  cnf(c_0_15, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.49  fof(c_0_16, plain, ![X17]:k4_xboole_0(X17,k1_xboole_0)=X17, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.19/0.49  fof(c_0_17, plain, ![X46, X47]:(~r2_hidden(X46,X47)|r1_tarski(k1_setfam_1(X47),X46)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_setfam_1])])).
% 0.19/0.49  cnf(c_0_18, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X4,X4,X5,X2)), inference(rw,[status(thm)],[c_0_13, c_0_14])).
% 0.19/0.49  cnf(c_0_19, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X2,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.49  cnf(c_0_20, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_15])).
% 0.19/0.49  cnf(c_0_21, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.49  fof(c_0_22, negated_conjecture, ~(![X1]:k1_setfam_1(k1_tarski(X1))=X1), inference(assume_negation,[status(cth)],[t11_setfam_1])).
% 0.19/0.49  fof(c_0_23, plain, ![X15, X16]:(((r1_tarski(X15,X16)|X15!=X16)&(r1_tarski(X16,X15)|X15!=X16))&(~r1_tarski(X15,X16)|~r1_tarski(X16,X15)|X15=X16)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.49  cnf(c_0_24, plain, (r1_tarski(k1_setfam_1(X2),X1)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.49  cnf(c_0_25, plain, (r2_hidden(X1,k2_enumset1(X2,X2,X3,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_18])])).
% 0.19/0.49  cnf(c_0_26, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X2,X2,X4,X5)), inference(rw,[status(thm)],[c_0_19, c_0_14])).
% 0.19/0.49  fof(c_0_27, plain, ![X48, X49]:((r2_hidden(esk4_2(X48,X49),X48)|(X48=k1_xboole_0|r1_tarski(X49,k1_setfam_1(X48))))&(~r1_tarski(X49,esk4_2(X48,X49))|(X48=k1_xboole_0|r1_tarski(X49,k1_setfam_1(X48))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_setfam_1])])])])).
% 0.19/0.49  cnf(c_0_28, plain, (~r2_hidden(X1,k1_xboole_0)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.19/0.49  fof(c_0_29, negated_conjecture, k1_setfam_1(k1_tarski(esk5_0))!=esk5_0, inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_22])])])).
% 0.19/0.49  fof(c_0_30, plain, ![X38]:k2_tarski(X38,X38)=k1_tarski(X38), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.49  fof(c_0_31, plain, ![X39, X40]:k1_enumset1(X39,X39,X40)=k2_tarski(X39,X40), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.49  cnf(c_0_32, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.49  cnf(c_0_33, plain, (r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X2,X3)),X3)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.19/0.49  cnf(c_0_34, plain, (r2_hidden(X1,k2_enumset1(X1,X1,X2,X3))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_26])])).
% 0.19/0.49  cnf(c_0_35, plain, (r2_hidden(esk4_2(X1,X2),X1)|X1=k1_xboole_0|r1_tarski(X2,k1_setfam_1(X1))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.49  cnf(c_0_36, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_28, c_0_25])).
% 0.19/0.49  cnf(c_0_37, plain, (X1=X3|X1=X4|X1=X5|~r2_hidden(X1,X2)|X2!=k1_enumset1(X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.49  cnf(c_0_38, negated_conjecture, (k1_setfam_1(k1_tarski(esk5_0))!=esk5_0), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.49  cnf(c_0_39, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.49  cnf(c_0_40, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.49  cnf(c_0_41, plain, (k1_setfam_1(k2_enumset1(X1,X1,X2,X3))=X3|~r1_tarski(X3,k1_setfam_1(k2_enumset1(X1,X1,X2,X3)))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.19/0.49  cnf(c_0_42, plain, (r1_tarski(X1,k1_setfam_1(k2_enumset1(X2,X2,X3,X4)))|r2_hidden(esk4_2(k2_enumset1(X2,X2,X3,X4),X1),k2_enumset1(X2,X2,X3,X4))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36])).
% 0.19/0.49  cnf(c_0_43, plain, (X1=X5|X1=X4|X1=X3|X2!=k2_enumset1(X3,X3,X4,X5)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_37, c_0_14])).
% 0.19/0.49  cnf(c_0_44, negated_conjecture, (k1_setfam_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))!=esk5_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_39]), c_0_40]), c_0_14])).
% 0.19/0.49  cnf(c_0_45, plain, (k1_setfam_1(k2_enumset1(X1,X1,X2,X3))=X3|r2_hidden(esk4_2(k2_enumset1(X1,X1,X2,X3),X3),k2_enumset1(X1,X1,X2,X3))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.19/0.49  cnf(c_0_46, plain, (X1=X2|X1=X3|X1=X4|~r2_hidden(X1,k2_enumset1(X4,X4,X3,X2))), inference(er,[status(thm)],[c_0_43])).
% 0.19/0.49  cnf(c_0_47, negated_conjecture, (r2_hidden(esk4_2(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk5_0),k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.19/0.49  cnf(c_0_48, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.49  cnf(c_0_49, plain, (X2=k1_xboole_0|r1_tarski(X1,k1_setfam_1(X2))|~r1_tarski(X1,esk4_2(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.49  cnf(c_0_50, negated_conjecture, (esk4_2(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk5_0)=esk5_0), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.19/0.49  cnf(c_0_51, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_48])).
% 0.19/0.49  cnf(c_0_52, negated_conjecture, (k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)=k1_xboole_0|r1_tarski(esk5_0,k1_setfam_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51])])).
% 0.19/0.49  cnf(c_0_53, negated_conjecture, (r1_tarski(esk5_0,k1_setfam_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_52]), c_0_36])).
% 0.19/0.49  cnf(c_0_54, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_53]), c_0_44]), ['proof']).
% 0.19/0.49  # SZS output end CNFRefutation
% 0.19/0.49  # Proof object total steps             : 55
% 0.19/0.49  # Proof object clause steps            : 34
% 0.19/0.49  # Proof object formula steps           : 21
% 0.19/0.49  # Proof object conjectures             : 10
% 0.19/0.49  # Proof object clause conjectures      : 7
% 0.19/0.49  # Proof object formula conjectures     : 3
% 0.19/0.49  # Proof object initial clauses used    : 14
% 0.19/0.49  # Proof object initial formulas used   : 10
% 0.19/0.49  # Proof object generating inferences   : 11
% 0.19/0.49  # Proof object simplifying inferences  : 18
% 0.19/0.49  # Training examples: 0 positive, 0 negative
% 0.19/0.49  # Parsed axioms                        : 13
% 0.19/0.49  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.49  # Initial clauses                      : 32
% 0.19/0.49  # Removed in clause preprocessing      : 3
% 0.19/0.49  # Initial clauses in saturation        : 29
% 0.19/0.49  # Processed clauses                    : 458
% 0.19/0.49  # ...of these trivial                  : 8
% 0.19/0.49  # ...subsumed                          : 230
% 0.19/0.49  # ...remaining for further processing  : 220
% 0.19/0.49  # Other redundant clauses eliminated   : 347
% 0.19/0.49  # Clauses deleted for lack of memory   : 0
% 0.19/0.49  # Backward-subsumed                    : 1
% 0.19/0.49  # Backward-rewritten                   : 3
% 0.19/0.49  # Generated clauses                    : 8729
% 0.19/0.49  # ...of the previous two non-trivial   : 8092
% 0.19/0.49  # Contextual simplify-reflections      : 0
% 0.19/0.49  # Paramodulations                      : 8380
% 0.19/0.49  # Factorizations                       : 6
% 0.19/0.49  # Equation resolutions                 : 347
% 0.19/0.49  # Propositional unsat checks           : 0
% 0.19/0.49  #    Propositional check models        : 0
% 0.19/0.49  #    Propositional check unsatisfiable : 0
% 0.19/0.49  #    Propositional clauses             : 0
% 0.19/0.49  #    Propositional clauses after purity: 0
% 0.19/0.49  #    Propositional unsat core size     : 0
% 0.19/0.49  #    Propositional preprocessing time  : 0.000
% 0.19/0.49  #    Propositional encoding time       : 0.000
% 0.19/0.49  #    Propositional solver time         : 0.000
% 0.19/0.49  #    Success case prop preproc time    : 0.000
% 0.19/0.49  #    Success case prop encoding time   : 0.000
% 0.19/0.49  #    Success case prop solver time     : 0.000
% 0.19/0.49  # Current number of processed clauses  : 177
% 0.19/0.49  #    Positive orientable unit clauses  : 17
% 0.19/0.49  #    Positive unorientable unit clauses: 0
% 0.19/0.49  #    Negative unit clauses             : 3
% 0.19/0.49  #    Non-unit-clauses                  : 157
% 0.19/0.49  # Current number of unprocessed clauses: 7684
% 0.19/0.49  # ...number of literals in the above   : 38372
% 0.19/0.49  # Current number of archived formulas  : 0
% 0.19/0.49  # Current number of archived clauses   : 34
% 0.19/0.49  # Clause-clause subsumption calls (NU) : 4047
% 0.19/0.49  # Rec. Clause-clause subsumption calls : 2395
% 0.19/0.49  # Non-unit clause-clause subsumptions  : 206
% 0.19/0.49  # Unit Clause-clause subsumption calls : 314
% 0.19/0.49  # Rewrite failures with RHS unbound    : 0
% 0.19/0.49  # BW rewrite match attempts            : 28
% 0.19/0.49  # BW rewrite match successes           : 2
% 0.19/0.49  # Condensation attempts                : 0
% 0.19/0.49  # Condensation successes               : 0
% 0.19/0.49  # Termbank termtop insertions          : 194867
% 0.19/0.50  
% 0.19/0.50  # -------------------------------------------------
% 0.19/0.50  # User time                : 0.142 s
% 0.19/0.50  # System time              : 0.007 s
% 0.19/0.50  # Total time               : 0.149 s
% 0.19/0.50  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
