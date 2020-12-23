%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:47:09 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 219 expanded)
%              Number of clauses        :   29 (  99 expanded)
%              Number of leaves         :    9 (  58 expanded)
%              Depth                    :    9
%              Number of atoms          :  169 ( 723 expanded)
%              Number of equality atoms :  105 ( 485 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal clause size      :   32 (   2 average)
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

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t11_setfam_1,conjecture,(
    ! [X1] : k1_setfam_1(k1_tarski(X1)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

fof(t65_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,k1_tarski(X2)) = X1
    <=> ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(d1_setfam_1,axiom,(
    ! [X1,X2] :
      ( ( X1 != k1_xboole_0
       => ( X2 = k1_setfam_1(X1)
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ! [X4] :
                  ( r2_hidden(X4,X1)
                 => r2_hidden(X3,X4) ) ) ) )
      & ( X1 = k1_xboole_0
       => ( X2 = k1_setfam_1(X1)
        <=> X2 = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_setfam_1)).

fof(c_0_9,plain,(
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

fof(c_0_10,plain,(
    ! [X34,X35,X36] : k2_enumset1(X34,X34,X35,X36) = k1_enumset1(X34,X35,X36) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_11,plain,(
    ! [X12,X13] :
      ( ( r1_tarski(X12,X13)
        | X12 != X13 )
      & ( r1_tarski(X13,X12)
        | X12 != X13 )
      & ( ~ r1_tarski(X12,X13)
        | ~ r1_tarski(X13,X12)
        | X12 = X13 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1] : k1_setfam_1(k1_tarski(X1)) = X1 ),
    inference(assume_negation,[status(cth)],[t11_setfam_1])).

cnf(c_0_13,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X2,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_15,plain,(
    ! [X44,X45] :
      ( ( k4_xboole_0(X44,k1_tarski(X45)) != X44
        | ~ r2_hidden(X45,X44) )
      & ( r2_hidden(X45,X44)
        | k4_xboole_0(X44,k1_tarski(X45)) = X44 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).

fof(c_0_16,plain,(
    ! [X31] : k2_tarski(X31,X31) = k1_tarski(X31) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_17,plain,(
    ! [X32,X33] : k1_enumset1(X32,X32,X33) = k2_tarski(X32,X33) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_18,plain,(
    ! [X14,X15] :
      ( ( k4_xboole_0(X14,X15) != k1_xboole_0
        | r1_tarski(X14,X15) )
      & ( ~ r1_tarski(X14,X15)
        | k4_xboole_0(X14,X15) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_19,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X2,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_21,negated_conjecture,(
    k1_setfam_1(k1_tarski(esk6_0)) != esk6_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

fof(c_0_22,plain,(
    ! [X46,X47,X48,X49,X50,X52,X55,X56,X57,X58] :
      ( ( ~ r2_hidden(X48,X47)
        | ~ r2_hidden(X49,X46)
        | r2_hidden(X48,X49)
        | X47 != k1_setfam_1(X46)
        | X46 = k1_xboole_0 )
      & ( r2_hidden(esk3_3(X46,X47,X50),X46)
        | r2_hidden(X50,X47)
        | X47 != k1_setfam_1(X46)
        | X46 = k1_xboole_0 )
      & ( ~ r2_hidden(X50,esk3_3(X46,X47,X50))
        | r2_hidden(X50,X47)
        | X47 != k1_setfam_1(X46)
        | X46 = k1_xboole_0 )
      & ( r2_hidden(esk5_2(X46,X52),X46)
        | ~ r2_hidden(esk4_2(X46,X52),X52)
        | X52 = k1_setfam_1(X46)
        | X46 = k1_xboole_0 )
      & ( ~ r2_hidden(esk4_2(X46,X52),esk5_2(X46,X52))
        | ~ r2_hidden(esk4_2(X46,X52),X52)
        | X52 = k1_setfam_1(X46)
        | X46 = k1_xboole_0 )
      & ( r2_hidden(esk4_2(X46,X52),X52)
        | ~ r2_hidden(X55,X46)
        | r2_hidden(esk4_2(X46,X52),X55)
        | X52 = k1_setfam_1(X46)
        | X46 = k1_xboole_0 )
      & ( X57 != k1_setfam_1(X56)
        | X57 = k1_xboole_0
        | X56 != k1_xboole_0 )
      & ( X58 != k1_xboole_0
        | X58 = k1_setfam_1(X56)
        | X56 != k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_setfam_1])])])])])])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X2,X2,X4,X5) ),
    inference(rw,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_24,plain,
    ( k4_xboole_0(X1,k1_tarski(X2)) != X1
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_19])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X4,X4,X2,X5) ),
    inference(rw,[status(thm)],[c_0_20,c_0_14])).

cnf(c_0_30,negated_conjecture,
    ( k1_setfam_1(k1_tarski(esk6_0)) != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( r2_hidden(esk4_2(X1,X2),X2)
    | r2_hidden(esk4_2(X1,X2),X3)
    | X2 = k1_setfam_1(X1)
    | X1 = k1_xboole_0
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,k2_enumset1(X1,X1,X2,X3)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_23])])).

cnf(c_0_33,plain,
    ( k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)) != X1
    | ~ r2_hidden(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_25]),c_0_26]),c_0_14])).

cnf(c_0_34,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,k2_enumset1(X2,X2,X1,X3)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_29])])).

cnf(c_0_36,plain,
    ( X1 = X3
    | X1 = X4
    | X1 = X5
    | ~ r2_hidden(X1,X2)
    | X2 != k1_enumset1(X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_37,negated_conjecture,
    ( k1_setfam_1(k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)) != esk6_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_25]),c_0_26]),c_0_14])).

cnf(c_0_38,plain,
    ( X1 = k1_setfam_1(k2_enumset1(X2,X2,X3,X4))
    | k2_enumset1(X2,X2,X3,X4) = k1_xboole_0
    | r2_hidden(esk4_2(k2_enumset1(X2,X2,X3,X4),X1),X1)
    | r2_hidden(esk4_2(k2_enumset1(X2,X2,X3,X4),X1),X2) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_39,plain,
    ( k2_enumset1(X1,X1,X1,X1) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])])).

cnf(c_0_40,plain,
    ( X1 = X5
    | X1 = X4
    | X1 = X3
    | X2 != k2_enumset1(X3,X3,X4,X5)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_36,c_0_14])).

cnf(c_0_41,plain,
    ( r2_hidden(esk5_2(X1,X2),X1)
    | X2 = k1_setfam_1(X1)
    | X1 = k1_xboole_0
    | ~ r2_hidden(esk4_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk4_2(k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk6_0),esk6_0) ),
    inference(er,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])])).

cnf(c_0_43,plain,
    ( X1 = X2
    | X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,k2_enumset1(X4,X4,X3,X2)) ),
    inference(er,[status(thm)],[c_0_40])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk5_2(k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk6_0),k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_37]),c_0_39])).

cnf(c_0_45,plain,
    ( X2 = k1_setfam_1(X1)
    | X1 = k1_xboole_0
    | ~ r2_hidden(esk4_2(X1,X2),esk5_2(X1,X2))
    | ~ r2_hidden(esk4_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_46,negated_conjecture,
    ( esk5_2(k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk6_0) = esk6_0 ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_47,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_42])]),c_0_37]),c_0_39]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.15/0.35  % Computer   : n015.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 16:22:08 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  # Version: 2.5pre002
% 0.15/0.35  # No SInE strategy applied
% 0.15/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.58  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.21/0.58  # and selection function SelectNegativeLiterals.
% 0.21/0.58  #
% 0.21/0.58  # Preprocessing time       : 0.030 s
% 0.21/0.58  # Presaturation interreduction done
% 0.21/0.58  
% 0.21/0.58  # Proof found!
% 0.21/0.58  # SZS status Theorem
% 0.21/0.58  # SZS output start CNFRefutation
% 0.21/0.58  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 0.21/0.58  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.21/0.58  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.21/0.58  fof(t11_setfam_1, conjecture, ![X1]:k1_setfam_1(k1_tarski(X1))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_setfam_1)).
% 0.21/0.58  fof(t65_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(X1,k1_tarski(X2))=X1<=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 0.21/0.58  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.21/0.58  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.21/0.58  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.21/0.58  fof(d1_setfam_1, axiom, ![X1, X2]:((X1!=k1_xboole_0=>(X2=k1_setfam_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>![X4]:(r2_hidden(X4,X1)=>r2_hidden(X3,X4)))))&(X1=k1_xboole_0=>(X2=k1_setfam_1(X1)<=>X2=k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_setfam_1)).
% 0.21/0.58  fof(c_0_9, plain, ![X20, X21, X22, X23, X24, X25, X26, X27, X28, X29]:(((~r2_hidden(X24,X23)|(X24=X20|X24=X21|X24=X22)|X23!=k1_enumset1(X20,X21,X22))&(((X25!=X20|r2_hidden(X25,X23)|X23!=k1_enumset1(X20,X21,X22))&(X25!=X21|r2_hidden(X25,X23)|X23!=k1_enumset1(X20,X21,X22)))&(X25!=X22|r2_hidden(X25,X23)|X23!=k1_enumset1(X20,X21,X22))))&((((esk2_4(X26,X27,X28,X29)!=X26|~r2_hidden(esk2_4(X26,X27,X28,X29),X29)|X29=k1_enumset1(X26,X27,X28))&(esk2_4(X26,X27,X28,X29)!=X27|~r2_hidden(esk2_4(X26,X27,X28,X29),X29)|X29=k1_enumset1(X26,X27,X28)))&(esk2_4(X26,X27,X28,X29)!=X28|~r2_hidden(esk2_4(X26,X27,X28,X29),X29)|X29=k1_enumset1(X26,X27,X28)))&(r2_hidden(esk2_4(X26,X27,X28,X29),X29)|(esk2_4(X26,X27,X28,X29)=X26|esk2_4(X26,X27,X28,X29)=X27|esk2_4(X26,X27,X28,X29)=X28)|X29=k1_enumset1(X26,X27,X28)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 0.21/0.58  fof(c_0_10, plain, ![X34, X35, X36]:k2_enumset1(X34,X34,X35,X36)=k1_enumset1(X34,X35,X36), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.21/0.58  fof(c_0_11, plain, ![X12, X13]:(((r1_tarski(X12,X13)|X12!=X13)&(r1_tarski(X13,X12)|X12!=X13))&(~r1_tarski(X12,X13)|~r1_tarski(X13,X12)|X12=X13)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.21/0.58  fof(c_0_12, negated_conjecture, ~(![X1]:k1_setfam_1(k1_tarski(X1))=X1), inference(assume_negation,[status(cth)],[t11_setfam_1])).
% 0.21/0.58  cnf(c_0_13, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X2,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.21/0.58  cnf(c_0_14, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.58  fof(c_0_15, plain, ![X44, X45]:((k4_xboole_0(X44,k1_tarski(X45))!=X44|~r2_hidden(X45,X44))&(r2_hidden(X45,X44)|k4_xboole_0(X44,k1_tarski(X45))=X44)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).
% 0.21/0.58  fof(c_0_16, plain, ![X31]:k2_tarski(X31,X31)=k1_tarski(X31), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.21/0.58  fof(c_0_17, plain, ![X32, X33]:k1_enumset1(X32,X32,X33)=k2_tarski(X32,X33), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.21/0.58  fof(c_0_18, plain, ![X14, X15]:((k4_xboole_0(X14,X15)!=k1_xboole_0|r1_tarski(X14,X15))&(~r1_tarski(X14,X15)|k4_xboole_0(X14,X15)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.21/0.58  cnf(c_0_19, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.58  cnf(c_0_20, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X2,X5)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.21/0.58  fof(c_0_21, negated_conjecture, k1_setfam_1(k1_tarski(esk6_0))!=esk6_0, inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 0.21/0.58  fof(c_0_22, plain, ![X46, X47, X48, X49, X50, X52, X55, X56, X57, X58]:((((~r2_hidden(X48,X47)|(~r2_hidden(X49,X46)|r2_hidden(X48,X49))|X47!=k1_setfam_1(X46)|X46=k1_xboole_0)&((r2_hidden(esk3_3(X46,X47,X50),X46)|r2_hidden(X50,X47)|X47!=k1_setfam_1(X46)|X46=k1_xboole_0)&(~r2_hidden(X50,esk3_3(X46,X47,X50))|r2_hidden(X50,X47)|X47!=k1_setfam_1(X46)|X46=k1_xboole_0)))&(((r2_hidden(esk5_2(X46,X52),X46)|~r2_hidden(esk4_2(X46,X52),X52)|X52=k1_setfam_1(X46)|X46=k1_xboole_0)&(~r2_hidden(esk4_2(X46,X52),esk5_2(X46,X52))|~r2_hidden(esk4_2(X46,X52),X52)|X52=k1_setfam_1(X46)|X46=k1_xboole_0))&(r2_hidden(esk4_2(X46,X52),X52)|(~r2_hidden(X55,X46)|r2_hidden(esk4_2(X46,X52),X55))|X52=k1_setfam_1(X46)|X46=k1_xboole_0)))&((X57!=k1_setfam_1(X56)|X57=k1_xboole_0|X56!=k1_xboole_0)&(X58!=k1_xboole_0|X58=k1_setfam_1(X56)|X56!=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_setfam_1])])])])])])).
% 0.21/0.58  cnf(c_0_23, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X2,X2,X4,X5)), inference(rw,[status(thm)],[c_0_13, c_0_14])).
% 0.21/0.58  cnf(c_0_24, plain, (k4_xboole_0(X1,k1_tarski(X2))!=X1|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.58  cnf(c_0_25, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.58  cnf(c_0_26, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.58  cnf(c_0_27, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.58  cnf(c_0_28, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_19])).
% 0.21/0.58  cnf(c_0_29, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X4,X4,X2,X5)), inference(rw,[status(thm)],[c_0_20, c_0_14])).
% 0.21/0.58  cnf(c_0_30, negated_conjecture, (k1_setfam_1(k1_tarski(esk6_0))!=esk6_0), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.58  cnf(c_0_31, plain, (r2_hidden(esk4_2(X1,X2),X2)|r2_hidden(esk4_2(X1,X2),X3)|X2=k1_setfam_1(X1)|X1=k1_xboole_0|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.58  cnf(c_0_32, plain, (r2_hidden(X1,k2_enumset1(X1,X1,X2,X3))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_23])])).
% 0.21/0.58  cnf(c_0_33, plain, (k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))!=X1|~r2_hidden(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_25]), c_0_26]), c_0_14])).
% 0.21/0.58  cnf(c_0_34, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.21/0.58  cnf(c_0_35, plain, (r2_hidden(X1,k2_enumset1(X2,X2,X1,X3))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_29])])).
% 0.21/0.58  cnf(c_0_36, plain, (X1=X3|X1=X4|X1=X5|~r2_hidden(X1,X2)|X2!=k1_enumset1(X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.21/0.58  cnf(c_0_37, negated_conjecture, (k1_setfam_1(k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0))!=esk6_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_25]), c_0_26]), c_0_14])).
% 0.21/0.58  cnf(c_0_38, plain, (X1=k1_setfam_1(k2_enumset1(X2,X2,X3,X4))|k2_enumset1(X2,X2,X3,X4)=k1_xboole_0|r2_hidden(esk4_2(k2_enumset1(X2,X2,X3,X4),X1),X1)|r2_hidden(esk4_2(k2_enumset1(X2,X2,X3,X4),X1),X2)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.21/0.58  cnf(c_0_39, plain, (k2_enumset1(X1,X1,X1,X1)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35])])).
% 0.21/0.58  cnf(c_0_40, plain, (X1=X5|X1=X4|X1=X3|X2!=k2_enumset1(X3,X3,X4,X5)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_36, c_0_14])).
% 0.21/0.58  cnf(c_0_41, plain, (r2_hidden(esk5_2(X1,X2),X1)|X2=k1_setfam_1(X1)|X1=k1_xboole_0|~r2_hidden(esk4_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.58  cnf(c_0_42, negated_conjecture, (r2_hidden(esk4_2(k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk6_0),esk6_0)), inference(er,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39])])).
% 0.21/0.58  cnf(c_0_43, plain, (X1=X2|X1=X3|X1=X4|~r2_hidden(X1,k2_enumset1(X4,X4,X3,X2))), inference(er,[status(thm)],[c_0_40])).
% 0.21/0.58  cnf(c_0_44, negated_conjecture, (r2_hidden(esk5_2(k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk6_0),k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_37]), c_0_39])).
% 0.21/0.58  cnf(c_0_45, plain, (X2=k1_setfam_1(X1)|X1=k1_xboole_0|~r2_hidden(esk4_2(X1,X2),esk5_2(X1,X2))|~r2_hidden(esk4_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.58  cnf(c_0_46, negated_conjecture, (esk5_2(k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk6_0)=esk6_0), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.21/0.58  cnf(c_0_47, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_42])]), c_0_37]), c_0_39]), ['proof']).
% 0.21/0.58  # SZS output end CNFRefutation
% 0.21/0.58  # Proof object total steps             : 48
% 0.21/0.58  # Proof object clause steps            : 29
% 0.21/0.58  # Proof object formula steps           : 19
% 0.21/0.58  # Proof object conjectures             : 9
% 0.21/0.58  # Proof object clause conjectures      : 6
% 0.21/0.58  # Proof object formula conjectures     : 3
% 0.21/0.58  # Proof object initial clauses used    : 13
% 0.21/0.58  # Proof object initial formulas used   : 9
% 0.21/0.58  # Proof object generating inferences   : 7
% 0.21/0.58  # Proof object simplifying inferences  : 25
% 0.21/0.58  # Training examples: 0 positive, 0 negative
% 0.21/0.58  # Parsed axioms                        : 15
% 0.21/0.58  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.58  # Initial clauses                      : 39
% 0.21/0.58  # Removed in clause preprocessing      : 3
% 0.21/0.58  # Initial clauses in saturation        : 36
% 0.21/0.58  # Processed clauses                    : 950
% 0.21/0.58  # ...of these trivial                  : 18
% 0.21/0.58  # ...subsumed                          : 644
% 0.21/0.58  # ...remaining for further processing  : 288
% 0.21/0.58  # Other redundant clauses eliminated   : 610
% 0.21/0.58  # Clauses deleted for lack of memory   : 0
% 0.21/0.58  # Backward-subsumed                    : 15
% 0.21/0.58  # Backward-rewritten                   : 19
% 0.21/0.58  # Generated clauses                    : 20313
% 0.21/0.58  # ...of the previous two non-trivial   : 16775
% 0.21/0.58  # Contextual simplify-reflections      : 1
% 0.21/0.58  # Paramodulations                      : 19702
% 0.21/0.58  # Factorizations                       : 6
% 0.21/0.58  # Equation resolutions                 : 610
% 0.21/0.58  # Propositional unsat checks           : 0
% 0.21/0.58  #    Propositional check models        : 0
% 0.21/0.58  #    Propositional check unsatisfiable : 0
% 0.21/0.58  #    Propositional clauses             : 0
% 0.21/0.58  #    Propositional clauses after purity: 0
% 0.21/0.58  #    Propositional unsat core size     : 0
% 0.21/0.58  #    Propositional preprocessing time  : 0.000
% 0.21/0.58  #    Propositional encoding time       : 0.000
% 0.21/0.58  #    Propositional solver time         : 0.000
% 0.21/0.58  #    Success case prop preproc time    : 0.000
% 0.21/0.58  #    Success case prop encoding time   : 0.000
% 0.21/0.58  #    Success case prop solver time     : 0.000
% 0.21/0.58  # Current number of processed clauses  : 207
% 0.21/0.58  #    Positive orientable unit clauses  : 29
% 0.21/0.58  #    Positive unorientable unit clauses: 0
% 0.21/0.58  #    Negative unit clauses             : 4
% 0.21/0.58  #    Non-unit-clauses                  : 174
% 0.21/0.58  # Current number of unprocessed clauses: 15770
% 0.21/0.58  # ...number of literals in the above   : 60241
% 0.21/0.58  # Current number of archived formulas  : 0
% 0.21/0.58  # Current number of archived clauses   : 71
% 0.21/0.58  # Clause-clause subsumption calls (NU) : 7250
% 0.21/0.58  # Rec. Clause-clause subsumption calls : 4139
% 0.21/0.58  # Non-unit clause-clause subsumptions  : 613
% 0.21/0.58  # Unit Clause-clause subsumption calls : 261
% 0.21/0.58  # Rewrite failures with RHS unbound    : 0
% 0.21/0.58  # BW rewrite match attempts            : 26
% 0.21/0.58  # BW rewrite match successes           : 9
% 0.21/0.58  # Condensation attempts                : 0
% 0.21/0.58  # Condensation successes               : 0
% 0.21/0.58  # Termbank termtop insertions          : 366894
% 0.21/0.58  
% 0.21/0.58  # -------------------------------------------------
% 0.21/0.58  # User time                : 0.213 s
% 0.21/0.58  # System time              : 0.018 s
% 0.21/0.58  # Total time               : 0.230 s
% 0.21/0.58  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
