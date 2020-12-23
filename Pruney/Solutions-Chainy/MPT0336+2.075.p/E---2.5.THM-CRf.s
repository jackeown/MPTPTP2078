%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:44:58 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 127 expanded)
%              Number of clauses        :   39 (  56 expanded)
%              Number of leaves         :   14 (  33 expanded)
%              Depth                    :   15
%              Number of atoms          :  126 ( 242 expanded)
%              Number of equality atoms :   29 (  64 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t149_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))
        & r2_hidden(X4,X3)
        & r1_xboole_0(X3,X2) )
     => r1_xboole_0(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).

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

fof(l27_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( ~ r2_hidden(X1,X2)
     => r1_xboole_0(k1_tarski(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t85_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_xboole_0(X1,k4_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t70_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ~ ( ~ r1_xboole_0(X1,k2_xboole_0(X2,X3))
          & r1_xboole_0(X1,X2)
          & r1_xboole_0(X1,X3) )
      & ~ ( ~ ( r1_xboole_0(X1,X2)
              & r1_xboole_0(X1,X3) )
          & r1_xboole_0(X1,k2_xboole_0(X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))
          & r2_hidden(X4,X3)
          & r1_xboole_0(X3,X2) )
       => r1_xboole_0(k2_xboole_0(X1,X3),X2) ) ),
    inference(assume_negation,[status(cth)],[t149_zfmisc_1])).

fof(c_0_15,plain,(
    ! [X9,X10,X12,X13,X14] :
      ( ( r2_hidden(esk1_2(X9,X10),X9)
        | r1_xboole_0(X9,X10) )
      & ( r2_hidden(esk1_2(X9,X10),X10)
        | r1_xboole_0(X9,X10) )
      & ( ~ r2_hidden(X14,X12)
        | ~ r2_hidden(X14,X13)
        | ~ r1_xboole_0(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_16,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk2_0,esk3_0),k1_tarski(esk5_0))
    & r2_hidden(esk5_0,esk4_0)
    & r1_xboole_0(esk4_0,esk3_0)
    & ~ r1_xboole_0(k2_xboole_0(esk2_0,esk4_0),esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

fof(c_0_17,plain,(
    ! [X46,X47] :
      ( r2_hidden(X46,X47)
      | r1_xboole_0(k1_tarski(X46),X47) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l27_zfmisc_1])])])).

fof(c_0_18,plain,(
    ! [X40] : k2_tarski(X40,X40) = k1_tarski(X40) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_19,plain,(
    ! [X41,X42] : k1_enumset1(X41,X41,X42) = k2_tarski(X41,X42) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_20,plain,(
    ! [X43,X44,X45] : k2_enumset1(X43,X43,X44,X45) = k1_enumset1(X43,X44,X45) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

cnf(c_0_21,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(k1_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_27,plain,(
    ! [X7,X8] :
      ( ~ r1_xboole_0(X7,X8)
      | r1_xboole_0(X8,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

fof(c_0_28,plain,(
    ! [X22,X23] : k4_xboole_0(X22,k4_xboole_0(X22,X23)) = k3_xboole_0(X22,X23) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_29,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_30,negated_conjecture,
    ( ~ r2_hidden(esk5_0,X1)
    | ~ r1_xboole_0(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(k2_enumset1(X1,X1,X1,X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_24]),c_0_25]),c_0_26])).

cnf(c_0_32,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk2_0,esk3_0),k1_tarski(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_35,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,negated_conjecture,
    ( r1_xboole_0(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),X1)
    | ~ r1_xboole_0(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

fof(c_0_39,plain,(
    ! [X34,X35,X36] :
      ( ~ r1_tarski(X34,X35)
      | r1_xboole_0(X34,k4_xboole_0(X36,X35)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t85_xboole_1])])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0)),k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_24]),c_0_25]),c_0_26]),c_0_35])).

cnf(c_0_41,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_35]),c_0_35])).

fof(c_0_42,plain,(
    ! [X32,X33] :
      ( ( ~ r1_xboole_0(X32,X33)
        | k4_xboole_0(X32,X33) = X32 )
      & ( k4_xboole_0(X32,X33) != X32
        | r1_xboole_0(X32,X33) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

cnf(c_0_43,negated_conjecture,
    ( r1_xboole_0(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_44,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk2_0)),k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(rw,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_46,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_47,negated_conjecture,
    ( r1_xboole_0(esk3_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_43])).

cnf(c_0_48,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk2_0)),k4_xboole_0(X1,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_49,negated_conjecture,
    ( k4_xboole_0(esk3_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

fof(c_0_50,plain,(
    ! [X18,X19] :
      ( ~ r1_tarski(X18,X19)
      | k3_xboole_0(X18,X19) = X18 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_51,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk2_0)),esk3_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_52,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

fof(c_0_53,plain,(
    ! [X20,X21] : r1_tarski(k4_xboole_0(X20,X21),X20) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_54,negated_conjecture,
    ( r1_xboole_0(esk3_0,k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_32,c_0_51])).

cnf(c_0_55,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_52,c_0_35])).

cnf(c_0_56,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

fof(c_0_57,plain,(
    ! [X24,X25,X26] :
      ( ( r1_xboole_0(X24,k2_xboole_0(X25,X26))
        | ~ r1_xboole_0(X24,X25)
        | ~ r1_xboole_0(X24,X26) )
      & ( r1_xboole_0(X24,X25)
        | ~ r1_xboole_0(X24,k2_xboole_0(X25,X26)) )
      & ( r1_xboole_0(X24,X26)
        | ~ r1_xboole_0(X24,k2_xboole_0(X25,X26)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).

cnf(c_0_58,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk2_0))) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_46,c_0_54])).

cnf(c_0_59,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_41])).

cnf(c_0_60,plain,
    ( r1_xboole_0(X1,k2_xboole_0(X2,X3))
    | ~ r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_61,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_62,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk2_0) = esk3_0 ),
    inference(rw,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_63,negated_conjecture,
    ( r1_xboole_0(esk3_0,k2_xboole_0(X1,esk4_0))
    | ~ r1_xboole_0(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_60,c_0_38])).

cnf(c_0_64,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_65,negated_conjecture,
    ( r1_xboole_0(esk3_0,k2_xboole_0(esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_66,negated_conjecture,
    ( ~ r1_xboole_0(k2_xboole_0(esk2_0,esk4_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_67,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_65]),c_0_66]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:28:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.45  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S03EI
% 0.21/0.45  # and selection function SelectLComplex.
% 0.21/0.45  #
% 0.21/0.45  # Preprocessing time       : 0.027 s
% 0.21/0.45  # Presaturation interreduction done
% 0.21/0.45  
% 0.21/0.45  # Proof found!
% 0.21/0.45  # SZS status Theorem
% 0.21/0.45  # SZS output start CNFRefutation
% 0.21/0.45  fof(t149_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(((r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))&r2_hidden(X4,X3))&r1_xboole_0(X3,X2))=>r1_xboole_0(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 0.21/0.45  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.21/0.45  fof(l27_zfmisc_1, axiom, ![X1, X2]:(~(r2_hidden(X1,X2))=>r1_xboole_0(k1_tarski(X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 0.21/0.45  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.21/0.45  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.21/0.45  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.21/0.45  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.21/0.45  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.21/0.45  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.21/0.45  fof(t85_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_xboole_0(X1,k4_xboole_0(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_xboole_1)).
% 0.21/0.45  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.21/0.45  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.21/0.45  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.21/0.45  fof(t70_xboole_1, axiom, ![X1, X2, X3]:(~(((~(r1_xboole_0(X1,k2_xboole_0(X2,X3)))&r1_xboole_0(X1,X2))&r1_xboole_0(X1,X3)))&~((~((r1_xboole_0(X1,X2)&r1_xboole_0(X1,X3)))&r1_xboole_0(X1,k2_xboole_0(X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 0.21/0.45  fof(c_0_14, negated_conjecture, ~(![X1, X2, X3, X4]:(((r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))&r2_hidden(X4,X3))&r1_xboole_0(X3,X2))=>r1_xboole_0(k2_xboole_0(X1,X3),X2))), inference(assume_negation,[status(cth)],[t149_zfmisc_1])).
% 0.21/0.45  fof(c_0_15, plain, ![X9, X10, X12, X13, X14]:(((r2_hidden(esk1_2(X9,X10),X9)|r1_xboole_0(X9,X10))&(r2_hidden(esk1_2(X9,X10),X10)|r1_xboole_0(X9,X10)))&(~r2_hidden(X14,X12)|~r2_hidden(X14,X13)|~r1_xboole_0(X12,X13))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.21/0.45  fof(c_0_16, negated_conjecture, (((r1_tarski(k3_xboole_0(esk2_0,esk3_0),k1_tarski(esk5_0))&r2_hidden(esk5_0,esk4_0))&r1_xboole_0(esk4_0,esk3_0))&~r1_xboole_0(k2_xboole_0(esk2_0,esk4_0),esk3_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.21/0.45  fof(c_0_17, plain, ![X46, X47]:(r2_hidden(X46,X47)|r1_xboole_0(k1_tarski(X46),X47)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l27_zfmisc_1])])])).
% 0.21/0.45  fof(c_0_18, plain, ![X40]:k2_tarski(X40,X40)=k1_tarski(X40), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.21/0.45  fof(c_0_19, plain, ![X41, X42]:k1_enumset1(X41,X41,X42)=k2_tarski(X41,X42), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.21/0.45  fof(c_0_20, plain, ![X43, X44, X45]:k2_enumset1(X43,X43,X44,X45)=k1_enumset1(X43,X44,X45), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.21/0.45  cnf(c_0_21, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.45  cnf(c_0_22, negated_conjecture, (r2_hidden(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.45  cnf(c_0_23, plain, (r2_hidden(X1,X2)|r1_xboole_0(k1_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.45  cnf(c_0_24, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.45  cnf(c_0_25, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.45  cnf(c_0_26, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.45  fof(c_0_27, plain, ![X7, X8]:(~r1_xboole_0(X7,X8)|r1_xboole_0(X8,X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.21/0.45  fof(c_0_28, plain, ![X22, X23]:k4_xboole_0(X22,k4_xboole_0(X22,X23))=k3_xboole_0(X22,X23), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.21/0.45  fof(c_0_29, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.21/0.45  cnf(c_0_30, negated_conjecture, (~r2_hidden(esk5_0,X1)|~r1_xboole_0(X1,esk4_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.21/0.45  cnf(c_0_31, plain, (r2_hidden(X1,X2)|r1_xboole_0(k2_enumset1(X1,X1,X1,X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_24]), c_0_25]), c_0_26])).
% 0.21/0.45  cnf(c_0_32, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.21/0.45  cnf(c_0_33, negated_conjecture, (r1_xboole_0(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.45  cnf(c_0_34, negated_conjecture, (r1_tarski(k3_xboole_0(esk2_0,esk3_0),k1_tarski(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.45  cnf(c_0_35, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.21/0.45  cnf(c_0_36, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.21/0.45  cnf(c_0_37, negated_conjecture, (r1_xboole_0(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),X1)|~r1_xboole_0(X1,esk4_0)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.21/0.45  cnf(c_0_38, negated_conjecture, (r1_xboole_0(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.21/0.45  fof(c_0_39, plain, ![X34, X35, X36]:(~r1_tarski(X34,X35)|r1_xboole_0(X34,k4_xboole_0(X36,X35))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t85_xboole_1])])).
% 0.21/0.45  cnf(c_0_40, negated_conjecture, (r1_tarski(k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0)),k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_24]), c_0_25]), c_0_26]), c_0_35])).
% 0.21/0.45  cnf(c_0_41, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_35]), c_0_35])).
% 0.21/0.45  fof(c_0_42, plain, ![X32, X33]:((~r1_xboole_0(X32,X33)|k4_xboole_0(X32,X33)=X32)&(k4_xboole_0(X32,X33)!=X32|r1_xboole_0(X32,X33))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.21/0.45  cnf(c_0_43, negated_conjecture, (r1_xboole_0(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk3_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.21/0.45  cnf(c_0_44, plain, (r1_xboole_0(X1,k4_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.21/0.45  cnf(c_0_45, negated_conjecture, (r1_tarski(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk2_0)),k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))), inference(rw,[status(thm)],[c_0_40, c_0_41])).
% 0.21/0.45  cnf(c_0_46, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.21/0.45  cnf(c_0_47, negated_conjecture, (r1_xboole_0(esk3_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))), inference(spm,[status(thm)],[c_0_32, c_0_43])).
% 0.21/0.45  cnf(c_0_48, negated_conjecture, (r1_xboole_0(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk2_0)),k4_xboole_0(X1,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.21/0.45  cnf(c_0_49, negated_conjecture, (k4_xboole_0(esk3_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))=esk3_0), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.21/0.45  fof(c_0_50, plain, ![X18, X19]:(~r1_tarski(X18,X19)|k3_xboole_0(X18,X19)=X18), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.21/0.45  cnf(c_0_51, negated_conjecture, (r1_xboole_0(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk2_0)),esk3_0)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.21/0.45  cnf(c_0_52, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.21/0.45  fof(c_0_53, plain, ![X20, X21]:r1_tarski(k4_xboole_0(X20,X21),X20), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.21/0.45  cnf(c_0_54, negated_conjecture, (r1_xboole_0(esk3_0,k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk2_0)))), inference(spm,[status(thm)],[c_0_32, c_0_51])).
% 0.21/0.45  cnf(c_0_55, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=X1|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_52, c_0_35])).
% 0.21/0.45  cnf(c_0_56, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.21/0.45  fof(c_0_57, plain, ![X24, X25, X26]:((r1_xboole_0(X24,k2_xboole_0(X25,X26))|~r1_xboole_0(X24,X25)|~r1_xboole_0(X24,X26))&((r1_xboole_0(X24,X25)|~r1_xboole_0(X24,k2_xboole_0(X25,X26)))&(r1_xboole_0(X24,X26)|~r1_xboole_0(X24,k2_xboole_0(X25,X26))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).
% 0.21/0.45  cnf(c_0_58, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk2_0)))=esk3_0), inference(spm,[status(thm)],[c_0_46, c_0_54])).
% 0.21/0.45  cnf(c_0_59, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_41])).
% 0.21/0.45  cnf(c_0_60, plain, (r1_xboole_0(X1,k2_xboole_0(X2,X3))|~r1_xboole_0(X1,X2)|~r1_xboole_0(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.21/0.45  cnf(c_0_61, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.21/0.45  cnf(c_0_62, negated_conjecture, (k4_xboole_0(esk3_0,esk2_0)=esk3_0), inference(rw,[status(thm)],[c_0_58, c_0_59])).
% 0.21/0.45  cnf(c_0_63, negated_conjecture, (r1_xboole_0(esk3_0,k2_xboole_0(X1,esk4_0))|~r1_xboole_0(esk3_0,X1)), inference(spm,[status(thm)],[c_0_60, c_0_38])).
% 0.21/0.45  cnf(c_0_64, negated_conjecture, (r1_xboole_0(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.21/0.45  cnf(c_0_65, negated_conjecture, (r1_xboole_0(esk3_0,k2_xboole_0(esk2_0,esk4_0))), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.21/0.45  cnf(c_0_66, negated_conjecture, (~r1_xboole_0(k2_xboole_0(esk2_0,esk4_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.45  cnf(c_0_67, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_65]), c_0_66]), ['proof']).
% 0.21/0.45  # SZS output end CNFRefutation
% 0.21/0.45  # Proof object total steps             : 68
% 0.21/0.45  # Proof object clause steps            : 39
% 0.21/0.45  # Proof object formula steps           : 29
% 0.21/0.45  # Proof object conjectures             : 24
% 0.21/0.45  # Proof object clause conjectures      : 21
% 0.21/0.45  # Proof object formula conjectures     : 3
% 0.21/0.45  # Proof object initial clauses used    : 18
% 0.21/0.45  # Proof object initial formulas used   : 14
% 0.21/0.45  # Proof object generating inferences   : 15
% 0.21/0.45  # Proof object simplifying inferences  : 14
% 0.21/0.45  # Training examples: 0 positive, 0 negative
% 0.21/0.45  # Parsed axioms                        : 18
% 0.21/0.45  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.45  # Initial clauses                      : 26
% 0.21/0.45  # Removed in clause preprocessing      : 4
% 0.21/0.45  # Initial clauses in saturation        : 22
% 0.21/0.45  # Processed clauses                    : 448
% 0.21/0.45  # ...of these trivial                  : 71
% 0.21/0.45  # ...subsumed                          : 144
% 0.21/0.45  # ...remaining for further processing  : 233
% 0.21/0.45  # Other redundant clauses eliminated   : 18
% 0.21/0.45  # Clauses deleted for lack of memory   : 0
% 0.21/0.45  # Backward-subsumed                    : 6
% 0.21/0.45  # Backward-rewritten                   : 44
% 0.21/0.45  # Generated clauses                    : 4509
% 0.21/0.45  # ...of the previous two non-trivial   : 2747
% 0.21/0.45  # Contextual simplify-reflections      : 0
% 0.21/0.45  # Paramodulations                      : 4491
% 0.21/0.45  # Factorizations                       : 0
% 0.21/0.45  # Equation resolutions                 : 18
% 0.21/0.45  # Propositional unsat checks           : 0
% 0.21/0.45  #    Propositional check models        : 0
% 0.21/0.45  #    Propositional check unsatisfiable : 0
% 0.21/0.45  #    Propositional clauses             : 0
% 0.21/0.45  #    Propositional clauses after purity: 0
% 0.21/0.45  #    Propositional unsat core size     : 0
% 0.21/0.45  #    Propositional preprocessing time  : 0.000
% 0.21/0.45  #    Propositional encoding time       : 0.000
% 0.21/0.45  #    Propositional solver time         : 0.000
% 0.21/0.45  #    Success case prop preproc time    : 0.000
% 0.21/0.45  #    Success case prop encoding time   : 0.000
% 0.21/0.45  #    Success case prop solver time     : 0.000
% 0.21/0.45  # Current number of processed clauses  : 161
% 0.21/0.45  #    Positive orientable unit clauses  : 107
% 0.21/0.45  #    Positive unorientable unit clauses: 5
% 0.21/0.45  #    Negative unit clauses             : 3
% 0.21/0.45  #    Non-unit-clauses                  : 46
% 0.21/0.45  # Current number of unprocessed clauses: 2300
% 0.21/0.45  # ...number of literals in the above   : 2845
% 0.21/0.45  # Current number of archived formulas  : 0
% 0.21/0.45  # Current number of archived clauses   : 76
% 0.21/0.45  # Clause-clause subsumption calls (NU) : 423
% 0.21/0.45  # Rec. Clause-clause subsumption calls : 416
% 0.21/0.45  # Non-unit clause-clause subsumptions  : 81
% 0.21/0.45  # Unit Clause-clause subsumption calls : 100
% 0.21/0.45  # Rewrite failures with RHS unbound    : 201
% 0.21/0.45  # BW rewrite match attempts            : 429
% 0.21/0.45  # BW rewrite match successes           : 89
% 0.21/0.45  # Condensation attempts                : 0
% 0.21/0.45  # Condensation successes               : 0
% 0.21/0.45  # Termbank termtop insertions          : 79086
% 0.21/0.45  
% 0.21/0.45  # -------------------------------------------------
% 0.21/0.45  # User time                : 0.092 s
% 0.21/0.45  # System time              : 0.007 s
% 0.21/0.45  # Total time               : 0.099 s
% 0.21/0.45  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
