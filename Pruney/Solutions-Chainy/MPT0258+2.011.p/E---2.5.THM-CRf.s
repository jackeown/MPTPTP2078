%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:41:49 EST 2020

% Result     : Theorem 29.70s
% Output     : CNFRefutation 29.70s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 268 expanded)
%              Number of clauses        :   41 ( 126 expanded)
%              Number of leaves         :   13 (  68 expanded)
%              Depth                    :   14
%              Number of atoms          :  142 ( 437 expanded)
%              Number of equality atoms :   47 ( 221 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t74_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( ~ r1_xboole_0(X1,k3_xboole_0(X2,X3))
        & r1_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t81_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_xboole_0(X1,k4_xboole_0(X2,X3))
     => r1_xboole_0(X2,k4_xboole_0(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_xboole_1)).

fof(t46_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t20_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3)
        & ! [X4] :
            ( ( r1_tarski(X4,X2)
              & r1_tarski(X4,X3) )
           => r1_tarski(X4,X1) ) )
     => X1 = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_xboole_1)).

fof(t38_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_tarski(X1,X2),X3)
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(t53_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & r2_hidden(X3,X2) )
     => k3_xboole_0(k2_tarski(X1,X3),X2) = k2_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_zfmisc_1)).

fof(c_0_13,plain,(
    ! [X19,X20,X21] :
      ( r1_xboole_0(X19,k3_xboole_0(X20,X21))
      | ~ r1_xboole_0(X19,X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t74_xboole_1])])])).

fof(c_0_14,plain,(
    ! [X17,X18] : k4_xboole_0(X17,k4_xboole_0(X17,X18)) = k3_xboole_0(X17,X18) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_15,plain,(
    ! [X9] : k3_xboole_0(X9,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

cnf(c_0_16,plain,
    ( r1_xboole_0(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_19,plain,(
    ! [X25,X26] :
      ( ( ~ r1_xboole_0(X25,X26)
        | k4_xboole_0(X25,X26) = X25 )
      & ( k4_xboole_0(X25,X26) != X25
        | r1_xboole_0(X25,X26) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

cnf(c_0_20,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_21,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_18,c_0_17])).

fof(c_0_22,plain,(
    ! [X29,X30] : k3_tarski(k2_tarski(X29,X30)) = k2_xboole_0(X29,X30) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_23,plain,(
    ! [X27,X28] : k1_enumset1(X27,X27,X28) = k2_tarski(X27,X28) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_24,plain,(
    ! [X10,X11] : r1_tarski(k4_xboole_0(X10,X11),X10) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_25,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,k1_xboole_0))
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

fof(c_0_27,plain,(
    ! [X22,X23,X24] :
      ( ~ r1_xboole_0(X22,k4_xboole_0(X23,X24))
      | r1_xboole_0(X23,k4_xboole_0(X22,X24)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t81_xboole_1])])).

fof(c_0_28,plain,(
    ! [X15,X16] : k4_xboole_0(X15,k2_xboole_0(X15,X16)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t46_xboole_1])).

cnf(c_0_29,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_31,plain,(
    ! [X12,X13,X14] : k4_xboole_0(k4_xboole_0(X12,X13),X14) = k4_xboole_0(X12,k2_xboole_0(X13,X14)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_32,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k1_xboole_0)) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_34,plain,
    ( r1_xboole_0(X2,k4_xboole_0(X1,X3))
    | ~ r1_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_37,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_38,plain,(
    ! [X5,X6,X7] :
      ( ( r1_tarski(esk1_3(X5,X6,X7),X6)
        | ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X5,X7)
        | X5 = k3_xboole_0(X6,X7) )
      & ( r1_tarski(esk1_3(X5,X6,X7),X7)
        | ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X5,X7)
        | X5 = k3_xboole_0(X6,X7) )
      & ( ~ r1_tarski(esk1_3(X5,X6,X7),X5)
        | ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X5,X7)
        | X5 = k3_xboole_0(X6,X7) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_xboole_1])])])])).

fof(c_0_39,plain,(
    ! [X31,X32,X33] :
      ( ( r2_hidden(X31,X33)
        | ~ r1_tarski(k2_tarski(X31,X32),X33) )
      & ( r2_hidden(X32,X33)
        | ~ r1_tarski(k2_tarski(X31,X32),X33) )
      & ( ~ r2_hidden(X31,X33)
        | ~ r2_hidden(X32,X33)
        | r1_tarski(k2_tarski(X31,X32),X33) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_41,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,k1_xboole_0))
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_26])).

cnf(c_0_42,plain,
    ( k4_xboole_0(X1,k3_tarski(k1_enumset1(X1,X1,X2))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_43,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k3_tarski(k1_enumset1(X2,X2,X3))) ),
    inference(rw,[status(thm)],[c_0_37,c_0_36])).

cnf(c_0_44,plain,
    ( r1_tarski(esk1_3(X1,X2,X3),X2)
    | X1 = k3_xboole_0(X2,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_45,plain,
    ( r1_tarski(k2_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_46,plain,
    ( r1_tarski(X1,X1)
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_47,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_48,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X1),X2) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_49,plain,
    ( X1 = k4_xboole_0(X2,k4_xboole_0(X2,X3))
    | r1_tarski(esk1_3(X1,X2,X3),X2)
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_44,c_0_17])).

cnf(c_0_50,plain,
    ( r1_tarski(k1_enumset1(X1,X1,X3),X2)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_45,c_0_30])).

cnf(c_0_51,plain,
    ( r1_tarski(X1,X1)
    | k4_xboole_0(X2,X1) != X2 ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_52,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_48,c_0_48])).

fof(c_0_53,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( r2_hidden(X1,X2)
          & r2_hidden(X3,X2) )
       => k3_xboole_0(k2_tarski(X1,X3),X2) = k2_tarski(X1,X3) ) ),
    inference(assume_negation,[status(cth)],[t53_zfmisc_1])).

cnf(c_0_54,plain,
    ( k1_enumset1(X1,X1,X2) = k4_xboole_0(X3,k4_xboole_0(X3,X4))
    | r1_tarski(esk1_3(k1_enumset1(X1,X1,X2),X3,X4),X3)
    | ~ r2_hidden(X2,X4)
    | ~ r2_hidden(X1,X4)
    | ~ r1_tarski(k1_enumset1(X1,X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_55,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

fof(c_0_56,negated_conjecture,
    ( r2_hidden(esk2_0,esk3_0)
    & r2_hidden(esk4_0,esk3_0)
    & k3_xboole_0(k2_tarski(esk2_0,esk4_0),esk3_0) != k2_tarski(esk2_0,esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_53])])])).

cnf(c_0_57,plain,
    ( k4_xboole_0(k1_enumset1(X1,X1,X2),k4_xboole_0(k1_enumset1(X1,X1,X2),X3)) = k1_enumset1(X1,X1,X2)
    | r1_tarski(esk1_3(k1_enumset1(X1,X1,X2),k1_enumset1(X1,X1,X2),X3),k1_enumset1(X1,X1,X2))
    | ~ r2_hidden(X2,X3)
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_59,negated_conjecture,
    ( k3_xboole_0(k2_tarski(esk2_0,esk4_0),esk3_0) != k2_tarski(esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_60,plain,
    ( X1 = k3_xboole_0(X2,X3)
    | ~ r1_tarski(esk1_3(X1,X2,X3),X1)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_61,negated_conjecture,
    ( k4_xboole_0(k1_enumset1(X1,X1,esk4_0),k4_xboole_0(k1_enumset1(X1,X1,esk4_0),esk3_0)) = k1_enumset1(X1,X1,esk4_0)
    | r1_tarski(esk1_3(k1_enumset1(X1,X1,esk4_0),k1_enumset1(X1,X1,esk4_0),esk3_0),k1_enumset1(X1,X1,esk4_0))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_63,negated_conjecture,
    ( k4_xboole_0(k1_enumset1(esk2_0,esk2_0,esk4_0),k4_xboole_0(k1_enumset1(esk2_0,esk2_0,esk4_0),esk3_0)) != k1_enumset1(esk2_0,esk2_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_30]),c_0_30]),c_0_17])).

cnf(c_0_64,plain,
    ( X1 = k4_xboole_0(X2,k4_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_60,c_0_17])).

cnf(c_0_65,negated_conjecture,
    ( r1_tarski(esk1_3(k1_enumset1(esk2_0,esk2_0,esk4_0),k1_enumset1(esk2_0,esk2_0,esk4_0),esk3_0),k1_enumset1(esk2_0,esk2_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63])).

cnf(c_0_66,negated_conjecture,
    ( ~ r1_tarski(k1_enumset1(esk2_0,esk2_0,esk4_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_55])]),c_0_63])).

cnf(c_0_67,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_50]),c_0_58]),c_0_62])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:15:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 29.70/29.92  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 29.70/29.92  # and selection function SelectComplexExceptUniqMaxHorn.
% 29.70/29.92  #
% 29.70/29.92  # Preprocessing time       : 0.041 s
% 29.70/29.92  # Presaturation interreduction done
% 29.70/29.92  
% 29.70/29.92  # Proof found!
% 29.70/29.92  # SZS status Theorem
% 29.70/29.92  # SZS output start CNFRefutation
% 29.70/29.92  fof(t74_xboole_1, axiom, ![X1, X2, X3]:~((~(r1_xboole_0(X1,k3_xboole_0(X2,X3)))&r1_xboole_0(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_xboole_1)).
% 29.70/29.92  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 29.70/29.92  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 29.70/29.92  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 29.70/29.92  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 29.70/29.92  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 29.70/29.92  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 29.70/29.92  fof(t81_xboole_1, axiom, ![X1, X2, X3]:(r1_xboole_0(X1,k4_xboole_0(X2,X3))=>r1_xboole_0(X2,k4_xboole_0(X1,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_xboole_1)).
% 29.70/29.92  fof(t46_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 29.70/29.92  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 29.70/29.92  fof(t20_xboole_1, axiom, ![X1, X2, X3]:(((r1_tarski(X1,X2)&r1_tarski(X1,X3))&![X4]:((r1_tarski(X4,X2)&r1_tarski(X4,X3))=>r1_tarski(X4,X1)))=>X1=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_xboole_1)).
% 29.70/29.92  fof(t38_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_tarski(X1,X2),X3)<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 29.70/29.92  fof(t53_zfmisc_1, conjecture, ![X1, X2, X3]:((r2_hidden(X1,X2)&r2_hidden(X3,X2))=>k3_xboole_0(k2_tarski(X1,X3),X2)=k2_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_zfmisc_1)).
% 29.70/29.92  fof(c_0_13, plain, ![X19, X20, X21]:(r1_xboole_0(X19,k3_xboole_0(X20,X21))|~r1_xboole_0(X19,X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t74_xboole_1])])])).
% 29.70/29.92  fof(c_0_14, plain, ![X17, X18]:k4_xboole_0(X17,k4_xboole_0(X17,X18))=k3_xboole_0(X17,X18), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 29.70/29.92  fof(c_0_15, plain, ![X9]:k3_xboole_0(X9,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 29.70/29.92  cnf(c_0_16, plain, (r1_xboole_0(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 29.70/29.92  cnf(c_0_17, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 29.70/29.92  cnf(c_0_18, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 29.70/29.92  fof(c_0_19, plain, ![X25, X26]:((~r1_xboole_0(X25,X26)|k4_xboole_0(X25,X26)=X25)&(k4_xboole_0(X25,X26)!=X25|r1_xboole_0(X25,X26))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 29.70/29.92  cnf(c_0_20, plain, (r1_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 29.70/29.92  cnf(c_0_21, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_18, c_0_17])).
% 29.70/29.92  fof(c_0_22, plain, ![X29, X30]:k3_tarski(k2_tarski(X29,X30))=k2_xboole_0(X29,X30), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 29.70/29.92  fof(c_0_23, plain, ![X27, X28]:k1_enumset1(X27,X27,X28)=k2_tarski(X27,X28), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 29.70/29.92  fof(c_0_24, plain, ![X10, X11]:r1_tarski(k4_xboole_0(X10,X11),X10), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 29.70/29.92  cnf(c_0_25, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 29.70/29.92  cnf(c_0_26, plain, (r1_xboole_0(X1,k4_xboole_0(X2,k1_xboole_0))|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 29.70/29.92  fof(c_0_27, plain, ![X22, X23, X24]:(~r1_xboole_0(X22,k4_xboole_0(X23,X24))|r1_xboole_0(X23,k4_xboole_0(X22,X24))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t81_xboole_1])])).
% 29.70/29.92  fof(c_0_28, plain, ![X15, X16]:k4_xboole_0(X15,k2_xboole_0(X15,X16))=k1_xboole_0, inference(variable_rename,[status(thm)],[t46_xboole_1])).
% 29.70/29.92  cnf(c_0_29, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 29.70/29.92  cnf(c_0_30, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 29.70/29.92  fof(c_0_31, plain, ![X12, X13, X14]:k4_xboole_0(k4_xboole_0(X12,X13),X14)=k4_xboole_0(X12,k2_xboole_0(X13,X14)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 29.70/29.92  cnf(c_0_32, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 29.70/29.92  cnf(c_0_33, plain, (k4_xboole_0(X1,k4_xboole_0(X2,k1_xboole_0))=X1|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 29.70/29.92  cnf(c_0_34, plain, (r1_xboole_0(X2,k4_xboole_0(X1,X3))|~r1_xboole_0(X1,k4_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 29.70/29.92  cnf(c_0_35, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_28])).
% 29.70/29.92  cnf(c_0_36, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_29, c_0_30])).
% 29.70/29.92  cnf(c_0_37, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 29.70/29.92  fof(c_0_38, plain, ![X5, X6, X7]:(((r1_tarski(esk1_3(X5,X6,X7),X6)|(~r1_tarski(X5,X6)|~r1_tarski(X5,X7))|X5=k3_xboole_0(X6,X7))&(r1_tarski(esk1_3(X5,X6,X7),X7)|(~r1_tarski(X5,X6)|~r1_tarski(X5,X7))|X5=k3_xboole_0(X6,X7)))&(~r1_tarski(esk1_3(X5,X6,X7),X5)|(~r1_tarski(X5,X6)|~r1_tarski(X5,X7))|X5=k3_xboole_0(X6,X7))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_xboole_1])])])])).
% 29.70/29.92  fof(c_0_39, plain, ![X31, X32, X33]:(((r2_hidden(X31,X33)|~r1_tarski(k2_tarski(X31,X32),X33))&(r2_hidden(X32,X33)|~r1_tarski(k2_tarski(X31,X32),X33)))&(~r2_hidden(X31,X33)|~r2_hidden(X32,X33)|r1_tarski(k2_tarski(X31,X32),X33))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).
% 29.70/29.92  cnf(c_0_40, plain, (r1_tarski(X1,X1)|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 29.70/29.92  cnf(c_0_41, plain, (r1_xboole_0(X1,k4_xboole_0(X2,k1_xboole_0))|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_34, c_0_26])).
% 29.70/29.92  cnf(c_0_42, plain, (k4_xboole_0(X1,k3_tarski(k1_enumset1(X1,X1,X2)))=k1_xboole_0), inference(rw,[status(thm)],[c_0_35, c_0_36])).
% 29.70/29.92  cnf(c_0_43, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k3_tarski(k1_enumset1(X2,X2,X3)))), inference(rw,[status(thm)],[c_0_37, c_0_36])).
% 29.70/29.92  cnf(c_0_44, plain, (r1_tarski(esk1_3(X1,X2,X3),X2)|X1=k3_xboole_0(X2,X3)|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 29.70/29.92  cnf(c_0_45, plain, (r1_tarski(k2_tarski(X1,X3),X2)|~r2_hidden(X1,X2)|~r2_hidden(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 29.70/29.92  cnf(c_0_46, plain, (r1_tarski(X1,X1)|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 29.70/29.92  cnf(c_0_47, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_19])).
% 29.70/29.92  cnf(c_0_48, plain, (k4_xboole_0(k4_xboole_0(X1,X1),X2)=k1_xboole_0), inference(rw,[status(thm)],[c_0_42, c_0_43])).
% 29.70/29.92  cnf(c_0_49, plain, (X1=k4_xboole_0(X2,k4_xboole_0(X2,X3))|r1_tarski(esk1_3(X1,X2,X3),X2)|~r1_tarski(X1,X3)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_44, c_0_17])).
% 29.70/29.92  cnf(c_0_50, plain, (r1_tarski(k1_enumset1(X1,X1,X3),X2)|~r2_hidden(X3,X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_45, c_0_30])).
% 29.70/29.92  cnf(c_0_51, plain, (r1_tarski(X1,X1)|k4_xboole_0(X2,X1)!=X2), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 29.70/29.92  cnf(c_0_52, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_48, c_0_48])).
% 29.70/29.92  fof(c_0_53, negated_conjecture, ~(![X1, X2, X3]:((r2_hidden(X1,X2)&r2_hidden(X3,X2))=>k3_xboole_0(k2_tarski(X1,X3),X2)=k2_tarski(X1,X3))), inference(assume_negation,[status(cth)],[t53_zfmisc_1])).
% 29.70/29.92  cnf(c_0_54, plain, (k1_enumset1(X1,X1,X2)=k4_xboole_0(X3,k4_xboole_0(X3,X4))|r1_tarski(esk1_3(k1_enumset1(X1,X1,X2),X3,X4),X3)|~r2_hidden(X2,X4)|~r2_hidden(X1,X4)|~r1_tarski(k1_enumset1(X1,X1,X2),X3)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 29.70/29.92  cnf(c_0_55, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 29.70/29.92  fof(c_0_56, negated_conjecture, ((r2_hidden(esk2_0,esk3_0)&r2_hidden(esk4_0,esk3_0))&k3_xboole_0(k2_tarski(esk2_0,esk4_0),esk3_0)!=k2_tarski(esk2_0,esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_53])])])).
% 29.70/29.92  cnf(c_0_57, plain, (k4_xboole_0(k1_enumset1(X1,X1,X2),k4_xboole_0(k1_enumset1(X1,X1,X2),X3))=k1_enumset1(X1,X1,X2)|r1_tarski(esk1_3(k1_enumset1(X1,X1,X2),k1_enumset1(X1,X1,X2),X3),k1_enumset1(X1,X1,X2))|~r2_hidden(X2,X3)|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 29.70/29.92  cnf(c_0_58, negated_conjecture, (r2_hidden(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 29.70/29.92  cnf(c_0_59, negated_conjecture, (k3_xboole_0(k2_tarski(esk2_0,esk4_0),esk3_0)!=k2_tarski(esk2_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 29.70/29.92  cnf(c_0_60, plain, (X1=k3_xboole_0(X2,X3)|~r1_tarski(esk1_3(X1,X2,X3),X1)|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 29.70/29.92  cnf(c_0_61, negated_conjecture, (k4_xboole_0(k1_enumset1(X1,X1,esk4_0),k4_xboole_0(k1_enumset1(X1,X1,esk4_0),esk3_0))=k1_enumset1(X1,X1,esk4_0)|r1_tarski(esk1_3(k1_enumset1(X1,X1,esk4_0),k1_enumset1(X1,X1,esk4_0),esk3_0),k1_enumset1(X1,X1,esk4_0))|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 29.70/29.92  cnf(c_0_62, negated_conjecture, (r2_hidden(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 29.70/29.92  cnf(c_0_63, negated_conjecture, (k4_xboole_0(k1_enumset1(esk2_0,esk2_0,esk4_0),k4_xboole_0(k1_enumset1(esk2_0,esk2_0,esk4_0),esk3_0))!=k1_enumset1(esk2_0,esk2_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_30]), c_0_30]), c_0_17])).
% 29.70/29.92  cnf(c_0_64, plain, (X1=k4_xboole_0(X2,k4_xboole_0(X2,X3))|~r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_60, c_0_17])).
% 29.70/29.92  cnf(c_0_65, negated_conjecture, (r1_tarski(esk1_3(k1_enumset1(esk2_0,esk2_0,esk4_0),k1_enumset1(esk2_0,esk2_0,esk4_0),esk3_0),k1_enumset1(esk2_0,esk2_0,esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_63])).
% 29.70/29.92  cnf(c_0_66, negated_conjecture, (~r1_tarski(k1_enumset1(esk2_0,esk2_0,esk4_0),esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_55])]), c_0_63])).
% 29.70/29.92  cnf(c_0_67, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_50]), c_0_58]), c_0_62])]), ['proof']).
% 29.70/29.92  # SZS output end CNFRefutation
% 29.70/29.92  # Proof object total steps             : 68
% 29.70/29.92  # Proof object clause steps            : 41
% 29.70/29.92  # Proof object formula steps           : 27
% 29.70/29.92  # Proof object conjectures             : 11
% 29.70/29.92  # Proof object clause conjectures      : 8
% 29.70/29.92  # Proof object formula conjectures     : 3
% 29.70/29.92  # Proof object initial clauses used    : 17
% 29.70/29.92  # Proof object initial formulas used   : 13
% 29.70/29.92  # Proof object generating inferences   : 14
% 29.70/29.92  # Proof object simplifying inferences  : 19
% 29.70/29.92  # Training examples: 0 positive, 0 negative
% 29.70/29.92  # Parsed axioms                        : 13
% 29.70/29.92  # Removed by relevancy pruning/SinE    : 0
% 29.70/29.92  # Initial clauses                      : 20
% 29.70/29.92  # Removed in clause preprocessing      : 3
% 29.70/29.92  # Initial clauses in saturation        : 17
% 29.70/29.92  # Processed clauses                    : 66284
% 29.70/29.92  # ...of these trivial                  : 1121
% 29.70/29.92  # ...subsumed                          : 61839
% 29.70/29.92  # ...remaining for further processing  : 3324
% 29.70/29.92  # Other redundant clauses eliminated   : 123350
% 29.70/29.92  # Clauses deleted for lack of memory   : 347981
% 29.70/29.92  # Backward-subsumed                    : 319
% 29.70/29.92  # Backward-rewritten                   : 54
% 29.70/29.92  # Generated clauses                    : 4343592
% 29.70/29.92  # ...of the previous two non-trivial   : 3158593
% 29.70/29.92  # Contextual simplify-reflections      : 22
% 29.70/29.92  # Paramodulations                      : 4220242
% 29.70/29.92  # Factorizations                       : 0
% 29.70/29.92  # Equation resolutions                 : 123350
% 29.70/29.92  # Propositional unsat checks           : 0
% 29.70/29.92  #    Propositional check models        : 0
% 29.70/29.92  #    Propositional check unsatisfiable : 0
% 29.70/29.92  #    Propositional clauses             : 0
% 29.70/29.92  #    Propositional clauses after purity: 0
% 29.70/29.92  #    Propositional unsat core size     : 0
% 29.70/29.92  #    Propositional preprocessing time  : 0.000
% 29.70/29.92  #    Propositional encoding time       : 0.000
% 29.70/29.92  #    Propositional solver time         : 0.000
% 29.70/29.92  #    Success case prop preproc time    : 0.000
% 29.70/29.92  #    Success case prop encoding time   : 0.000
% 29.70/29.92  #    Success case prop solver time     : 0.000
% 29.70/29.92  # Current number of processed clauses  : 2934
% 29.70/29.92  #    Positive orientable unit clauses  : 606
% 29.70/29.92  #    Positive unorientable unit clauses: 0
% 29.70/29.92  #    Negative unit clauses             : 5
% 29.70/29.92  #    Non-unit-clauses                  : 2323
% 29.70/29.92  # Current number of unprocessed clauses: 1888798
% 29.70/29.92  # ...number of literals in the above   : 4946039
% 29.70/29.92  # Current number of archived formulas  : 0
% 29.70/29.92  # Current number of archived clauses   : 393
% 29.70/29.92  # Clause-clause subsumption calls (NU) : 1657424
% 29.70/29.92  # Rec. Clause-clause subsumption calls : 1581306
% 29.70/29.92  # Non-unit clause-clause subsumptions  : 62167
% 29.70/29.92  # Unit Clause-clause subsumption calls : 18219
% 29.70/29.92  # Rewrite failures with RHS unbound    : 0
% 29.70/29.92  # BW rewrite match attempts            : 38937
% 29.70/29.92  # BW rewrite match successes           : 28
% 29.70/29.92  # Condensation attempts                : 0
% 29.70/29.92  # Condensation successes               : 0
% 29.70/29.92  # Termbank termtop insertions          : 65791754
% 29.80/30.00  
% 29.80/30.00  # -------------------------------------------------
% 29.80/30.00  # User time                : 28.666 s
% 29.80/30.00  # System time              : 0.951 s
% 29.80/30.00  # Total time               : 29.617 s
% 29.80/30.00  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
