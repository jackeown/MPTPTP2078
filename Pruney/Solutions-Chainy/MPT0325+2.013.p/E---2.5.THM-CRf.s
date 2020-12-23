%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:44:07 EST 2020

% Result     : Theorem 0.57s
% Output     : CNFRefutation 0.57s
% Verified   : 
% Statistics : Number of formulae       :   99 (8495 expanded)
%              Number of clauses        :   80 (4013 expanded)
%              Number of leaves         :    9 (2065 expanded)
%              Depth                    :   26
%              Number of atoms          :  222 (18868 expanded)
%              Number of equality atoms :  146 (10669 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t138_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))
     => ( k2_zfmisc_1(X1,X2) = k1_xboole_0
        | ( r1_tarski(X1,X3)
          & r1_tarski(X2,X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(t134_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( k2_zfmisc_1(X1,X2) = k2_zfmisc_1(X3,X4)
     => ( X1 = k1_xboole_0
        | X2 = k1_xboole_0
        | ( X1 = X3
          & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(t123_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t127_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( r1_xboole_0(X1,X2)
        | r1_xboole_0(X3,X4) )
     => r1_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))
       => ( k2_zfmisc_1(X1,X2) = k1_xboole_0
          | ( r1_tarski(X1,X3)
            & r1_tarski(X2,X4) ) ) ) ),
    inference(assume_negation,[status(cth)],[t138_zfmisc_1])).

fof(c_0_10,plain,(
    ! [X32,X33,X34,X35] :
      ( ( X32 = X34
        | X32 = k1_xboole_0
        | X33 = k1_xboole_0
        | k2_zfmisc_1(X32,X33) != k2_zfmisc_1(X34,X35) )
      & ( X33 = X35
        | X32 = k1_xboole_0
        | X33 = k1_xboole_0
        | k2_zfmisc_1(X32,X33) != k2_zfmisc_1(X34,X35) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t134_zfmisc_1])])])).

fof(c_0_11,plain,(
    ! [X24,X25,X26,X27] : k2_zfmisc_1(k3_xboole_0(X24,X25),k3_xboole_0(X26,X27)) = k3_xboole_0(k2_zfmisc_1(X24,X26),k2_zfmisc_1(X25,X27)) ),
    inference(variable_rename,[status(thm)],[t123_zfmisc_1])).

fof(c_0_12,plain,(
    ! [X22,X23] :
      ( ~ r1_tarski(X22,X23)
      | k3_xboole_0(X22,X23) = X22 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_13,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk6_0))
    & k2_zfmisc_1(esk3_0,esk4_0) != k1_xboole_0
    & ( ~ r1_tarski(esk3_0,esk5_0)
      | ~ r1_tarski(esk4_0,esk6_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

cnf(c_0_14,plain,
    ( X1 = X2
    | X3 = k1_xboole_0
    | X1 = k1_xboole_0
    | k2_zfmisc_1(X3,X1) != k2_zfmisc_1(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_18,plain,(
    ! [X20,X21] : r1_tarski(k3_xboole_0(X20,X21),X20) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

fof(c_0_19,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_20,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | k3_xboole_0(X3,X4) = k1_xboole_0
    | k3_xboole_0(X1,X2) = X5
    | k3_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X4,X2)) != k2_zfmisc_1(X6,X5) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( k3_xboole_0(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk6_0)) = k2_zfmisc_1(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_22,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk5_0) = k1_xboole_0
    | k3_xboole_0(esk4_0,esk6_0) = k1_xboole_0
    | k3_xboole_0(esk4_0,esk6_0) = X1
    | k2_zfmisc_1(esk3_0,esk4_0) != k2_zfmisc_1(X2,X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

fof(c_0_25,plain,(
    ! [X11,X12] :
      ( ( ~ r1_xboole_0(X11,X12)
        | k3_xboole_0(X11,X12) = k1_xboole_0 )
      & ( k3_xboole_0(X11,X12) != k1_xboole_0
        | r1_xboole_0(X11,X12) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_26,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_22]),c_0_23])).

cnf(c_0_27,negated_conjecture,
    ( k3_xboole_0(esk4_0,esk6_0) = esk4_0
    | k3_xboole_0(esk4_0,esk6_0) = k1_xboole_0
    | k3_xboole_0(esk3_0,esk5_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_24])).

fof(c_0_28,plain,(
    ! [X14,X15,X17,X18,X19] :
      ( ( r1_xboole_0(X14,X15)
        | r2_hidden(esk2_2(X14,X15),k3_xboole_0(X14,X15)) )
      & ( ~ r2_hidden(X19,k3_xboole_0(X17,X18))
        | ~ r1_xboole_0(X17,X18) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

cnf(c_0_29,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk5_0) = k1_xboole_0
    | k3_xboole_0(esk4_0,esk6_0) = k1_xboole_0
    | k3_xboole_0(esk4_0,esk4_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_31,plain,
    ( X1 = X2
    | X1 = k1_xboole_0
    | X3 = k1_xboole_0
    | k2_zfmisc_1(X1,X3) != k2_zfmisc_1(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_32,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_33,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( k3_xboole_0(esk4_0,esk4_0) = esk4_0
    | k3_xboole_0(esk3_0,esk5_0) = k1_xboole_0
    | r1_xboole_0(esk4_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_35,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk2_2(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,plain,
    ( X1 = k3_xboole_0(X2,X3)
    | X1 = k1_xboole_0
    | X4 = k1_xboole_0
    | k2_zfmisc_1(X1,X4) != k3_xboole_0(k2_zfmisc_1(X2,X5),k2_zfmisc_1(X3,X6)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_15])).

cnf(c_0_37,plain,
    ( X1 = k3_xboole_0(X2,X3)
    | X1 = k1_xboole_0
    | X4 = k1_xboole_0
    | k2_zfmisc_1(X4,X1) != k3_xboole_0(k2_zfmisc_1(X5,X2),k2_zfmisc_1(X6,X3)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_38,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_39,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X1)) = k3_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_32]),c_0_23])).

fof(c_0_40,plain,(
    ! [X28,X29,X30,X31] :
      ( ( ~ r1_xboole_0(X28,X29)
        | r1_xboole_0(k2_zfmisc_1(X28,X30),k2_zfmisc_1(X29,X31)) )
      & ( ~ r1_xboole_0(X30,X31)
        | r1_xboole_0(k2_zfmisc_1(X28,X30),k2_zfmisc_1(X29,X31)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t127_zfmisc_1])])])).

cnf(c_0_41,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk5_0) = k1_xboole_0
    | k3_xboole_0(esk4_0,esk4_0) = esk4_0
    | ~ r2_hidden(X1,k3_xboole_0(esk4_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_42,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk2_2(X1,X2),k3_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_23])).

cnf(c_0_43,negated_conjecture,
    ( X1 = k3_xboole_0(esk3_0,esk5_0)
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k2_zfmisc_1(X1,X2) != k2_zfmisc_1(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_21])).

cnf(c_0_44,negated_conjecture,
    ( X1 = k3_xboole_0(esk4_0,esk6_0)
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k2_zfmisc_1(X2,X1) != k2_zfmisc_1(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_21])).

cnf(c_0_45,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X2,k3_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,esk4_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_47,plain,
    ( r1_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X4,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_48,negated_conjecture,
    ( k3_xboole_0(esk4_0,esk4_0) = esk4_0
    | k3_xboole_0(esk3_0,esk5_0) = k1_xboole_0
    | r1_xboole_0(esk6_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_49,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk5_0) = esk3_0
    | esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_43])).

cnf(c_0_50,negated_conjecture,
    ( k3_xboole_0(esk4_0,esk6_0) = esk4_0
    | esk4_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_44])).

cnf(c_0_51,plain,
    ( k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X3,X2),k2_zfmisc_1(X1,X4)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_23]),c_0_15])).

cnf(c_0_52,negated_conjecture,
    ( ~ r1_xboole_0(k2_zfmisc_1(esk5_0,esk6_0),k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_21]),c_0_46])).

cnf(c_0_53,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk5_0) = k1_xboole_0
    | k3_xboole_0(esk4_0,esk4_0) = esk4_0
    | r1_xboole_0(k2_zfmisc_1(X1,esk6_0),k2_zfmisc_1(X2,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_54,negated_conjecture,
    ( ~ r1_tarski(esk3_0,esk5_0)
    | ~ r1_tarski(esk4_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_55,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | r1_tarski(esk3_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_49])).

cnf(c_0_56,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | r1_tarski(esk4_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_50])).

cnf(c_0_57,plain,
    ( r1_tarski(k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)),k2_zfmisc_1(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_51])).

cnf(c_0_58,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_26])).

cnf(c_0_59,negated_conjecture,
    ( k3_xboole_0(esk4_0,esk4_0) = esk4_0
    | k3_xboole_0(esk3_0,esk5_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_60,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56])).

cnf(c_0_61,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_21])).

cnf(c_0_62,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_16,c_0_58])).

cnf(c_0_63,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk5_0) = k1_xboole_0
    | k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | esk3_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_64,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | k2_zfmisc_1(X1,X2) != k2_zfmisc_1(k1_xboole_0,X3) ),
    inference(ef,[status(thm)],[c_0_31])).

cnf(c_0_65,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_23])).

cnf(c_0_66,negated_conjecture,
    ( k3_xboole_0(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk4_0)) = k2_zfmisc_1(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_61])).

cnf(c_0_67,negated_conjecture,
    ( k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | esk3_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_68,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | k3_xboole_0(X3,X4) = k1_xboole_0
    | k3_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X4,X2)) != k2_zfmisc_1(k1_xboole_0,X5) ),
    inference(spm,[status(thm)],[c_0_64,c_0_15])).

cnf(c_0_69,negated_conjecture,
    ( ~ r1_xboole_0(k2_zfmisc_1(esk5_0,esk4_0),k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_46])).

cnf(c_0_70,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_67])).

cnf(c_0_71,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk5_0) = k1_xboole_0
    | k3_xboole_0(esk4_0,esk4_0) = k1_xboole_0
    | k2_zfmisc_1(esk3_0,esk4_0) != k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_68,c_0_66])).

cnf(c_0_72,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | ~ r1_xboole_0(k2_zfmisc_1(esk5_0,k1_xboole_0),k2_zfmisc_1(esk3_0,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_60])).

cnf(c_0_73,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | r1_xboole_0(k2_zfmisc_1(X1,k1_xboole_0),k2_zfmisc_1(X2,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_70])).

cnf(c_0_74,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_21])).

cnf(c_0_75,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk5_0) = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | k2_zfmisc_1(esk3_0,esk4_0) != k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_71,c_0_59])).

cnf(c_0_76,negated_conjecture,
    ( esk3_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_77,negated_conjecture,
    ( k3_xboole_0(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk3_0,esk4_0)) = k2_zfmisc_1(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_74])).

cnf(c_0_78,negated_conjecture,
    ( k3_xboole_0(k1_xboole_0,esk5_0) = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | k2_zfmisc_1(k1_xboole_0,esk4_0) != k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_76]),c_0_76])).

cnf(c_0_79,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk3_0) = k1_xboole_0
    | k3_xboole_0(esk4_0,esk4_0) = k1_xboole_0
    | k3_xboole_0(esk4_0,esk4_0) = X1
    | k2_zfmisc_1(esk3_0,esk4_0) != k2_zfmisc_1(X2,X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_77])).

cnf(c_0_80,negated_conjecture,
    ( k3_xboole_0(k1_xboole_0,esk5_0) = k1_xboole_0
    | esk4_0 = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_78])).

cnf(c_0_81,negated_conjecture,
    ( k3_xboole_0(esk4_0,esk4_0) = esk4_0
    | k3_xboole_0(esk4_0,esk4_0) = k1_xboole_0
    | k3_xboole_0(esk3_0,esk3_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_79])).

cnf(c_0_82,plain,
    ( k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)) = k1_xboole_0
    | ~ r1_xboole_0(k2_zfmisc_1(X1,X4),k2_zfmisc_1(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_51])).

cnf(c_0_83,negated_conjecture,
    ( k3_xboole_0(k2_zfmisc_1(k1_xboole_0,esk4_0),k2_zfmisc_1(esk5_0,esk6_0)) = k2_zfmisc_1(k1_xboole_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_76]),c_0_76])).

cnf(c_0_84,negated_conjecture,
    ( k2_zfmisc_1(k1_xboole_0,esk4_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_46,c_0_76])).

cnf(c_0_85,plain,
    ( r1_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_86,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r1_xboole_0(k1_xboole_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_80])).

cnf(c_0_87,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk3_0) = k1_xboole_0
    | k3_xboole_0(esk4_0,esk4_0) = k1_xboole_0
    | esk4_0 != k1_xboole_0 ),
    inference(ef,[status(thm)],[c_0_81])).

cnf(c_0_88,negated_conjecture,
    ( ~ r1_xboole_0(k2_zfmisc_1(k1_xboole_0,esk6_0),k2_zfmisc_1(esk5_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_84])).

cnf(c_0_89,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r1_xboole_0(k2_zfmisc_1(k1_xboole_0,X1),k2_zfmisc_1(esk5_0,X2)) ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_90,negated_conjecture,
    ( k3_xboole_0(esk4_0,esk4_0) = k1_xboole_0
    | k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | esk4_0 != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_87,c_0_76]),c_0_76])).

cnf(c_0_91,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_92,negated_conjecture,
    ( ~ r1_xboole_0(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_77]),c_0_46])).

cnf(c_0_93,negated_conjecture,
    ( k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_90,c_0_91]),c_0_91]),c_0_91])])).

cnf(c_0_94,negated_conjecture,
    ( ~ r1_xboole_0(k2_zfmisc_1(k1_xboole_0,esk4_0),k2_zfmisc_1(k1_xboole_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_92,c_0_76]),c_0_76])).

cnf(c_0_95,negated_conjecture,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_93])).

cnf(c_0_96,negated_conjecture,
    ( ~ r1_xboole_0(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_94,c_0_91]),c_0_91])).

cnf(c_0_97,negated_conjecture,
    ( r1_xboole_0(k2_zfmisc_1(X1,k1_xboole_0),k2_zfmisc_1(X2,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_95])).

cnf(c_0_98,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_96,c_0_97])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.32  % Computer   : n014.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % WCLimit    : 600
% 0.13/0.32  % DateTime   : Tue Dec  1 12:41:07 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.32  # Version: 2.5pre002
% 0.13/0.32  # No SInE strategy applied
% 0.13/0.32  # Trying AutoSched0 for 299 seconds
% 0.57/0.73  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S053N
% 0.57/0.73  # and selection function HSelectMinInfpos.
% 0.57/0.73  #
% 0.57/0.73  # Preprocessing time       : 0.027 s
% 0.57/0.73  # Presaturation interreduction done
% 0.57/0.73  
% 0.57/0.73  # Proof found!
% 0.57/0.73  # SZS status Theorem
% 0.57/0.73  # SZS output start CNFRefutation
% 0.57/0.73  fof(t138_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))=>(k2_zfmisc_1(X1,X2)=k1_xboole_0|(r1_tarski(X1,X3)&r1_tarski(X2,X4)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 0.57/0.73  fof(t134_zfmisc_1, axiom, ![X1, X2, X3, X4]:(k2_zfmisc_1(X1,X2)=k2_zfmisc_1(X3,X4)=>(X1=k1_xboole_0|X2=k1_xboole_0|(X1=X3&X2=X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t134_zfmisc_1)).
% 0.57/0.73  fof(t123_zfmisc_1, axiom, ![X1, X2, X3, X4]:k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4))=k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 0.57/0.73  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.57/0.73  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.57/0.73  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.57/0.73  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.57/0.73  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.57/0.73  fof(t127_zfmisc_1, axiom, ![X1, X2, X3, X4]:((r1_xboole_0(X1,X2)|r1_xboole_0(X3,X4))=>r1_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t127_zfmisc_1)).
% 0.57/0.73  fof(c_0_9, negated_conjecture, ~(![X1, X2, X3, X4]:(r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))=>(k2_zfmisc_1(X1,X2)=k1_xboole_0|(r1_tarski(X1,X3)&r1_tarski(X2,X4))))), inference(assume_negation,[status(cth)],[t138_zfmisc_1])).
% 0.57/0.73  fof(c_0_10, plain, ![X32, X33, X34, X35]:((X32=X34|(X32=k1_xboole_0|X33=k1_xboole_0)|k2_zfmisc_1(X32,X33)!=k2_zfmisc_1(X34,X35))&(X33=X35|(X32=k1_xboole_0|X33=k1_xboole_0)|k2_zfmisc_1(X32,X33)!=k2_zfmisc_1(X34,X35))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t134_zfmisc_1])])])).
% 0.57/0.73  fof(c_0_11, plain, ![X24, X25, X26, X27]:k2_zfmisc_1(k3_xboole_0(X24,X25),k3_xboole_0(X26,X27))=k3_xboole_0(k2_zfmisc_1(X24,X26),k2_zfmisc_1(X25,X27)), inference(variable_rename,[status(thm)],[t123_zfmisc_1])).
% 0.57/0.73  fof(c_0_12, plain, ![X22, X23]:(~r1_tarski(X22,X23)|k3_xboole_0(X22,X23)=X22), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.57/0.73  fof(c_0_13, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk6_0))&(k2_zfmisc_1(esk3_0,esk4_0)!=k1_xboole_0&(~r1_tarski(esk3_0,esk5_0)|~r1_tarski(esk4_0,esk6_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.57/0.73  cnf(c_0_14, plain, (X1=X2|X3=k1_xboole_0|X1=k1_xboole_0|k2_zfmisc_1(X3,X1)!=k2_zfmisc_1(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.57/0.73  cnf(c_0_15, plain, (k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4))=k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.57/0.73  cnf(c_0_16, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.57/0.73  cnf(c_0_17, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.57/0.73  fof(c_0_18, plain, ![X20, X21]:r1_tarski(k3_xboole_0(X20,X21),X20), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.57/0.73  fof(c_0_19, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.57/0.73  cnf(c_0_20, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|k3_xboole_0(X3,X4)=k1_xboole_0|k3_xboole_0(X1,X2)=X5|k3_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X4,X2))!=k2_zfmisc_1(X6,X5)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.57/0.73  cnf(c_0_21, negated_conjecture, (k3_xboole_0(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk6_0))=k2_zfmisc_1(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.57/0.73  cnf(c_0_22, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.57/0.73  cnf(c_0_23, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.57/0.73  cnf(c_0_24, negated_conjecture, (k3_xboole_0(esk3_0,esk5_0)=k1_xboole_0|k3_xboole_0(esk4_0,esk6_0)=k1_xboole_0|k3_xboole_0(esk4_0,esk6_0)=X1|k2_zfmisc_1(esk3_0,esk4_0)!=k2_zfmisc_1(X2,X1)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.57/0.73  fof(c_0_25, plain, ![X11, X12]:((~r1_xboole_0(X11,X12)|k3_xboole_0(X11,X12)=k1_xboole_0)&(k3_xboole_0(X11,X12)!=k1_xboole_0|r1_xboole_0(X11,X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.57/0.73  cnf(c_0_26, plain, (k3_xboole_0(X1,k3_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_22]), c_0_23])).
% 0.57/0.73  cnf(c_0_27, negated_conjecture, (k3_xboole_0(esk4_0,esk6_0)=esk4_0|k3_xboole_0(esk4_0,esk6_0)=k1_xboole_0|k3_xboole_0(esk3_0,esk5_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_24])).
% 0.57/0.73  fof(c_0_28, plain, ![X14, X15, X17, X18, X19]:((r1_xboole_0(X14,X15)|r2_hidden(esk2_2(X14,X15),k3_xboole_0(X14,X15)))&(~r2_hidden(X19,k3_xboole_0(X17,X18))|~r1_xboole_0(X17,X18))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.57/0.73  cnf(c_0_29, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.57/0.73  cnf(c_0_30, negated_conjecture, (k3_xboole_0(esk3_0,esk5_0)=k1_xboole_0|k3_xboole_0(esk4_0,esk6_0)=k1_xboole_0|k3_xboole_0(esk4_0,esk4_0)=esk4_0), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.57/0.73  cnf(c_0_31, plain, (X1=X2|X1=k1_xboole_0|X3=k1_xboole_0|k2_zfmisc_1(X1,X3)!=k2_zfmisc_1(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.57/0.73  cnf(c_0_32, plain, (r1_tarski(k3_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.57/0.73  cnf(c_0_33, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.57/0.73  cnf(c_0_34, negated_conjecture, (k3_xboole_0(esk4_0,esk4_0)=esk4_0|k3_xboole_0(esk3_0,esk5_0)=k1_xboole_0|r1_xboole_0(esk4_0,esk6_0)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.57/0.73  cnf(c_0_35, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk2_2(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.57/0.73  cnf(c_0_36, plain, (X1=k3_xboole_0(X2,X3)|X1=k1_xboole_0|X4=k1_xboole_0|k2_zfmisc_1(X1,X4)!=k3_xboole_0(k2_zfmisc_1(X2,X5),k2_zfmisc_1(X3,X6))), inference(spm,[status(thm)],[c_0_31, c_0_15])).
% 0.57/0.73  cnf(c_0_37, plain, (X1=k3_xboole_0(X2,X3)|X1=k1_xboole_0|X4=k1_xboole_0|k2_zfmisc_1(X4,X1)!=k3_xboole_0(k2_zfmisc_1(X5,X2),k2_zfmisc_1(X6,X3))), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.57/0.73  cnf(c_0_38, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.57/0.73  cnf(c_0_39, plain, (k3_xboole_0(X1,k3_xboole_0(X2,X1))=k3_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_32]), c_0_23])).
% 0.57/0.73  fof(c_0_40, plain, ![X28, X29, X30, X31]:((~r1_xboole_0(X28,X29)|r1_xboole_0(k2_zfmisc_1(X28,X30),k2_zfmisc_1(X29,X31)))&(~r1_xboole_0(X30,X31)|r1_xboole_0(k2_zfmisc_1(X28,X30),k2_zfmisc_1(X29,X31)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t127_zfmisc_1])])])).
% 0.57/0.73  cnf(c_0_41, negated_conjecture, (k3_xboole_0(esk3_0,esk5_0)=k1_xboole_0|k3_xboole_0(esk4_0,esk4_0)=esk4_0|~r2_hidden(X1,k3_xboole_0(esk4_0,esk6_0))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.57/0.73  cnf(c_0_42, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk2_2(X1,X2),k3_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_35, c_0_23])).
% 0.57/0.73  cnf(c_0_43, negated_conjecture, (X1=k3_xboole_0(esk3_0,esk5_0)|X2=k1_xboole_0|X1=k1_xboole_0|k2_zfmisc_1(X1,X2)!=k2_zfmisc_1(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_36, c_0_21])).
% 0.57/0.73  cnf(c_0_44, negated_conjecture, (X1=k3_xboole_0(esk4_0,esk6_0)|X2=k1_xboole_0|X1=k1_xboole_0|k2_zfmisc_1(X2,X1)!=k2_zfmisc_1(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_37, c_0_21])).
% 0.57/0.73  cnf(c_0_45, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X2,k3_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.57/0.73  cnf(c_0_46, negated_conjecture, (k2_zfmisc_1(esk3_0,esk4_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.57/0.73  cnf(c_0_47, plain, (r1_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X4,X2))|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.57/0.73  cnf(c_0_48, negated_conjecture, (k3_xboole_0(esk4_0,esk4_0)=esk4_0|k3_xboole_0(esk3_0,esk5_0)=k1_xboole_0|r1_xboole_0(esk6_0,esk4_0)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.57/0.73  cnf(c_0_49, negated_conjecture, (k3_xboole_0(esk3_0,esk5_0)=esk3_0|esk3_0=k1_xboole_0|esk4_0=k1_xboole_0), inference(er,[status(thm)],[c_0_43])).
% 0.57/0.73  cnf(c_0_50, negated_conjecture, (k3_xboole_0(esk4_0,esk6_0)=esk4_0|esk4_0=k1_xboole_0|esk3_0=k1_xboole_0), inference(er,[status(thm)],[c_0_44])).
% 0.57/0.73  cnf(c_0_51, plain, (k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))=k3_xboole_0(k2_zfmisc_1(X3,X2),k2_zfmisc_1(X1,X4))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_23]), c_0_15])).
% 0.57/0.73  cnf(c_0_52, negated_conjecture, (~r1_xboole_0(k2_zfmisc_1(esk5_0,esk6_0),k2_zfmisc_1(esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_21]), c_0_46])).
% 0.57/0.73  cnf(c_0_53, negated_conjecture, (k3_xboole_0(esk3_0,esk5_0)=k1_xboole_0|k3_xboole_0(esk4_0,esk4_0)=esk4_0|r1_xboole_0(k2_zfmisc_1(X1,esk6_0),k2_zfmisc_1(X2,esk4_0))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.57/0.74  cnf(c_0_54, negated_conjecture, (~r1_tarski(esk3_0,esk5_0)|~r1_tarski(esk4_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.57/0.74  cnf(c_0_55, negated_conjecture, (esk4_0=k1_xboole_0|esk3_0=k1_xboole_0|r1_tarski(esk3_0,esk5_0)), inference(spm,[status(thm)],[c_0_32, c_0_49])).
% 0.57/0.74  cnf(c_0_56, negated_conjecture, (esk3_0=k1_xboole_0|esk4_0=k1_xboole_0|r1_tarski(esk4_0,esk6_0)), inference(spm,[status(thm)],[c_0_32, c_0_50])).
% 0.57/0.74  cnf(c_0_57, plain, (r1_tarski(k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)),k2_zfmisc_1(X3,X2))), inference(spm,[status(thm)],[c_0_22, c_0_51])).
% 0.57/0.74  cnf(c_0_58, plain, (r1_tarski(k3_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_32, c_0_26])).
% 0.57/0.74  cnf(c_0_59, negated_conjecture, (k3_xboole_0(esk4_0,esk4_0)=esk4_0|k3_xboole_0(esk3_0,esk5_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.57/0.74  cnf(c_0_60, negated_conjecture, (esk3_0=k1_xboole_0|esk4_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56])).
% 0.57/0.74  cnf(c_0_61, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk4_0))), inference(spm,[status(thm)],[c_0_57, c_0_21])).
% 0.57/0.74  cnf(c_0_62, plain, (k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_16, c_0_58])).
% 0.57/0.74  cnf(c_0_63, negated_conjecture, (k3_xboole_0(esk3_0,esk5_0)=k1_xboole_0|k3_xboole_0(k1_xboole_0,k1_xboole_0)=k1_xboole_0|esk3_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.57/0.74  cnf(c_0_64, plain, (X1=k1_xboole_0|X2=k1_xboole_0|k2_zfmisc_1(X1,X2)!=k2_zfmisc_1(k1_xboole_0,X3)), inference(ef,[status(thm)],[c_0_31])).
% 0.57/0.74  cnf(c_0_65, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_38, c_0_23])).
% 0.57/0.74  cnf(c_0_66, negated_conjecture, (k3_xboole_0(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk4_0))=k2_zfmisc_1(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_16, c_0_61])).
% 0.57/0.74  cnf(c_0_67, negated_conjecture, (k3_xboole_0(k1_xboole_0,k1_xboole_0)=k1_xboole_0|esk3_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.57/0.74  cnf(c_0_68, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|k3_xboole_0(X3,X4)=k1_xboole_0|k3_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X4,X2))!=k2_zfmisc_1(k1_xboole_0,X5)), inference(spm,[status(thm)],[c_0_64, c_0_15])).
% 0.57/0.74  cnf(c_0_69, negated_conjecture, (~r1_xboole_0(k2_zfmisc_1(esk5_0,esk4_0),k2_zfmisc_1(esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_46])).
% 0.57/0.74  cnf(c_0_70, negated_conjecture, (esk3_0=k1_xboole_0|r1_xboole_0(k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_29, c_0_67])).
% 0.57/0.74  cnf(c_0_71, negated_conjecture, (k3_xboole_0(esk3_0,esk5_0)=k1_xboole_0|k3_xboole_0(esk4_0,esk4_0)=k1_xboole_0|k2_zfmisc_1(esk3_0,esk4_0)!=k2_zfmisc_1(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_68, c_0_66])).
% 0.57/0.74  cnf(c_0_72, negated_conjecture, (esk3_0=k1_xboole_0|~r1_xboole_0(k2_zfmisc_1(esk5_0,k1_xboole_0),k2_zfmisc_1(esk3_0,k1_xboole_0))), inference(spm,[status(thm)],[c_0_69, c_0_60])).
% 0.57/0.74  cnf(c_0_73, negated_conjecture, (esk3_0=k1_xboole_0|r1_xboole_0(k2_zfmisc_1(X1,k1_xboole_0),k2_zfmisc_1(X2,k1_xboole_0))), inference(spm,[status(thm)],[c_0_47, c_0_70])).
% 0.57/0.74  cnf(c_0_74, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_22, c_0_21])).
% 0.57/0.74  cnf(c_0_75, negated_conjecture, (k3_xboole_0(esk3_0,esk5_0)=k1_xboole_0|esk4_0=k1_xboole_0|k2_zfmisc_1(esk3_0,esk4_0)!=k2_zfmisc_1(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_71, c_0_59])).
% 0.57/0.74  cnf(c_0_76, negated_conjecture, (esk3_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.57/0.74  cnf(c_0_77, negated_conjecture, (k3_xboole_0(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk3_0,esk4_0))=k2_zfmisc_1(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_16, c_0_74])).
% 0.57/0.74  cnf(c_0_78, negated_conjecture, (k3_xboole_0(k1_xboole_0,esk5_0)=k1_xboole_0|esk4_0=k1_xboole_0|k2_zfmisc_1(k1_xboole_0,esk4_0)!=k2_zfmisc_1(k1_xboole_0,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75, c_0_76]), c_0_76])).
% 0.57/0.74  cnf(c_0_79, negated_conjecture, (k3_xboole_0(esk3_0,esk3_0)=k1_xboole_0|k3_xboole_0(esk4_0,esk4_0)=k1_xboole_0|k3_xboole_0(esk4_0,esk4_0)=X1|k2_zfmisc_1(esk3_0,esk4_0)!=k2_zfmisc_1(X2,X1)), inference(spm,[status(thm)],[c_0_20, c_0_77])).
% 0.57/0.74  cnf(c_0_80, negated_conjecture, (k3_xboole_0(k1_xboole_0,esk5_0)=k1_xboole_0|esk4_0=k1_xboole_0), inference(er,[status(thm)],[c_0_78])).
% 0.57/0.74  cnf(c_0_81, negated_conjecture, (k3_xboole_0(esk4_0,esk4_0)=esk4_0|k3_xboole_0(esk4_0,esk4_0)=k1_xboole_0|k3_xboole_0(esk3_0,esk3_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_79])).
% 0.57/0.74  cnf(c_0_82, plain, (k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))=k1_xboole_0|~r1_xboole_0(k2_zfmisc_1(X1,X4),k2_zfmisc_1(X3,X2))), inference(spm,[status(thm)],[c_0_65, c_0_51])).
% 0.57/0.74  cnf(c_0_83, negated_conjecture, (k3_xboole_0(k2_zfmisc_1(k1_xboole_0,esk4_0),k2_zfmisc_1(esk5_0,esk6_0))=k2_zfmisc_1(k1_xboole_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_76]), c_0_76])).
% 0.57/0.74  cnf(c_0_84, negated_conjecture, (k2_zfmisc_1(k1_xboole_0,esk4_0)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_46, c_0_76])).
% 0.57/0.74  cnf(c_0_85, plain, (r1_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.57/0.74  cnf(c_0_86, negated_conjecture, (esk4_0=k1_xboole_0|r1_xboole_0(k1_xboole_0,esk5_0)), inference(spm,[status(thm)],[c_0_29, c_0_80])).
% 0.57/0.74  cnf(c_0_87, negated_conjecture, (k3_xboole_0(esk3_0,esk3_0)=k1_xboole_0|k3_xboole_0(esk4_0,esk4_0)=k1_xboole_0|esk4_0!=k1_xboole_0), inference(ef,[status(thm)],[c_0_81])).
% 0.57/0.74  cnf(c_0_88, negated_conjecture, (~r1_xboole_0(k2_zfmisc_1(k1_xboole_0,esk6_0),k2_zfmisc_1(esk5_0,esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_84])).
% 0.57/0.74  cnf(c_0_89, negated_conjecture, (esk4_0=k1_xboole_0|r1_xboole_0(k2_zfmisc_1(k1_xboole_0,X1),k2_zfmisc_1(esk5_0,X2))), inference(spm,[status(thm)],[c_0_85, c_0_86])).
% 0.57/0.74  cnf(c_0_90, negated_conjecture, (k3_xboole_0(esk4_0,esk4_0)=k1_xboole_0|k3_xboole_0(k1_xboole_0,k1_xboole_0)=k1_xboole_0|esk4_0!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_87, c_0_76]), c_0_76])).
% 0.57/0.74  cnf(c_0_91, negated_conjecture, (esk4_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_88, c_0_89])).
% 0.57/0.74  cnf(c_0_92, negated_conjecture, (~r1_xboole_0(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_77]), c_0_46])).
% 0.57/0.74  cnf(c_0_93, negated_conjecture, (k3_xboole_0(k1_xboole_0,k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_90, c_0_91]), c_0_91]), c_0_91])])).
% 0.57/0.74  cnf(c_0_94, negated_conjecture, (~r1_xboole_0(k2_zfmisc_1(k1_xboole_0,esk4_0),k2_zfmisc_1(k1_xboole_0,esk4_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_92, c_0_76]), c_0_76])).
% 0.57/0.74  cnf(c_0_95, negated_conjecture, (r1_xboole_0(k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_29, c_0_93])).
% 0.57/0.74  cnf(c_0_96, negated_conjecture, (~r1_xboole_0(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k2_zfmisc_1(k1_xboole_0,k1_xboole_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_94, c_0_91]), c_0_91])).
% 0.57/0.74  cnf(c_0_97, negated_conjecture, (r1_xboole_0(k2_zfmisc_1(X1,k1_xboole_0),k2_zfmisc_1(X2,k1_xboole_0))), inference(spm,[status(thm)],[c_0_47, c_0_95])).
% 0.57/0.74  cnf(c_0_98, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_96, c_0_97])]), ['proof']).
% 0.57/0.74  # SZS output end CNFRefutation
% 0.57/0.74  # Proof object total steps             : 99
% 0.57/0.74  # Proof object clause steps            : 80
% 0.57/0.74  # Proof object formula steps           : 19
% 0.57/0.74  # Proof object conjectures             : 55
% 0.57/0.74  # Proof object clause conjectures      : 52
% 0.57/0.74  # Proof object formula conjectures     : 3
% 0.57/0.74  # Proof object initial clauses used    : 15
% 0.57/0.74  # Proof object initial formulas used   : 9
% 0.57/0.74  # Proof object generating inferences   : 57
% 0.57/0.74  # Proof object simplifying inferences  : 25
% 0.57/0.74  # Training examples: 0 positive, 0 negative
% 0.57/0.74  # Parsed axioms                        : 11
% 0.57/0.74  # Removed by relevancy pruning/SinE    : 0
% 0.57/0.74  # Initial clauses                      : 18
% 0.57/0.74  # Removed in clause preprocessing      : 0
% 0.57/0.74  # Initial clauses in saturation        : 18
% 0.57/0.74  # Processed clauses                    : 4289
% 0.57/0.74  # ...of these trivial                  : 122
% 0.57/0.74  # ...subsumed                          : 3004
% 0.57/0.74  # ...remaining for further processing  : 1163
% 0.57/0.74  # Other redundant clauses eliminated   : 96
% 0.57/0.74  # Clauses deleted for lack of memory   : 0
% 0.57/0.74  # Backward-subsumed                    : 385
% 0.57/0.74  # Backward-rewritten                   : 605
% 0.57/0.74  # Generated clauses                    : 26026
% 0.57/0.74  # ...of the previous two non-trivial   : 25006
% 0.57/0.74  # Contextual simplify-reflections      : 11
% 0.57/0.74  # Paramodulations                      : 25569
% 0.57/0.74  # Factorizations                       : 328
% 0.57/0.74  # Equation resolutions                 : 128
% 0.57/0.74  # Propositional unsat checks           : 0
% 0.57/0.74  #    Propositional check models        : 0
% 0.57/0.74  #    Propositional check unsatisfiable : 0
% 0.57/0.74  #    Propositional clauses             : 0
% 0.57/0.74  #    Propositional clauses after purity: 0
% 0.57/0.74  #    Propositional unsat core size     : 0
% 0.57/0.74  #    Propositional preprocessing time  : 0.000
% 0.57/0.74  #    Propositional encoding time       : 0.000
% 0.57/0.74  #    Propositional solver time         : 0.000
% 0.57/0.74  #    Success case prop preproc time    : 0.000
% 0.57/0.74  #    Success case prop encoding time   : 0.000
% 0.57/0.74  #    Success case prop solver time     : 0.000
% 0.57/0.74  # Current number of processed clauses  : 154
% 0.57/0.74  #    Positive orientable unit clauses  : 39
% 0.57/0.74  #    Positive unorientable unit clauses: 7
% 0.57/0.74  #    Negative unit clauses             : 11
% 0.57/0.74  #    Non-unit-clauses                  : 97
% 0.57/0.74  # Current number of unprocessed clauses: 20261
% 0.57/0.74  # ...number of literals in the above   : 60346
% 0.57/0.74  # Current number of archived formulas  : 0
% 0.57/0.74  # Current number of archived clauses   : 1009
% 0.57/0.74  # Clause-clause subsumption calls (NU) : 56340
% 0.57/0.74  # Rec. Clause-clause subsumption calls : 26374
% 0.57/0.74  # Non-unit clause-clause subsumptions  : 3069
% 0.57/0.74  # Unit Clause-clause subsumption calls : 341
% 0.57/0.74  # Rewrite failures with RHS unbound    : 0
% 0.57/0.74  # BW rewrite match attempts            : 1186
% 0.57/0.74  # BW rewrite match successes           : 135
% 0.57/0.74  # Condensation attempts                : 0
% 0.57/0.74  # Condensation successes               : 0
% 0.57/0.74  # Termbank termtop insertions          : 511738
% 0.57/0.74  
% 0.57/0.74  # -------------------------------------------------
% 0.57/0.74  # User time                : 0.402 s
% 0.57/0.74  # System time              : 0.015 s
% 0.57/0.74  # Total time               : 0.417 s
% 0.57/0.74  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
