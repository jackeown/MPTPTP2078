%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:44:07 EST 2020

% Result     : Theorem 0.78s
% Output     : CNFRefutation 0.78s
% Verified   : 
% Statistics : Number of formulae       :   86 (3760 expanded)
%              Number of clauses        :   69 (1728 expanded)
%              Number of leaves         :    8 ( 936 expanded)
%              Depth                    :   19
%              Number of atoms          :  185 (7750 expanded)
%              Number of equality atoms :  119 (4194 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t138_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))
     => ( k2_zfmisc_1(X1,X2) = k1_xboole_0
        | ( r1_tarski(X1,X3)
          & r1_tarski(X2,X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t127_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( r1_xboole_0(X1,X2)
        | r1_xboole_0(X3,X4) )
     => r1_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).

fof(t123_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t134_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( k2_zfmisc_1(X1,X2) = k2_zfmisc_1(X3,X4)
     => ( X1 = k1_xboole_0
        | X2 = k1_xboole_0
        | ( X1 = X3
          & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))
       => ( k2_zfmisc_1(X1,X2) = k1_xboole_0
          | ( r1_tarski(X1,X3)
            & r1_tarski(X2,X4) ) ) ) ),
    inference(assume_negation,[status(cth)],[t138_zfmisc_1])).

fof(c_0_9,plain,(
    ! [X19,X20] :
      ( ~ r1_tarski(X19,X20)
      | k3_xboole_0(X19,X20) = X19 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_10,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk6_0))
    & k2_zfmisc_1(esk3_0,esk4_0) != k1_xboole_0
    & ( ~ r1_tarski(esk3_0,esk5_0)
      | ~ r1_tarski(esk4_0,esk6_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

fof(c_0_11,plain,(
    ! [X25,X26,X27,X28] :
      ( ( ~ r1_xboole_0(X25,X26)
        | r1_xboole_0(k2_zfmisc_1(X25,X27),k2_zfmisc_1(X26,X28)) )
      & ( ~ r1_xboole_0(X27,X28)
        | r1_xboole_0(k2_zfmisc_1(X25,X27),k2_zfmisc_1(X26,X28)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t127_zfmisc_1])])])).

fof(c_0_12,plain,(
    ! [X21,X22,X23,X24] : k2_zfmisc_1(k3_xboole_0(X21,X22),k3_xboole_0(X23,X24)) = k3_xboole_0(k2_zfmisc_1(X21,X23),k2_zfmisc_1(X22,X24)) ),
    inference(variable_rename,[status(thm)],[t123_zfmisc_1])).

fof(c_0_13,plain,(
    ! [X17,X18] : r1_tarski(k3_xboole_0(X17,X18),X17) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

fof(c_0_14,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_15,plain,(
    ! [X29,X30,X31,X32] :
      ( ( X29 = X31
        | X29 = k1_xboole_0
        | X30 = k1_xboole_0
        | k2_zfmisc_1(X29,X30) != k2_zfmisc_1(X31,X32) )
      & ( X30 = X32
        | X29 = k1_xboole_0
        | X30 = k1_xboole_0
        | k2_zfmisc_1(X29,X30) != k2_zfmisc_1(X31,X32) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t134_zfmisc_1])])])).

cnf(c_0_16,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( r1_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X4,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_20,plain,(
    ! [X7,X8] :
      ( ( ~ r1_xboole_0(X7,X8)
        | k3_xboole_0(X7,X8) = k1_xboole_0 )
      & ( k3_xboole_0(X7,X8) != k1_xboole_0
        | r1_xboole_0(X7,X8) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_21,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( X1 = X2
    | X3 = k1_xboole_0
    | X1 = k1_xboole_0
    | k2_zfmisc_1(X3,X1) != k2_zfmisc_1(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,negated_conjecture,
    ( k3_xboole_0(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk6_0)) = k2_zfmisc_1(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_25,plain,
    ( r1_xboole_0(k2_zfmisc_1(X1,X2),k3_xboole_0(k2_zfmisc_1(X3,X4),k2_zfmisc_1(X5,X6)))
    | ~ r1_xboole_0(X2,k3_xboole_0(X4,X6)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_26,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_21]),c_0_22])).

cnf(c_0_28,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | k3_xboole_0(X3,X4) = k1_xboole_0
    | k3_xboole_0(X1,X2) = X5
    | k3_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X4,X2)) != k2_zfmisc_1(X6,X5) ),
    inference(spm,[status(thm)],[c_0_23,c_0_19])).

cnf(c_0_29,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_24])).

cnf(c_0_30,plain,
    ( k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X3,X2),k2_zfmisc_1(X1,X4)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_22]),c_0_19])).

cnf(c_0_31,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_32,negated_conjecture,
    ( r1_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(esk3_0,esk4_0))
    | ~ r1_xboole_0(X2,k3_xboole_0(esk4_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_24])).

cnf(c_0_33,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,esk4_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_35,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk5_0) = k1_xboole_0
    | k3_xboole_0(esk4_0,esk6_0) = k1_xboole_0
    | k3_xboole_0(esk4_0,esk6_0) = X1
    | k2_zfmisc_1(esk3_0,esk4_0) != k2_zfmisc_1(X2,X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_24])).

cnf(c_0_36,negated_conjecture,
    ( k3_xboole_0(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk3_0,esk4_0)) = k2_zfmisc_1(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_29])).

cnf(c_0_37,plain,
    ( r1_tarski(k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)),k2_zfmisc_1(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_30])).

cnf(c_0_38,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_39,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X1)) = k3_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_31]),c_0_22])).

cnf(c_0_40,negated_conjecture,
    ( r1_xboole_0(k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)),k2_zfmisc_1(esk3_0,esk4_0))
    | ~ r1_xboole_0(k3_xboole_0(X2,X4),k3_xboole_0(esk4_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_19])).

cnf(c_0_41,negated_conjecture,
    ( ~ r1_xboole_0(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_24]),c_0_34])).

cnf(c_0_42,negated_conjecture,
    ( k3_xboole_0(esk4_0,esk6_0) = esk4_0
    | k3_xboole_0(esk4_0,esk6_0) = k1_xboole_0
    | k3_xboole_0(esk3_0,esk5_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_35])).

cnf(c_0_43,plain,
    ( X1 = X2
    | X1 = k1_xboole_0
    | X3 = k1_xboole_0
    | k2_zfmisc_1(X1,X3) != k2_zfmisc_1(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_44,negated_conjecture,
    ( r1_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(esk3_0,esk4_0))
    | ~ r1_xboole_0(X2,k3_xboole_0(esk4_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_36])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_24])).

cnf(c_0_46,plain,
    ( r1_xboole_0(X1,k3_xboole_0(X2,X1))
    | k3_xboole_0(X2,X1) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_47,negated_conjecture,
    ( ~ r1_xboole_0(k3_xboole_0(esk4_0,esk6_0),k3_xboole_0(esk4_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_24]),c_0_41])).

cnf(c_0_48,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk5_0) = k1_xboole_0
    | k3_xboole_0(esk4_0,esk6_0) = k1_xboole_0
    | k3_xboole_0(esk4_0,esk4_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_27,c_0_42])).

cnf(c_0_49,plain,
    ( X1 = k3_xboole_0(X2,X3)
    | X1 = k1_xboole_0
    | X4 = k1_xboole_0
    | k2_zfmisc_1(X1,X4) != k3_xboole_0(k2_zfmisc_1(X2,X5),k2_zfmisc_1(X3,X6)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_19])).

cnf(c_0_50,plain,
    ( X1 = k3_xboole_0(X2,X3)
    | X1 = k1_xboole_0
    | X4 = k1_xboole_0
    | k2_zfmisc_1(X4,X1) != k3_xboole_0(k2_zfmisc_1(X5,X2),k2_zfmisc_1(X6,X3)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_19])).

cnf(c_0_51,negated_conjecture,
    ( r1_xboole_0(k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)),k2_zfmisc_1(esk3_0,esk4_0))
    | ~ r1_xboole_0(k3_xboole_0(X2,X4),k3_xboole_0(esk4_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_19])).

cnf(c_0_52,negated_conjecture,
    ( k3_xboole_0(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk4_0)) = k2_zfmisc_1(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_45])).

cnf(c_0_53,plain,
    ( r1_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X2))
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_46,c_0_27])).

cnf(c_0_54,negated_conjecture,
    ( k3_xboole_0(esk4_0,esk4_0) = esk4_0
    | k3_xboole_0(esk3_0,esk5_0) = k1_xboole_0
    | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_55,negated_conjecture,
    ( X1 = k3_xboole_0(esk3_0,esk5_0)
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k2_zfmisc_1(X1,X2) != k2_zfmisc_1(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_24])).

cnf(c_0_56,negated_conjecture,
    ( X1 = k3_xboole_0(esk4_0,esk6_0)
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k2_zfmisc_1(X2,X1) != k2_zfmisc_1(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_24])).

cnf(c_0_57,negated_conjecture,
    ( ~ r1_xboole_0(k3_xboole_0(esk4_0,esk4_0),k3_xboole_0(esk4_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_41])).

cnf(c_0_58,negated_conjecture,
    ( k3_xboole_0(esk4_0,esk4_0) = esk4_0
    | k3_xboole_0(esk3_0,esk5_0) = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_48]),c_0_54])).

cnf(c_0_59,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk5_0) = esk3_0
    | esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_55])).

cnf(c_0_60,negated_conjecture,
    ( k3_xboole_0(esk4_0,esk6_0) = esk4_0
    | esk4_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_56])).

cnf(c_0_61,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk5_0) = k1_xboole_0
    | ~ r1_xboole_0(esk4_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_62,negated_conjecture,
    ( ~ r1_tarski(esk3_0,esk5_0)
    | ~ r1_tarski(esk4_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_63,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | r1_tarski(esk3_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_59])).

cnf(c_0_64,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | r1_tarski(esk4_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_60])).

cnf(c_0_65,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | k2_zfmisc_1(X1,X2) != k2_zfmisc_1(k1_xboole_0,X3) ),
    inference(ef,[status(thm)],[c_0_43])).

cnf(c_0_66,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_27])).

cnf(c_0_67,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk5_0) = k1_xboole_0
    | esk4_0 != k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_58]),c_0_61])).

cnf(c_0_68,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64])).

cnf(c_0_69,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | k3_xboole_0(X3,X4) = k1_xboole_0
    | k3_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X4,X2)) != k2_zfmisc_1(k1_xboole_0,X5) ),
    inference(spm,[status(thm)],[c_0_65,c_0_19])).

cnf(c_0_70,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_16,c_0_66])).

cnf(c_0_71,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk5_0) = k1_xboole_0
    | esk3_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_72,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk5_0) = k1_xboole_0
    | k3_xboole_0(esk4_0,esk4_0) = k1_xboole_0
    | k2_zfmisc_1(esk3_0,esk4_0) != k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_69,c_0_52])).

cnf(c_0_73,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | ~ r1_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k3_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_68])).

cnf(c_0_74,negated_conjecture,
    ( k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | esk3_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_75,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_71])).

cnf(c_0_76,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk5_0) = k1_xboole_0
    | k2_zfmisc_1(esk3_0,esk4_0) != k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_58]),c_0_67])).

cnf(c_0_77,negated_conjecture,
    ( esk3_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_75])).

cnf(c_0_78,negated_conjecture,
    ( k3_xboole_0(k1_xboole_0,esk5_0) = k1_xboole_0
    | k2_zfmisc_1(k1_xboole_0,esk4_0) != k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_77]),c_0_77])).

cnf(c_0_79,negated_conjecture,
    ( k3_xboole_0(k1_xboole_0,esk5_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_78])).

cnf(c_0_80,negated_conjecture,
    ( ~ r1_xboole_0(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_52]),c_0_34])).

cnf(c_0_81,plain,
    ( r1_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_82,negated_conjecture,
    ( r1_xboole_0(k1_xboole_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_79])).

cnf(c_0_83,negated_conjecture,
    ( ~ r1_xboole_0(k2_zfmisc_1(k1_xboole_0,esk4_0),k2_zfmisc_1(esk5_0,esk4_0)) ),
    inference(rw,[status(thm)],[c_0_80,c_0_77])).

cnf(c_0_84,negated_conjecture,
    ( r1_xboole_0(k2_zfmisc_1(k1_xboole_0,X1),k2_zfmisc_1(esk5_0,X2)) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_85,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_83,c_0_84])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.15/0.34  % Computer   : n002.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 19:56:37 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  # Version: 2.5pre002
% 0.15/0.35  # No SInE strategy applied
% 0.15/0.35  # Trying AutoSched0 for 299 seconds
% 0.78/0.96  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S053N
% 0.78/0.96  # and selection function HSelectMinInfpos.
% 0.78/0.96  #
% 0.78/0.96  # Preprocessing time       : 0.027 s
% 0.78/0.96  # Presaturation interreduction done
% 0.78/0.96  
% 0.78/0.96  # Proof found!
% 0.78/0.96  # SZS status Theorem
% 0.78/0.96  # SZS output start CNFRefutation
% 0.78/0.96  fof(t138_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))=>(k2_zfmisc_1(X1,X2)=k1_xboole_0|(r1_tarski(X1,X3)&r1_tarski(X2,X4)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 0.78/0.96  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.78/0.96  fof(t127_zfmisc_1, axiom, ![X1, X2, X3, X4]:((r1_xboole_0(X1,X2)|r1_xboole_0(X3,X4))=>r1_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t127_zfmisc_1)).
% 0.78/0.96  fof(t123_zfmisc_1, axiom, ![X1, X2, X3, X4]:k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4))=k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 0.78/0.96  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.78/0.96  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.78/0.96  fof(t134_zfmisc_1, axiom, ![X1, X2, X3, X4]:(k2_zfmisc_1(X1,X2)=k2_zfmisc_1(X3,X4)=>(X1=k1_xboole_0|X2=k1_xboole_0|(X1=X3&X2=X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t134_zfmisc_1)).
% 0.78/0.96  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.78/0.96  fof(c_0_8, negated_conjecture, ~(![X1, X2, X3, X4]:(r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))=>(k2_zfmisc_1(X1,X2)=k1_xboole_0|(r1_tarski(X1,X3)&r1_tarski(X2,X4))))), inference(assume_negation,[status(cth)],[t138_zfmisc_1])).
% 0.78/0.96  fof(c_0_9, plain, ![X19, X20]:(~r1_tarski(X19,X20)|k3_xboole_0(X19,X20)=X19), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.78/0.96  fof(c_0_10, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk6_0))&(k2_zfmisc_1(esk3_0,esk4_0)!=k1_xboole_0&(~r1_tarski(esk3_0,esk5_0)|~r1_tarski(esk4_0,esk6_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.78/0.96  fof(c_0_11, plain, ![X25, X26, X27, X28]:((~r1_xboole_0(X25,X26)|r1_xboole_0(k2_zfmisc_1(X25,X27),k2_zfmisc_1(X26,X28)))&(~r1_xboole_0(X27,X28)|r1_xboole_0(k2_zfmisc_1(X25,X27),k2_zfmisc_1(X26,X28)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t127_zfmisc_1])])])).
% 0.78/0.96  fof(c_0_12, plain, ![X21, X22, X23, X24]:k2_zfmisc_1(k3_xboole_0(X21,X22),k3_xboole_0(X23,X24))=k3_xboole_0(k2_zfmisc_1(X21,X23),k2_zfmisc_1(X22,X24)), inference(variable_rename,[status(thm)],[t123_zfmisc_1])).
% 0.78/0.96  fof(c_0_13, plain, ![X17, X18]:r1_tarski(k3_xboole_0(X17,X18),X17), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.78/0.96  fof(c_0_14, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.78/0.96  fof(c_0_15, plain, ![X29, X30, X31, X32]:((X29=X31|(X29=k1_xboole_0|X30=k1_xboole_0)|k2_zfmisc_1(X29,X30)!=k2_zfmisc_1(X31,X32))&(X30=X32|(X29=k1_xboole_0|X30=k1_xboole_0)|k2_zfmisc_1(X29,X30)!=k2_zfmisc_1(X31,X32))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t134_zfmisc_1])])])).
% 0.78/0.96  cnf(c_0_16, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.78/0.96  cnf(c_0_17, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.78/0.96  cnf(c_0_18, plain, (r1_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X4,X2))|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.78/0.96  cnf(c_0_19, plain, (k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4))=k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.78/0.96  fof(c_0_20, plain, ![X7, X8]:((~r1_xboole_0(X7,X8)|k3_xboole_0(X7,X8)=k1_xboole_0)&(k3_xboole_0(X7,X8)!=k1_xboole_0|r1_xboole_0(X7,X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.78/0.96  cnf(c_0_21, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.78/0.96  cnf(c_0_22, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.78/0.96  cnf(c_0_23, plain, (X1=X2|X3=k1_xboole_0|X1=k1_xboole_0|k2_zfmisc_1(X3,X1)!=k2_zfmisc_1(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.78/0.96  cnf(c_0_24, negated_conjecture, (k3_xboole_0(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk6_0))=k2_zfmisc_1(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.78/0.96  cnf(c_0_25, plain, (r1_xboole_0(k2_zfmisc_1(X1,X2),k3_xboole_0(k2_zfmisc_1(X3,X4),k2_zfmisc_1(X5,X6)))|~r1_xboole_0(X2,k3_xboole_0(X4,X6))), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.78/0.96  cnf(c_0_26, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.78/0.96  cnf(c_0_27, plain, (k3_xboole_0(X1,k3_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_21]), c_0_22])).
% 0.78/0.96  cnf(c_0_28, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|k3_xboole_0(X3,X4)=k1_xboole_0|k3_xboole_0(X1,X2)=X5|k3_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X4,X2))!=k2_zfmisc_1(X6,X5)), inference(spm,[status(thm)],[c_0_23, c_0_19])).
% 0.78/0.96  cnf(c_0_29, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_21, c_0_24])).
% 0.78/0.96  cnf(c_0_30, plain, (k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))=k3_xboole_0(k2_zfmisc_1(X3,X2),k2_zfmisc_1(X1,X4))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_22]), c_0_19])).
% 0.78/0.96  cnf(c_0_31, plain, (r1_tarski(k3_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.78/0.96  cnf(c_0_32, negated_conjecture, (r1_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(esk3_0,esk4_0))|~r1_xboole_0(X2,k3_xboole_0(esk4_0,esk6_0))), inference(spm,[status(thm)],[c_0_25, c_0_24])).
% 0.78/0.96  cnf(c_0_33, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,k3_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.78/0.96  cnf(c_0_34, negated_conjecture, (k2_zfmisc_1(esk3_0,esk4_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.78/0.96  cnf(c_0_35, negated_conjecture, (k3_xboole_0(esk3_0,esk5_0)=k1_xboole_0|k3_xboole_0(esk4_0,esk6_0)=k1_xboole_0|k3_xboole_0(esk4_0,esk6_0)=X1|k2_zfmisc_1(esk3_0,esk4_0)!=k2_zfmisc_1(X2,X1)), inference(spm,[status(thm)],[c_0_28, c_0_24])).
% 0.78/0.96  cnf(c_0_36, negated_conjecture, (k3_xboole_0(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk3_0,esk4_0))=k2_zfmisc_1(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_16, c_0_29])).
% 0.78/0.96  cnf(c_0_37, plain, (r1_tarski(k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)),k2_zfmisc_1(X3,X2))), inference(spm,[status(thm)],[c_0_21, c_0_30])).
% 0.78/0.96  cnf(c_0_38, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.78/0.96  cnf(c_0_39, plain, (k3_xboole_0(X1,k3_xboole_0(X2,X1))=k3_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_31]), c_0_22])).
% 0.78/0.96  cnf(c_0_40, negated_conjecture, (r1_xboole_0(k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)),k2_zfmisc_1(esk3_0,esk4_0))|~r1_xboole_0(k3_xboole_0(X2,X4),k3_xboole_0(esk4_0,esk6_0))), inference(spm,[status(thm)],[c_0_32, c_0_19])).
% 0.78/0.96  cnf(c_0_41, negated_conjecture, (~r1_xboole_0(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_24]), c_0_34])).
% 0.78/0.96  cnf(c_0_42, negated_conjecture, (k3_xboole_0(esk4_0,esk6_0)=esk4_0|k3_xboole_0(esk4_0,esk6_0)=k1_xboole_0|k3_xboole_0(esk3_0,esk5_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_35])).
% 0.78/0.96  cnf(c_0_43, plain, (X1=X2|X1=k1_xboole_0|X3=k1_xboole_0|k2_zfmisc_1(X1,X3)!=k2_zfmisc_1(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.78/0.96  cnf(c_0_44, negated_conjecture, (r1_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(esk3_0,esk4_0))|~r1_xboole_0(X2,k3_xboole_0(esk4_0,esk4_0))), inference(spm,[status(thm)],[c_0_25, c_0_36])).
% 0.78/0.96  cnf(c_0_45, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk4_0))), inference(spm,[status(thm)],[c_0_37, c_0_24])).
% 0.78/0.96  cnf(c_0_46, plain, (r1_xboole_0(X1,k3_xboole_0(X2,X1))|k3_xboole_0(X2,X1)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.78/0.96  cnf(c_0_47, negated_conjecture, (~r1_xboole_0(k3_xboole_0(esk4_0,esk6_0),k3_xboole_0(esk4_0,esk6_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_24]), c_0_41])).
% 0.78/0.96  cnf(c_0_48, negated_conjecture, (k3_xboole_0(esk3_0,esk5_0)=k1_xboole_0|k3_xboole_0(esk4_0,esk6_0)=k1_xboole_0|k3_xboole_0(esk4_0,esk4_0)=esk4_0), inference(spm,[status(thm)],[c_0_27, c_0_42])).
% 0.78/0.96  cnf(c_0_49, plain, (X1=k3_xboole_0(X2,X3)|X1=k1_xboole_0|X4=k1_xboole_0|k2_zfmisc_1(X1,X4)!=k3_xboole_0(k2_zfmisc_1(X2,X5),k2_zfmisc_1(X3,X6))), inference(spm,[status(thm)],[c_0_43, c_0_19])).
% 0.78/0.96  cnf(c_0_50, plain, (X1=k3_xboole_0(X2,X3)|X1=k1_xboole_0|X4=k1_xboole_0|k2_zfmisc_1(X4,X1)!=k3_xboole_0(k2_zfmisc_1(X5,X2),k2_zfmisc_1(X6,X3))), inference(spm,[status(thm)],[c_0_23, c_0_19])).
% 0.78/0.96  cnf(c_0_51, negated_conjecture, (r1_xboole_0(k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)),k2_zfmisc_1(esk3_0,esk4_0))|~r1_xboole_0(k3_xboole_0(X2,X4),k3_xboole_0(esk4_0,esk4_0))), inference(spm,[status(thm)],[c_0_44, c_0_19])).
% 0.78/0.96  cnf(c_0_52, negated_conjecture, (k3_xboole_0(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk4_0))=k2_zfmisc_1(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_16, c_0_45])).
% 0.78/0.96  cnf(c_0_53, plain, (r1_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X2))|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_46, c_0_27])).
% 0.78/0.96  cnf(c_0_54, negated_conjecture, (k3_xboole_0(esk4_0,esk4_0)=esk4_0|k3_xboole_0(esk3_0,esk5_0)=k1_xboole_0|~r1_xboole_0(k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.78/0.96  cnf(c_0_55, negated_conjecture, (X1=k3_xboole_0(esk3_0,esk5_0)|X2=k1_xboole_0|X1=k1_xboole_0|k2_zfmisc_1(X1,X2)!=k2_zfmisc_1(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_49, c_0_24])).
% 0.78/0.96  cnf(c_0_56, negated_conjecture, (X1=k3_xboole_0(esk4_0,esk6_0)|X2=k1_xboole_0|X1=k1_xboole_0|k2_zfmisc_1(X2,X1)!=k2_zfmisc_1(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_50, c_0_24])).
% 0.78/0.96  cnf(c_0_57, negated_conjecture, (~r1_xboole_0(k3_xboole_0(esk4_0,esk4_0),k3_xboole_0(esk4_0,esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_41])).
% 0.78/0.96  cnf(c_0_58, negated_conjecture, (k3_xboole_0(esk4_0,esk4_0)=esk4_0|k3_xboole_0(esk3_0,esk5_0)=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_48]), c_0_54])).
% 0.78/0.96  cnf(c_0_59, negated_conjecture, (k3_xboole_0(esk3_0,esk5_0)=esk3_0|esk3_0=k1_xboole_0|esk4_0=k1_xboole_0), inference(er,[status(thm)],[c_0_55])).
% 0.78/0.96  cnf(c_0_60, negated_conjecture, (k3_xboole_0(esk4_0,esk6_0)=esk4_0|esk4_0=k1_xboole_0|esk3_0=k1_xboole_0), inference(er,[status(thm)],[c_0_56])).
% 0.78/0.96  cnf(c_0_61, negated_conjecture, (k3_xboole_0(esk3_0,esk5_0)=k1_xboole_0|~r1_xboole_0(esk4_0,esk4_0)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.78/0.96  cnf(c_0_62, negated_conjecture, (~r1_tarski(esk3_0,esk5_0)|~r1_tarski(esk4_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.78/0.96  cnf(c_0_63, negated_conjecture, (esk4_0=k1_xboole_0|esk3_0=k1_xboole_0|r1_tarski(esk3_0,esk5_0)), inference(spm,[status(thm)],[c_0_31, c_0_59])).
% 0.78/0.96  cnf(c_0_64, negated_conjecture, (esk3_0=k1_xboole_0|esk4_0=k1_xboole_0|r1_tarski(esk4_0,esk6_0)), inference(spm,[status(thm)],[c_0_31, c_0_60])).
% 0.78/0.96  cnf(c_0_65, plain, (X1=k1_xboole_0|X2=k1_xboole_0|k2_zfmisc_1(X1,X2)!=k2_zfmisc_1(k1_xboole_0,X3)), inference(ef,[status(thm)],[c_0_43])).
% 0.78/0.96  cnf(c_0_66, plain, (r1_tarski(k3_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_31, c_0_27])).
% 0.78/0.96  cnf(c_0_67, negated_conjecture, (k3_xboole_0(esk3_0,esk5_0)=k1_xboole_0|esk4_0!=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_58]), c_0_61])).
% 0.78/0.96  cnf(c_0_68, negated_conjecture, (esk3_0=k1_xboole_0|esk4_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_64])).
% 0.78/0.96  cnf(c_0_69, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|k3_xboole_0(X3,X4)=k1_xboole_0|k3_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X4,X2))!=k2_zfmisc_1(k1_xboole_0,X5)), inference(spm,[status(thm)],[c_0_65, c_0_19])).
% 0.78/0.96  cnf(c_0_70, plain, (k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_16, c_0_66])).
% 0.78/0.96  cnf(c_0_71, negated_conjecture, (k3_xboole_0(esk3_0,esk5_0)=k1_xboole_0|esk3_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.78/0.96  cnf(c_0_72, negated_conjecture, (k3_xboole_0(esk3_0,esk5_0)=k1_xboole_0|k3_xboole_0(esk4_0,esk4_0)=k1_xboole_0|k2_zfmisc_1(esk3_0,esk4_0)!=k2_zfmisc_1(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_69, c_0_52])).
% 0.78/0.96  cnf(c_0_73, negated_conjecture, (esk3_0=k1_xboole_0|~r1_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k3_xboole_0(k1_xboole_0,k1_xboole_0))), inference(spm,[status(thm)],[c_0_57, c_0_68])).
% 0.78/0.96  cnf(c_0_74, negated_conjecture, (k3_xboole_0(k1_xboole_0,k1_xboole_0)=k1_xboole_0|esk3_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 0.78/0.96  cnf(c_0_75, negated_conjecture, (esk3_0=k1_xboole_0|r1_xboole_0(k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_53, c_0_71])).
% 0.78/0.96  cnf(c_0_76, negated_conjecture, (k3_xboole_0(esk3_0,esk5_0)=k1_xboole_0|k2_zfmisc_1(esk3_0,esk4_0)!=k2_zfmisc_1(k1_xboole_0,X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_58]), c_0_67])).
% 0.78/0.96  cnf(c_0_77, negated_conjecture, (esk3_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_75])).
% 0.78/0.96  cnf(c_0_78, negated_conjecture, (k3_xboole_0(k1_xboole_0,esk5_0)=k1_xboole_0|k2_zfmisc_1(k1_xboole_0,esk4_0)!=k2_zfmisc_1(k1_xboole_0,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76, c_0_77]), c_0_77])).
% 0.78/0.96  cnf(c_0_79, negated_conjecture, (k3_xboole_0(k1_xboole_0,esk5_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_78])).
% 0.78/0.96  cnf(c_0_80, negated_conjecture, (~r1_xboole_0(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_52]), c_0_34])).
% 0.78/0.96  cnf(c_0_81, plain, (r1_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.78/0.96  cnf(c_0_82, negated_conjecture, (r1_xboole_0(k1_xboole_0,esk5_0)), inference(spm,[status(thm)],[c_0_38, c_0_79])).
% 0.78/0.96  cnf(c_0_83, negated_conjecture, (~r1_xboole_0(k2_zfmisc_1(k1_xboole_0,esk4_0),k2_zfmisc_1(esk5_0,esk4_0))), inference(rw,[status(thm)],[c_0_80, c_0_77])).
% 0.78/0.96  cnf(c_0_84, negated_conjecture, (r1_xboole_0(k2_zfmisc_1(k1_xboole_0,X1),k2_zfmisc_1(esk5_0,X2))), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 0.78/0.96  cnf(c_0_85, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_83, c_0_84])]), ['proof']).
% 0.78/0.96  # SZS output end CNFRefutation
% 0.78/0.96  # Proof object total steps             : 86
% 0.78/0.96  # Proof object clause steps            : 69
% 0.78/0.96  # Proof object formula steps           : 17
% 0.78/0.96  # Proof object conjectures             : 46
% 0.78/0.96  # Proof object clause conjectures      : 43
% 0.78/0.96  # Proof object formula conjectures     : 3
% 0.78/0.96  # Proof object initial clauses used    : 13
% 0.78/0.96  # Proof object initial formulas used   : 8
% 0.78/0.96  # Proof object generating inferences   : 53
% 0.78/0.96  # Proof object simplifying inferences  : 17
% 0.78/0.96  # Training examples: 0 positive, 0 negative
% 0.78/0.96  # Parsed axioms                        : 10
% 0.78/0.96  # Removed by relevancy pruning/SinE    : 0
% 0.78/0.96  # Initial clauses                      : 16
% 0.78/0.96  # Removed in clause preprocessing      : 0
% 0.78/0.96  # Initial clauses in saturation        : 16
% 0.78/0.96  # Processed clauses                    : 6378
% 0.78/0.96  # ...of these trivial                  : 142
% 0.78/0.96  # ...subsumed                          : 4909
% 0.78/0.96  # ...remaining for further processing  : 1327
% 0.78/0.96  # Other redundant clauses eliminated   : 101
% 0.78/0.96  # Clauses deleted for lack of memory   : 0
% 0.78/0.96  # Backward-subsumed                    : 660
% 0.78/0.96  # Backward-rewritten                   : 482
% 0.78/0.96  # Generated clauses                    : 47360
% 0.78/0.96  # ...of the previous two non-trivial   : 45554
% 0.78/0.96  # Contextual simplify-reflections      : 19
% 0.78/0.96  # Paramodulations                      : 46862
% 0.78/0.96  # Factorizations                       : 359
% 0.78/0.96  # Equation resolutions                 : 137
% 0.78/0.96  # Propositional unsat checks           : 0
% 0.78/0.96  #    Propositional check models        : 0
% 0.78/0.96  #    Propositional check unsatisfiable : 0
% 0.78/0.96  #    Propositional clauses             : 0
% 0.78/0.96  #    Propositional clauses after purity: 0
% 0.78/0.96  #    Propositional unsat core size     : 0
% 0.78/0.96  #    Propositional preprocessing time  : 0.000
% 0.78/0.96  #    Propositional encoding time       : 0.000
% 0.78/0.96  #    Propositional solver time         : 0.000
% 0.78/0.96  #    Success case prop preproc time    : 0.000
% 0.78/0.96  #    Success case prop encoding time   : 0.000
% 0.78/0.96  #    Success case prop solver time     : 0.000
% 0.78/0.96  # Current number of processed clauses  : 167
% 0.78/0.96  #    Positive orientable unit clauses  : 33
% 0.78/0.96  #    Positive unorientable unit clauses: 7
% 0.78/0.96  #    Negative unit clauses             : 14
% 0.78/0.96  #    Non-unit-clauses                  : 113
% 0.78/0.96  # Current number of unprocessed clauses: 38933
% 0.78/0.96  # ...number of literals in the above   : 130681
% 0.78/0.96  # Current number of archived formulas  : 0
% 0.78/0.96  # Current number of archived clauses   : 1160
% 0.78/0.96  # Clause-clause subsumption calls (NU) : 122132
% 0.78/0.96  # Rec. Clause-clause subsumption calls : 43497
% 0.78/0.96  # Non-unit clause-clause subsumptions  : 5312
% 0.78/0.96  # Unit Clause-clause subsumption calls : 556
% 0.78/0.96  # Rewrite failures with RHS unbound    : 0
% 0.78/0.96  # BW rewrite match attempts            : 5331
% 0.78/0.96  # BW rewrite match successes           : 154
% 0.78/0.96  # Condensation attempts                : 0
% 0.78/0.96  # Condensation successes               : 0
% 0.78/0.96  # Termbank termtop insertions          : 963649
% 0.78/0.96  
% 0.78/0.96  # -------------------------------------------------
% 0.78/0.96  # User time                : 0.583 s
% 0.78/0.96  # System time              : 0.028 s
% 0.78/0.96  # Total time               : 0.611 s
% 0.78/0.96  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
