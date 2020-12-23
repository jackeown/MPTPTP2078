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
% DateTime   : Thu Dec  3 10:45:45 EST 2020

% Result     : Theorem 2.65s
% Output     : CNFRefutation 2.74s
% Verified   : 
% Statistics : Number of formulae       :  133 (13340 expanded)
%              Number of clauses        :  102 (6049 expanded)
%              Number of leaves         :   15 (3584 expanded)
%              Depth                    :   19
%              Number of atoms          :  194 (21233 expanded)
%              Number of equality atoms :  103 (10652 expanded)
%              Maximal formula depth    :   10 (   2 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t33_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => k3_subset_1(X1,k7_subset_1(X1,X2,X3)) = k4_subset_1(X1,k3_subset_1(X1,X2),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_subset_1)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t49_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t54_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k3_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(dt_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(X1))
           => k3_subset_1(X1,k7_subset_1(X1,X2,X3)) = k4_subset_1(X1,k3_subset_1(X1,X2),X3) ) ) ),
    inference(assume_negation,[status(cth)],[t33_subset_1])).

fof(c_0_16,plain,(
    ! [X31,X32,X33] :
      ( ~ m1_subset_1(X32,k1_zfmisc_1(X31))
      | ~ r2_hidden(X33,X32)
      | r2_hidden(X33,X31) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

fof(c_0_17,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))
    & m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))
    & k3_subset_1(esk2_0,k7_subset_1(esk2_0,esk3_0,esk4_0)) != k4_subset_1(esk2_0,k3_subset_1(esk2_0,esk3_0),esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

fof(c_0_18,plain,(
    ! [X14,X15] :
      ( ~ r1_tarski(X14,X15)
      | k3_xboole_0(X14,X15) = X14 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_19,plain,(
    ! [X16,X17] : k4_xboole_0(X16,k4_xboole_0(X16,X17)) = k3_xboole_0(X16,X17) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_20,plain,(
    ! [X8,X9,X10,X11,X12] :
      ( ( ~ r1_tarski(X8,X9)
        | ~ r2_hidden(X10,X8)
        | r2_hidden(X10,X9) )
      & ( r2_hidden(esk1_2(X11,X12),X11)
        | r1_tarski(X11,X12) )
      & ( ~ r2_hidden(esk1_2(X11,X12),X12)
        | r1_tarski(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_21,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_23,plain,(
    ! [X18,X19,X20] : k3_xboole_0(X18,k4_xboole_0(X19,X20)) = k4_xboole_0(k3_xboole_0(X18,X19),X20) ),
    inference(variable_rename,[status(thm)],[t49_xboole_1])).

cnf(c_0_24,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(X1,esk2_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

fof(c_0_30,plain,(
    ! [X6,X7] : k3_xboole_0(X6,X7) = k3_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_31,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(X1,esk2_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_28])).

fof(c_0_35,plain,(
    ! [X21,X22,X23] : k4_xboole_0(X21,k3_xboole_0(X22,X23)) = k2_xboole_0(k4_xboole_0(X21,X22),k4_xboole_0(X21,X23)) ),
    inference(variable_rename,[status(thm)],[t54_xboole_1])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk1_2(esk4_0,X1),esk2_0)
    | r1_tarski(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_27])).

cnf(c_0_37,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_25]),c_0_25])).

cnf(c_0_39,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk1_2(esk3_0,X1),esk2_0)
    | r1_tarski(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_27])).

cnf(c_0_41,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_36])).

cnf(c_0_43,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_25]),c_0_25])).

fof(c_0_44,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_45,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_40])).

cnf(c_0_47,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    inference(rw,[status(thm)],[c_0_41,c_0_25])).

cnf(c_0_48,negated_conjecture,
    ( k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk4_0)) = esk4_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_42]),c_0_43])).

cnf(c_0_49,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_50,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1))) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_45,c_0_43])).

cnf(c_0_51,negated_conjecture,
    ( k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0)) = esk3_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_46]),c_0_43])).

cnf(c_0_52,negated_conjecture,
    ( k4_xboole_0(esk2_0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(esk2_0,esk4_0)))) = k2_xboole_0(esk4_0,k4_xboole_0(esk2_0,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49])).

cnf(c_0_53,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X1,X3))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_43]),c_0_38])).

cnf(c_0_54,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_47,c_0_39])).

cnf(c_0_55,negated_conjecture,
    ( k4_xboole_0(esk4_0,esk4_0) = k4_xboole_0(esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_48])).

cnf(c_0_56,negated_conjecture,
    ( k4_xboole_0(esk2_0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(esk2_0,esk3_0)))) = k2_xboole_0(esk3_0,k4_xboole_0(esk2_0,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_51]),c_0_49])).

cnf(c_0_57,plain,
    ( k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1))),X3) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X1,X2),X3))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_43])).

cnf(c_0_58,negated_conjecture,
    ( k2_xboole_0(esk4_0,k4_xboole_0(esk2_0,X1)) = k4_xboole_0(esk2_0,k4_xboole_0(X1,esk4_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_45])).

cnf(c_0_59,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_54,c_0_39])).

cnf(c_0_60,negated_conjecture,
    ( k4_xboole_0(esk4_0,k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,X1))) = k4_xboole_0(esk4_0,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_55]),c_0_45]),c_0_47])).

cnf(c_0_61,negated_conjecture,
    ( k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,k4_xboole_0(esk4_0,X1))) = k4_xboole_0(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_48])).

cnf(c_0_62,negated_conjecture,
    ( k2_xboole_0(esk3_0,k4_xboole_0(esk2_0,X1)) = k4_xboole_0(esk2_0,k4_xboole_0(X1,esk3_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_53]),c_0_45])).

cnf(c_0_63,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X1,X2),X3))) = k4_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[c_0_57,c_0_50])).

cnf(c_0_64,negated_conjecture,
    ( k4_xboole_0(esk2_0,k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),esk4_0)) = k2_xboole_0(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_51]),c_0_49])).

cnf(c_0_65,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk3_0) = k4_xboole_0(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_66,negated_conjecture,
    ( k4_xboole_0(esk2_0,k4_xboole_0(k4_xboole_0(esk2_0,esk4_0),esk4_0)) = esk4_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_48]),c_0_59])).

cnf(c_0_67,negated_conjecture,
    ( k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,X1)) = k4_xboole_0(esk4_0,k4_xboole_0(esk2_0,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_60]),c_0_61])).

fof(c_0_68,plain,(
    ! [X24,X25] :
      ( ~ m1_subset_1(X25,k1_zfmisc_1(X24))
      | k3_subset_1(X24,X25) = k4_xboole_0(X24,X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

cnf(c_0_69,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X2,X3))) = k4_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_43]),c_0_50])).

cnf(c_0_70,negated_conjecture,
    ( k4_xboole_0(esk2_0,k4_xboole_0(k4_xboole_0(esk2_0,esk4_0),esk3_0)) = k2_xboole_0(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_48])).

cnf(c_0_71,negated_conjecture,
    ( k4_xboole_0(esk2_0,k2_xboole_0(esk3_0,esk4_0)) = k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_72,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,X1))) = k4_xboole_0(esk3_0,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_65]),c_0_45]),c_0_47])).

cnf(c_0_73,negated_conjecture,
    ( k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,k4_xboole_0(esk3_0,X1))) = k4_xboole_0(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_51])).

cnf(c_0_74,plain,
    ( k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),X3))) = k2_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X1)),k4_xboole_0(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_43])).

cnf(c_0_75,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),X3)) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X3,X2))) ),
    inference(spm,[status(thm)],[c_0_43,c_0_53])).

cnf(c_0_76,plain,
    ( k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(k4_xboole_0(X1,X1),X2))) = k2_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_39])).

cnf(c_0_77,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(esk2_0,esk4_0),esk4_0) = k4_xboole_0(esk2_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_66])).

cnf(c_0_78,negated_conjecture,
    ( k4_xboole_0(esk4_0,k4_xboole_0(esk2_0,esk4_0)) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_39,c_0_67])).

cnf(c_0_79,negated_conjecture,
    ( k3_subset_1(esk2_0,k7_subset_1(esk2_0,esk3_0,esk4_0)) != k4_subset_1(esk2_0,k3_subset_1(esk2_0,esk3_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_80,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_81,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X1,X1)))) = k2_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_39]),c_0_49])).

cnf(c_0_82,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_39]),c_0_49])).

cnf(c_0_83,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(esk2_0,esk4_0),esk3_0) = k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_70]),c_0_71])).

cnf(c_0_84,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,X1)) = k4_xboole_0(esk3_0,k4_xboole_0(esk2_0,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_72]),c_0_73])).

cnf(c_0_85,plain,
    ( k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X2,X3)) = k4_xboole_0(X2,k4_xboole_0(X3,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_75]),c_0_45])).

cnf(c_0_86,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_75]),c_0_45])).

cnf(c_0_87,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(esk2_0,esk4_0),k4_xboole_0(esk2_0,esk4_0)) = k4_xboole_0(esk4_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_77]),c_0_78]),c_0_55])).

cnf(c_0_88,negated_conjecture,
    ( k3_subset_1(esk2_0,k7_subset_1(esk2_0,esk3_0,esk4_0)) != k4_subset_1(esk2_0,k4_xboole_0(esk2_0,esk3_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_28])])).

fof(c_0_89,plain,(
    ! [X37,X38,X39] :
      ( ~ m1_subset_1(X38,k1_zfmisc_1(X37))
      | k7_subset_1(X37,X38,X39) = k4_xboole_0(X38,X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

fof(c_0_90,plain,(
    ! [X26,X27] :
      ( ~ m1_subset_1(X27,k1_zfmisc_1(X26))
      | m1_subset_1(k3_subset_1(X26,X27),k1_zfmisc_1(X26)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

cnf(c_0_91,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_53]),c_0_63]),c_0_45]),c_0_82])).

cnf(c_0_92,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(esk2_0,esk4_0),k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),esk4_0)) = k4_xboole_0(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_83]),c_0_84]),c_0_48])).

cnf(c_0_93,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,X1)))))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_43]),c_0_38])).

cnf(c_0_94,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(X1,esk3_0)) = k4_xboole_0(esk3_0,k4_xboole_0(X1,esk2_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_51]),c_0_86])).

cnf(c_0_95,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(esk2_0,esk4_0),esk2_0) = k4_xboole_0(esk4_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_48]),c_0_87])).

cnf(c_0_96,negated_conjecture,
    ( k4_xboole_0(esk2_0,k7_subset_1(esk2_0,esk3_0,esk4_0)) != k4_subset_1(esk2_0,k4_xboole_0(esk2_0,esk3_0),esk4_0)
    | ~ m1_subset_1(k7_subset_1(esk2_0,esk3_0,esk4_0),k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_88,c_0_80])).

cnf(c_0_97,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_89])).

fof(c_0_98,plain,(
    ! [X34,X35,X36] :
      ( ~ m1_subset_1(X35,k1_zfmisc_1(X34))
      | ~ m1_subset_1(X36,k1_zfmisc_1(X34))
      | k4_subset_1(X34,X35,X36) = k2_xboole_0(X35,X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

cnf(c_0_99,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_90])).

fof(c_0_100,plain,(
    ! [X40,X41,X42] :
      ( ~ m1_subset_1(X42,k1_zfmisc_1(X40))
      | k9_subset_1(X40,X41,X42) = k3_xboole_0(X41,X42) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

cnf(c_0_101,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X1,X3)))) = k4_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_53]),c_0_45])).

cnf(c_0_102,negated_conjecture,
    ( k4_xboole_0(X1,k4_xboole_0(esk4_0,k4_xboole_0(esk2_0,X1))) = k4_xboole_0(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_67])).

cnf(c_0_103,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(esk3_0,esk4_0),k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),esk4_0)) = k4_xboole_0(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_91,c_0_92])).

cnf(c_0_104,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X1))) = k4_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_39]),c_0_43]),c_0_45]),c_0_53]),c_0_63])).

cnf(c_0_105,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),esk4_0)) = k4_xboole_0(esk3_0,k4_xboole_0(esk4_0,esk2_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_83]),c_0_95])).

cnf(c_0_106,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,X3),X4))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X1,X3),X4))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_53]),c_0_38])).

cnf(c_0_107,negated_conjecture,
    ( k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,k4_xboole_0(k4_xboole_0(esk3_0,X1),X2))) = k4_xboole_0(k4_xboole_0(esk3_0,X1),X2) ),
    inference(spm,[status(thm)],[c_0_38,c_0_73])).

cnf(c_0_108,negated_conjecture,
    ( k4_subset_1(esk2_0,k4_xboole_0(esk2_0,esk3_0),esk4_0) != k4_xboole_0(esk2_0,k4_xboole_0(esk3_0,esk4_0))
    | ~ m1_subset_1(k4_xboole_0(esk3_0,esk4_0),k1_zfmisc_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_28])])).

cnf(c_0_109,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_98])).

cnf(c_0_110,plain,
    ( m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_99,c_0_80])).

fof(c_0_111,plain,(
    ! [X28,X29,X30] :
      ( ~ m1_subset_1(X30,k1_zfmisc_1(X28))
      | m1_subset_1(k9_subset_1(X28,X29,X30),k1_zfmisc_1(X28)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).

cnf(c_0_112,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_100])).

cnf(c_0_113,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),k4_xboole_0(esk2_0,esk4_0)) = k4_xboole_0(esk4_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_64]),c_0_71]),c_0_43]),c_0_67]),c_0_51])).

cnf(c_0_114,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),k4_xboole_0(esk4_0,esk3_0)) = k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_102,c_0_51])).

cnf(c_0_115,negated_conjecture,
    ( k4_xboole_0(esk4_0,k4_xboole_0(esk2_0,k4_xboole_0(esk3_0,esk4_0))) = k4_xboole_0(esk3_0,k2_xboole_0(esk3_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_103]),c_0_91]),c_0_84]),c_0_64]),c_0_104]),c_0_67])).

cnf(c_0_116,negated_conjecture,
    ( k4_xboole_0(esk3_0,k2_xboole_0(esk3_0,esk4_0)) = k4_xboole_0(esk3_0,k4_xboole_0(esk2_0,k4_xboole_0(esk4_0,esk2_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_105]),c_0_84]),c_0_64])).

cnf(c_0_117,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(esk2_0,k4_xboole_0(esk4_0,esk2_0))) = k4_xboole_0(k4_xboole_0(esk3_0,esk2_0),esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_105]),c_0_84]),c_0_65]),c_0_107])).

cnf(c_0_118,negated_conjecture,
    ( k2_xboole_0(esk4_0,k4_xboole_0(esk2_0,esk3_0)) != k4_xboole_0(esk2_0,k4_xboole_0(esk3_0,esk4_0))
    | ~ m1_subset_1(k4_xboole_0(esk3_0,esk4_0),k1_zfmisc_1(esk2_0))
    | ~ m1_subset_1(k4_xboole_0(esk2_0,esk3_0),k1_zfmisc_1(esk2_0)) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_109]),c_0_22])]),c_0_49])).

cnf(c_0_119,negated_conjecture,
    ( k2_xboole_0(esk4_0,k4_xboole_0(esk2_0,esk3_0)) = k4_xboole_0(esk2_0,k4_xboole_0(esk3_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_84]),c_0_48])).

cnf(c_0_120,plain,
    ( m1_subset_1(k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))),k1_zfmisc_1(k4_xboole_0(X1,k4_xboole_0(X1,X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_110,c_0_38])).

cnf(c_0_121,plain,
    ( m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_111])).

cnf(c_0_122,plain,
    ( k9_subset_1(X2,X3,X1) = k4_xboole_0(X3,k4_xboole_0(X3,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_112,c_0_25])).

cnf(c_0_123,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(esk2_0,esk4_0),k4_xboole_0(esk2_0,esk3_0)) = k4_xboole_0(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_113]),c_0_114]),c_0_92])).

cnf(c_0_124,negated_conjecture,
    ( k4_xboole_0(esk4_0,k4_xboole_0(esk2_0,k4_xboole_0(esk3_0,esk4_0))) = k4_xboole_0(k4_xboole_0(esk3_0,esk2_0),esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_115,c_0_116]),c_0_117])).

cnf(c_0_125,negated_conjecture,
    ( ~ m1_subset_1(k4_xboole_0(esk3_0,esk4_0),k1_zfmisc_1(esk2_0))
    | ~ m1_subset_1(k4_xboole_0(esk2_0,esk3_0),k1_zfmisc_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_118,c_0_119])])).

cnf(c_0_126,negated_conjecture,
    ( m1_subset_1(k4_xboole_0(esk2_0,esk3_0),k1_zfmisc_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_51]),c_0_39]),c_0_39]),c_0_28])])).

cnf(c_0_127,plain,
    ( m1_subset_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_121,c_0_122])).

cnf(c_0_128,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(esk3_0,esk4_0),esk3_0) = k4_xboole_0(k4_xboole_0(esk3_0,esk2_0),esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_123]),c_0_75]),c_0_107]),c_0_104]),c_0_67]),c_0_115]),c_0_116]),c_0_117])).

cnf(c_0_129,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(esk3_0,esk4_0),k4_xboole_0(k4_xboole_0(esk3_0,esk2_0),esk4_0)) = k4_xboole_0(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_124]),c_0_91])).

cnf(c_0_130,negated_conjecture,
    ( ~ m1_subset_1(k4_xboole_0(esk3_0,esk4_0),k1_zfmisc_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_125,c_0_126])])).

cnf(c_0_131,negated_conjecture,
    ( m1_subset_1(k4_xboole_0(esk3_0,esk4_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127,c_0_128]),c_0_129])).

cnf(c_0_132,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_130,c_0_131]),c_0_28])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:18:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 2.65/2.89  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 2.65/2.89  # and selection function SelectComplexExceptUniqMaxHorn.
% 2.65/2.89  #
% 2.65/2.89  # Preprocessing time       : 0.027 s
% 2.65/2.89  # Presaturation interreduction done
% 2.65/2.89  
% 2.65/2.89  # Proof found!
% 2.65/2.89  # SZS status Theorem
% 2.65/2.89  # SZS output start CNFRefutation
% 2.65/2.89  fof(t33_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k3_subset_1(X1,k7_subset_1(X1,X2,X3))=k4_subset_1(X1,k3_subset_1(X1,X2),X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_subset_1)).
% 2.65/2.89  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 2.65/2.89  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.65/2.89  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.65/2.89  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.65/2.89  fof(t49_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 2.65/2.89  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.65/2.89  fof(t54_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(X1,k3_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_xboole_1)).
% 2.65/2.89  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.65/2.89  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 2.65/2.89  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 2.65/2.89  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.65/2.89  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 2.65/2.89  fof(redefinition_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 2.65/2.89  fof(dt_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 2.65/2.89  fof(c_0_15, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k3_subset_1(X1,k7_subset_1(X1,X2,X3))=k4_subset_1(X1,k3_subset_1(X1,X2),X3)))), inference(assume_negation,[status(cth)],[t33_subset_1])).
% 2.65/2.89  fof(c_0_16, plain, ![X31, X32, X33]:(~m1_subset_1(X32,k1_zfmisc_1(X31))|(~r2_hidden(X33,X32)|r2_hidden(X33,X31))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 2.65/2.89  fof(c_0_17, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))&(m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))&k3_subset_1(esk2_0,k7_subset_1(esk2_0,esk3_0,esk4_0))!=k4_subset_1(esk2_0,k3_subset_1(esk2_0,esk3_0),esk4_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 2.65/2.89  fof(c_0_18, plain, ![X14, X15]:(~r1_tarski(X14,X15)|k3_xboole_0(X14,X15)=X14), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 2.65/2.89  fof(c_0_19, plain, ![X16, X17]:k4_xboole_0(X16,k4_xboole_0(X16,X17))=k3_xboole_0(X16,X17), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 2.65/2.89  fof(c_0_20, plain, ![X8, X9, X10, X11, X12]:((~r1_tarski(X8,X9)|(~r2_hidden(X10,X8)|r2_hidden(X10,X9)))&((r2_hidden(esk1_2(X11,X12),X11)|r1_tarski(X11,X12))&(~r2_hidden(esk1_2(X11,X12),X12)|r1_tarski(X11,X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 2.65/2.89  cnf(c_0_21, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 2.65/2.89  cnf(c_0_22, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 2.65/2.89  fof(c_0_23, plain, ![X18, X19, X20]:k3_xboole_0(X18,k4_xboole_0(X19,X20))=k4_xboole_0(k3_xboole_0(X18,X19),X20), inference(variable_rename,[status(thm)],[t49_xboole_1])).
% 2.65/2.89  cnf(c_0_24, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 2.65/2.89  cnf(c_0_25, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 2.65/2.89  cnf(c_0_26, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 2.65/2.89  cnf(c_0_27, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 2.65/2.89  cnf(c_0_28, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 2.65/2.89  cnf(c_0_29, negated_conjecture, (r2_hidden(X1,esk2_0)|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 2.65/2.89  fof(c_0_30, plain, ![X6, X7]:k3_xboole_0(X6,X7)=k3_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 2.65/2.89  cnf(c_0_31, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 2.65/2.89  cnf(c_0_32, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=X1|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_24, c_0_25])).
% 2.65/2.89  cnf(c_0_33, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 2.65/2.89  cnf(c_0_34, negated_conjecture, (r2_hidden(X1,esk2_0)|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_21, c_0_28])).
% 2.65/2.89  fof(c_0_35, plain, ![X21, X22, X23]:k4_xboole_0(X21,k3_xboole_0(X22,X23))=k2_xboole_0(k4_xboole_0(X21,X22),k4_xboole_0(X21,X23)), inference(variable_rename,[status(thm)],[t54_xboole_1])).
% 2.65/2.89  cnf(c_0_36, negated_conjecture, (r2_hidden(esk1_2(esk4_0,X1),esk2_0)|r1_tarski(esk4_0,X1)), inference(spm,[status(thm)],[c_0_29, c_0_27])).
% 2.65/2.89  cnf(c_0_37, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 2.65/2.89  cnf(c_0_38, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3)))=k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_25]), c_0_25])).
% 2.65/2.89  cnf(c_0_39, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X1))=X1), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 2.65/2.89  cnf(c_0_40, negated_conjecture, (r2_hidden(esk1_2(esk3_0,X1),esk2_0)|r1_tarski(esk3_0,X1)), inference(spm,[status(thm)],[c_0_34, c_0_27])).
% 2.65/2.89  cnf(c_0_41, plain, (k4_xboole_0(X1,k3_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 2.65/2.89  cnf(c_0_42, negated_conjecture, (r1_tarski(esk4_0,esk2_0)), inference(spm,[status(thm)],[c_0_26, c_0_36])).
% 2.65/2.89  cnf(c_0_43, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_25]), c_0_25])).
% 2.65/2.89  fof(c_0_44, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 2.65/2.89  cnf(c_0_45, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 2.65/2.89  cnf(c_0_46, negated_conjecture, (r1_tarski(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_26, c_0_40])).
% 2.65/2.89  cnf(c_0_47, plain, (k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3))), inference(rw,[status(thm)],[c_0_41, c_0_25])).
% 2.65/2.89  cnf(c_0_48, negated_conjecture, (k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk4_0))=esk4_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_42]), c_0_43])).
% 2.65/2.89  cnf(c_0_49, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 2.65/2.89  cnf(c_0_50, plain, (k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_45, c_0_43])).
% 2.65/2.89  cnf(c_0_51, negated_conjecture, (k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0))=esk3_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_46]), c_0_43])).
% 2.65/2.89  cnf(c_0_52, negated_conjecture, (k4_xboole_0(esk2_0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(esk2_0,esk4_0))))=k2_xboole_0(esk4_0,k4_xboole_0(esk2_0,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49])).
% 2.65/2.89  cnf(c_0_53, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3)))=k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X1,X3)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_43]), c_0_38])).
% 2.65/2.89  cnf(c_0_54, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_47, c_0_39])).
% 2.65/2.89  cnf(c_0_55, negated_conjecture, (k4_xboole_0(esk4_0,esk4_0)=k4_xboole_0(esk4_0,esk2_0)), inference(spm,[status(thm)],[c_0_50, c_0_48])).
% 2.65/2.89  cnf(c_0_56, negated_conjecture, (k4_xboole_0(esk2_0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(esk2_0,esk3_0))))=k2_xboole_0(esk3_0,k4_xboole_0(esk2_0,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_51]), c_0_49])).
% 2.65/2.89  cnf(c_0_57, plain, (k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1))),X3)=k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X1,X2),X3)))), inference(spm,[status(thm)],[c_0_38, c_0_43])).
% 2.65/2.89  cnf(c_0_58, negated_conjecture, (k2_xboole_0(esk4_0,k4_xboole_0(esk2_0,X1))=k4_xboole_0(esk2_0,k4_xboole_0(X1,esk4_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_45])).
% 2.65/2.89  cnf(c_0_59, plain, (k2_xboole_0(X1,X1)=X1), inference(spm,[status(thm)],[c_0_54, c_0_39])).
% 2.65/2.89  cnf(c_0_60, negated_conjecture, (k4_xboole_0(esk4_0,k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,X1)))=k4_xboole_0(esk4_0,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_55]), c_0_45]), c_0_47])).
% 2.65/2.89  cnf(c_0_61, negated_conjecture, (k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,k4_xboole_0(esk4_0,X1)))=k4_xboole_0(esk4_0,X1)), inference(spm,[status(thm)],[c_0_38, c_0_48])).
% 2.65/2.89  cnf(c_0_62, negated_conjecture, (k2_xboole_0(esk3_0,k4_xboole_0(esk2_0,X1))=k4_xboole_0(esk2_0,k4_xboole_0(X1,esk3_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_53]), c_0_45])).
% 2.65/2.89  cnf(c_0_63, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X1,X2),X3)))=k4_xboole_0(k4_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[c_0_57, c_0_50])).
% 2.65/2.89  cnf(c_0_64, negated_conjecture, (k4_xboole_0(esk2_0,k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),esk4_0))=k2_xboole_0(esk3_0,esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_51]), c_0_49])).
% 2.65/2.89  cnf(c_0_65, negated_conjecture, (k4_xboole_0(esk3_0,esk3_0)=k4_xboole_0(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 2.65/2.89  cnf(c_0_66, negated_conjecture, (k4_xboole_0(esk2_0,k4_xboole_0(k4_xboole_0(esk2_0,esk4_0),esk4_0))=esk4_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_48]), c_0_59])).
% 2.65/2.89  cnf(c_0_67, negated_conjecture, (k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,X1))=k4_xboole_0(esk4_0,k4_xboole_0(esk2_0,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_60]), c_0_61])).
% 2.65/2.89  fof(c_0_68, plain, ![X24, X25]:(~m1_subset_1(X25,k1_zfmisc_1(X24))|k3_subset_1(X24,X25)=k4_xboole_0(X24,X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 2.65/2.89  cnf(c_0_69, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X2,X3)))=k4_xboole_0(X1,k4_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_43]), c_0_50])).
% 2.65/2.89  cnf(c_0_70, negated_conjecture, (k4_xboole_0(esk2_0,k4_xboole_0(k4_xboole_0(esk2_0,esk4_0),esk3_0))=k2_xboole_0(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_62, c_0_48])).
% 2.65/2.89  cnf(c_0_71, negated_conjecture, (k4_xboole_0(esk2_0,k2_xboole_0(esk3_0,esk4_0))=k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),esk4_0)), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 2.65/2.89  cnf(c_0_72, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,X1)))=k4_xboole_0(esk3_0,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_65]), c_0_45]), c_0_47])).
% 2.65/2.89  cnf(c_0_73, negated_conjecture, (k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,k4_xboole_0(esk3_0,X1)))=k4_xboole_0(esk3_0,X1)), inference(spm,[status(thm)],[c_0_38, c_0_51])).
% 2.65/2.89  cnf(c_0_74, plain, (k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),X3)))=k2_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X1)),k4_xboole_0(X1,X3))), inference(spm,[status(thm)],[c_0_47, c_0_43])).
% 2.65/2.89  cnf(c_0_75, plain, (k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),X3))=k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X3,X2)))), inference(spm,[status(thm)],[c_0_43, c_0_53])).
% 2.65/2.89  cnf(c_0_76, plain, (k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(k4_xboole_0(X1,X1),X2)))=k2_xboole_0(X1,k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_47, c_0_39])).
% 2.65/2.89  cnf(c_0_77, negated_conjecture, (k4_xboole_0(k4_xboole_0(esk2_0,esk4_0),esk4_0)=k4_xboole_0(esk2_0,esk4_0)), inference(spm,[status(thm)],[c_0_63, c_0_66])).
% 2.65/2.89  cnf(c_0_78, negated_conjecture, (k4_xboole_0(esk4_0,k4_xboole_0(esk2_0,esk4_0))=esk4_0), inference(spm,[status(thm)],[c_0_39, c_0_67])).
% 2.65/2.89  cnf(c_0_79, negated_conjecture, (k3_subset_1(esk2_0,k7_subset_1(esk2_0,esk3_0,esk4_0))!=k4_subset_1(esk2_0,k3_subset_1(esk2_0,esk3_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 2.65/2.89  cnf(c_0_80, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_68])).
% 2.65/2.89  cnf(c_0_81, plain, (k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X1,X1))))=k2_xboole_0(X1,k4_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_39]), c_0_49])).
% 2.65/2.89  cnf(c_0_82, plain, (k2_xboole_0(X1,k4_xboole_0(X1,X1))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_39]), c_0_49])).
% 2.65/2.89  cnf(c_0_83, negated_conjecture, (k4_xboole_0(k4_xboole_0(esk2_0,esk4_0),esk3_0)=k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_70]), c_0_71])).
% 2.65/2.89  cnf(c_0_84, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,X1))=k4_xboole_0(esk3_0,k4_xboole_0(esk2_0,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_72]), c_0_73])).
% 2.65/2.89  cnf(c_0_85, plain, (k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X2,X3))=k4_xboole_0(X2,k4_xboole_0(X3,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74, c_0_75]), c_0_45])).
% 2.65/2.89  cnf(c_0_86, plain, (k2_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X1,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76, c_0_75]), c_0_45])).
% 2.65/2.89  cnf(c_0_87, negated_conjecture, (k4_xboole_0(k4_xboole_0(esk2_0,esk4_0),k4_xboole_0(esk2_0,esk4_0))=k4_xboole_0(esk4_0,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_77]), c_0_78]), c_0_55])).
% 2.65/2.89  cnf(c_0_88, negated_conjecture, (k3_subset_1(esk2_0,k7_subset_1(esk2_0,esk3_0,esk4_0))!=k4_subset_1(esk2_0,k4_xboole_0(esk2_0,esk3_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_28])])).
% 2.65/2.89  fof(c_0_89, plain, ![X37, X38, X39]:(~m1_subset_1(X38,k1_zfmisc_1(X37))|k7_subset_1(X37,X38,X39)=k4_xboole_0(X38,X39)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 2.65/2.89  fof(c_0_90, plain, ![X26, X27]:(~m1_subset_1(X27,k1_zfmisc_1(X26))|m1_subset_1(k3_subset_1(X26,X27),k1_zfmisc_1(X26))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 2.65/2.89  cnf(c_0_91, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_53]), c_0_63]), c_0_45]), c_0_82])).
% 2.65/2.89  cnf(c_0_92, negated_conjecture, (k4_xboole_0(k4_xboole_0(esk2_0,esk4_0),k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),esk4_0))=k4_xboole_0(esk3_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_83]), c_0_84]), c_0_48])).
% 2.65/2.89  cnf(c_0_93, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))))=k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,X1))))))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_43]), c_0_38])).
% 2.65/2.89  cnf(c_0_94, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(X1,esk3_0))=k4_xboole_0(esk3_0,k4_xboole_0(X1,esk2_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_51]), c_0_86])).
% 2.65/2.89  cnf(c_0_95, negated_conjecture, (k4_xboole_0(k4_xboole_0(esk2_0,esk4_0),esk2_0)=k4_xboole_0(esk4_0,esk2_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_48]), c_0_87])).
% 2.65/2.89  cnf(c_0_96, negated_conjecture, (k4_xboole_0(esk2_0,k7_subset_1(esk2_0,esk3_0,esk4_0))!=k4_subset_1(esk2_0,k4_xboole_0(esk2_0,esk3_0),esk4_0)|~m1_subset_1(k7_subset_1(esk2_0,esk3_0,esk4_0),k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_88, c_0_80])).
% 2.65/2.89  cnf(c_0_97, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_89])).
% 2.65/2.89  fof(c_0_98, plain, ![X34, X35, X36]:(~m1_subset_1(X35,k1_zfmisc_1(X34))|~m1_subset_1(X36,k1_zfmisc_1(X34))|k4_subset_1(X34,X35,X36)=k2_xboole_0(X35,X36)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 2.65/2.89  cnf(c_0_99, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_90])).
% 2.65/2.89  fof(c_0_100, plain, ![X40, X41, X42]:(~m1_subset_1(X42,k1_zfmisc_1(X40))|k9_subset_1(X40,X41,X42)=k3_xboole_0(X41,X42)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).
% 2.65/2.89  cnf(c_0_101, plain, (k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X1,X3))))=k4_xboole_0(X1,k4_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_53]), c_0_45])).
% 2.65/2.89  cnf(c_0_102, negated_conjecture, (k4_xboole_0(X1,k4_xboole_0(esk4_0,k4_xboole_0(esk2_0,X1)))=k4_xboole_0(X1,esk4_0)), inference(spm,[status(thm)],[c_0_50, c_0_67])).
% 2.65/2.89  cnf(c_0_103, negated_conjecture, (k4_xboole_0(k4_xboole_0(esk3_0,esk4_0),k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),esk4_0))=k4_xboole_0(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_91, c_0_92])).
% 2.65/2.89  cnf(c_0_104, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X1)))=k4_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_39]), c_0_43]), c_0_45]), c_0_53]), c_0_63])).
% 2.65/2.89  cnf(c_0_105, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),esk4_0))=k4_xboole_0(esk3_0,k4_xboole_0(esk4_0,esk2_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_83]), c_0_95])).
% 2.65/2.89  cnf(c_0_106, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,X3),X4)))=k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X1,X3),X4)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_53]), c_0_38])).
% 2.65/2.89  cnf(c_0_107, negated_conjecture, (k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,k4_xboole_0(k4_xboole_0(esk3_0,X1),X2)))=k4_xboole_0(k4_xboole_0(esk3_0,X1),X2)), inference(spm,[status(thm)],[c_0_38, c_0_73])).
% 2.65/2.89  cnf(c_0_108, negated_conjecture, (k4_subset_1(esk2_0,k4_xboole_0(esk2_0,esk3_0),esk4_0)!=k4_xboole_0(esk2_0,k4_xboole_0(esk3_0,esk4_0))|~m1_subset_1(k4_xboole_0(esk3_0,esk4_0),k1_zfmisc_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_97]), c_0_28])])).
% 2.65/2.89  cnf(c_0_109, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_98])).
% 2.65/2.89  cnf(c_0_110, plain, (m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_99, c_0_80])).
% 2.65/2.89  fof(c_0_111, plain, ![X28, X29, X30]:(~m1_subset_1(X30,k1_zfmisc_1(X28))|m1_subset_1(k9_subset_1(X28,X29,X30),k1_zfmisc_1(X28))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).
% 2.65/2.89  cnf(c_0_112, plain, (k9_subset_1(X2,X3,X1)=k3_xboole_0(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_100])).
% 2.65/2.89  cnf(c_0_113, negated_conjecture, (k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),k4_xboole_0(esk2_0,esk4_0))=k4_xboole_0(esk4_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_64]), c_0_71]), c_0_43]), c_0_67]), c_0_51])).
% 2.65/2.89  cnf(c_0_114, negated_conjecture, (k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),k4_xboole_0(esk4_0,esk3_0))=k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),esk4_0)), inference(spm,[status(thm)],[c_0_102, c_0_51])).
% 2.65/2.89  cnf(c_0_115, negated_conjecture, (k4_xboole_0(esk4_0,k4_xboole_0(esk2_0,k4_xboole_0(esk3_0,esk4_0)))=k4_xboole_0(esk3_0,k2_xboole_0(esk3_0,esk4_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_103]), c_0_91]), c_0_84]), c_0_64]), c_0_104]), c_0_67])).
% 2.65/2.89  cnf(c_0_116, negated_conjecture, (k4_xboole_0(esk3_0,k2_xboole_0(esk3_0,esk4_0))=k4_xboole_0(esk3_0,k4_xboole_0(esk2_0,k4_xboole_0(esk4_0,esk2_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_105]), c_0_84]), c_0_64])).
% 2.65/2.89  cnf(c_0_117, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk2_0,k4_xboole_0(esk4_0,esk2_0)))=k4_xboole_0(k4_xboole_0(esk3_0,esk2_0),esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_105]), c_0_84]), c_0_65]), c_0_107])).
% 2.65/2.89  cnf(c_0_118, negated_conjecture, (k2_xboole_0(esk4_0,k4_xboole_0(esk2_0,esk3_0))!=k4_xboole_0(esk2_0,k4_xboole_0(esk3_0,esk4_0))|~m1_subset_1(k4_xboole_0(esk3_0,esk4_0),k1_zfmisc_1(esk2_0))|~m1_subset_1(k4_xboole_0(esk2_0,esk3_0),k1_zfmisc_1(esk2_0))), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_109]), c_0_22])]), c_0_49])).
% 2.65/2.89  cnf(c_0_119, negated_conjecture, (k2_xboole_0(esk4_0,k4_xboole_0(esk2_0,esk3_0))=k4_xboole_0(esk2_0,k4_xboole_0(esk3_0,esk4_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_84]), c_0_48])).
% 2.65/2.89  cnf(c_0_120, plain, (m1_subset_1(k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))),k1_zfmisc_1(k4_xboole_0(X1,k4_xboole_0(X1,X2))))|~m1_subset_1(X3,k1_zfmisc_1(k4_xboole_0(X1,k4_xboole_0(X1,X2))))), inference(spm,[status(thm)],[c_0_110, c_0_38])).
% 2.65/2.89  cnf(c_0_121, plain, (m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_111])).
% 2.65/2.89  cnf(c_0_122, plain, (k9_subset_1(X2,X3,X1)=k4_xboole_0(X3,k4_xboole_0(X3,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_112, c_0_25])).
% 2.65/2.89  cnf(c_0_123, negated_conjecture, (k4_xboole_0(k4_xboole_0(esk2_0,esk4_0),k4_xboole_0(esk2_0,esk3_0))=k4_xboole_0(esk3_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_113]), c_0_114]), c_0_92])).
% 2.65/2.89  cnf(c_0_124, negated_conjecture, (k4_xboole_0(esk4_0,k4_xboole_0(esk2_0,k4_xboole_0(esk3_0,esk4_0)))=k4_xboole_0(k4_xboole_0(esk3_0,esk2_0),esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_115, c_0_116]), c_0_117])).
% 2.65/2.89  cnf(c_0_125, negated_conjecture, (~m1_subset_1(k4_xboole_0(esk3_0,esk4_0),k1_zfmisc_1(esk2_0))|~m1_subset_1(k4_xboole_0(esk2_0,esk3_0),k1_zfmisc_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_118, c_0_119])])).
% 2.65/2.89  cnf(c_0_126, negated_conjecture, (m1_subset_1(k4_xboole_0(esk2_0,esk3_0),k1_zfmisc_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120, c_0_51]), c_0_39]), c_0_39]), c_0_28])])).
% 2.65/2.89  cnf(c_0_127, plain, (m1_subset_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k1_zfmisc_1(X3))|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_121, c_0_122])).
% 2.65/2.89  cnf(c_0_128, negated_conjecture, (k4_xboole_0(k4_xboole_0(esk3_0,esk4_0),esk3_0)=k4_xboole_0(k4_xboole_0(esk3_0,esk2_0),esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_123]), c_0_75]), c_0_107]), c_0_104]), c_0_67]), c_0_115]), c_0_116]), c_0_117])).
% 2.74/2.89  cnf(c_0_129, negated_conjecture, (k4_xboole_0(k4_xboole_0(esk3_0,esk4_0),k4_xboole_0(k4_xboole_0(esk3_0,esk2_0),esk4_0))=k4_xboole_0(esk3_0,esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_124]), c_0_91])).
% 2.74/2.89  cnf(c_0_130, negated_conjecture, (~m1_subset_1(k4_xboole_0(esk3_0,esk4_0),k1_zfmisc_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_125, c_0_126])])).
% 2.74/2.89  cnf(c_0_131, negated_conjecture, (m1_subset_1(k4_xboole_0(esk3_0,esk4_0),k1_zfmisc_1(X1))|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127, c_0_128]), c_0_129])).
% 2.74/2.89  cnf(c_0_132, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_130, c_0_131]), c_0_28])]), ['proof']).
% 2.74/2.89  # SZS output end CNFRefutation
% 2.74/2.89  # Proof object total steps             : 133
% 2.74/2.89  # Proof object clause steps            : 102
% 2.74/2.89  # Proof object formula steps           : 31
% 2.74/2.89  # Proof object conjectures             : 60
% 2.74/2.89  # Proof object clause conjectures      : 57
% 2.74/2.89  # Proof object formula conjectures     : 3
% 2.74/2.89  # Proof object initial clauses used    : 18
% 2.74/2.89  # Proof object initial formulas used   : 15
% 2.74/2.89  # Proof object generating inferences   : 73
% 2.74/2.89  # Proof object simplifying inferences  : 93
% 2.74/2.89  # Training examples: 0 positive, 0 negative
% 2.74/2.89  # Parsed axioms                        : 15
% 2.74/2.89  # Removed by relevancy pruning/SinE    : 0
% 2.74/2.89  # Initial clauses                      : 19
% 2.74/2.89  # Removed in clause preprocessing      : 1
% 2.74/2.89  # Initial clauses in saturation        : 18
% 2.74/2.89  # Processed clauses                    : 4209
% 2.74/2.89  # ...of these trivial                  : 196
% 2.74/2.89  # ...subsumed                          : 3143
% 2.74/2.89  # ...remaining for further processing  : 870
% 2.74/2.89  # Other redundant clauses eliminated   : 0
% 2.74/2.89  # Clauses deleted for lack of memory   : 0
% 2.74/2.89  # Backward-subsumed                    : 49
% 2.74/2.89  # Backward-rewritten                   : 286
% 2.74/2.89  # Generated clauses                    : 208063
% 2.74/2.89  # ...of the previous two non-trivial   : 199255
% 2.74/2.89  # Contextual simplify-reflections      : 0
% 2.74/2.89  # Paramodulations                      : 208063
% 2.74/2.89  # Factorizations                       : 0
% 2.74/2.89  # Equation resolutions                 : 0
% 2.74/2.89  # Propositional unsat checks           : 0
% 2.74/2.89  #    Propositional check models        : 0
% 2.74/2.89  #    Propositional check unsatisfiable : 0
% 2.74/2.89  #    Propositional clauses             : 0
% 2.74/2.89  #    Propositional clauses after purity: 0
% 2.74/2.89  #    Propositional unsat core size     : 0
% 2.74/2.89  #    Propositional preprocessing time  : 0.000
% 2.74/2.89  #    Propositional encoding time       : 0.000
% 2.74/2.89  #    Propositional solver time         : 0.000
% 2.74/2.89  #    Success case prop preproc time    : 0.000
% 2.74/2.89  #    Success case prop encoding time   : 0.000
% 2.74/2.89  #    Success case prop solver time     : 0.000
% 2.74/2.89  # Current number of processed clauses  : 517
% 2.74/2.89  #    Positive orientable unit clauses  : 149
% 2.74/2.89  #    Positive unorientable unit clauses: 36
% 2.74/2.89  #    Negative unit clauses             : 6
% 2.74/2.89  #    Non-unit-clauses                  : 326
% 2.74/2.89  # Current number of unprocessed clauses: 194712
% 2.74/2.89  # ...number of literals in the above   : 320435
% 2.74/2.89  # Current number of archived formulas  : 0
% 2.74/2.89  # Current number of archived clauses   : 354
% 2.74/2.89  # Clause-clause subsumption calls (NU) : 73549
% 2.74/2.89  # Rec. Clause-clause subsumption calls : 60347
% 2.74/2.89  # Non-unit clause-clause subsumptions  : 3136
% 2.74/2.89  # Unit Clause-clause subsumption calls : 3473
% 2.74/2.89  # Rewrite failures with RHS unbound    : 0
% 2.74/2.89  # BW rewrite match attempts            : 24920
% 2.74/2.89  # BW rewrite match successes           : 649
% 2.74/2.89  # Condensation attempts                : 0
% 2.74/2.89  # Condensation successes               : 0
% 2.74/2.89  # Termbank termtop insertions          : 5701569
% 2.74/2.90  
% 2.74/2.90  # -------------------------------------------------
% 2.74/2.90  # User time                : 2.424 s
% 2.74/2.90  # System time              : 0.127 s
% 2.74/2.90  # Total time               : 2.551 s
% 2.74/2.90  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
