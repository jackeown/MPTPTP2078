%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:47:38 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 269 expanded)
%              Number of clauses        :   38 ( 116 expanded)
%              Number of leaves         :   14 (  67 expanded)
%              Depth                    :   10
%              Number of atoms          :  157 ( 682 expanded)
%              Number of equality atoms :   55 ( 312 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(dt_k6_subset_1,axiom,(
    ! [X1,X2] : m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(d8_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
         => ( X3 = k7_setfam_1(X1,X2)
          <=> ! [X4] :
                ( m1_subset_1(X4,k1_zfmisc_1(X1))
               => ( r2_hidden(X4,X3)
                <=> r2_hidden(k3_subset_1(X1,X4),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_setfam_1)).

fof(dt_k7_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => m1_subset_1(k7_setfam_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_setfam_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t46_setfam_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ~ ( X2 != k1_xboole_0
          & k7_setfam_1(X1,X2) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_setfam_1)).

fof(t152_zfmisc_1,axiom,(
    ! [X1,X2] : ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(c_0_14,plain,(
    ! [X7,X8] : k4_xboole_0(X7,k4_xboole_0(X7,X8)) = k3_xboole_0(X7,X8) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_15,plain,(
    ! [X28,X29] : k1_setfam_1(k2_tarski(X28,X29)) = k3_xboole_0(X28,X29) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_16,plain,(
    ! [X17,X18] : m1_subset_1(k6_subset_1(X17,X18),k1_zfmisc_1(X17)) ),
    inference(variable_rename,[status(thm)],[dt_k6_subset_1])).

fof(c_0_17,plain,(
    ! [X19,X20] : k6_subset_1(X19,X20) = k4_xboole_0(X19,X20) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

fof(c_0_18,plain,(
    ! [X21,X22,X23,X24] :
      ( ( ~ r2_hidden(X24,X23)
        | r2_hidden(k3_subset_1(X21,X24),X22)
        | ~ m1_subset_1(X24,k1_zfmisc_1(X21))
        | X23 != k7_setfam_1(X21,X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k1_zfmisc_1(X21)))
        | ~ m1_subset_1(X22,k1_zfmisc_1(k1_zfmisc_1(X21))) )
      & ( ~ r2_hidden(k3_subset_1(X21,X24),X22)
        | r2_hidden(X24,X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(X21))
        | X23 != k7_setfam_1(X21,X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k1_zfmisc_1(X21)))
        | ~ m1_subset_1(X22,k1_zfmisc_1(k1_zfmisc_1(X21))) )
      & ( m1_subset_1(esk1_3(X21,X22,X23),k1_zfmisc_1(X21))
        | X23 = k7_setfam_1(X21,X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k1_zfmisc_1(X21)))
        | ~ m1_subset_1(X22,k1_zfmisc_1(k1_zfmisc_1(X21))) )
      & ( ~ r2_hidden(esk1_3(X21,X22,X23),X23)
        | ~ r2_hidden(k3_subset_1(X21,esk1_3(X21,X22,X23)),X22)
        | X23 = k7_setfam_1(X21,X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k1_zfmisc_1(X21)))
        | ~ m1_subset_1(X22,k1_zfmisc_1(k1_zfmisc_1(X21))) )
      & ( r2_hidden(esk1_3(X21,X22,X23),X23)
        | r2_hidden(k3_subset_1(X21,esk1_3(X21,X22,X23)),X22)
        | X23 = k7_setfam_1(X21,X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k1_zfmisc_1(X21)))
        | ~ m1_subset_1(X22,k1_zfmisc_1(k1_zfmisc_1(X21))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_setfam_1])])])])])).

fof(c_0_19,plain,(
    ! [X26,X27] :
      ( ~ m1_subset_1(X27,k1_zfmisc_1(k1_zfmisc_1(X26)))
      | m1_subset_1(k7_setfam_1(X26,X27),k1_zfmisc_1(k1_zfmisc_1(X26))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_setfam_1])])).

fof(c_0_20,plain,(
    ! [X15,X16] :
      ( ~ m1_subset_1(X16,k1_zfmisc_1(X15))
      | k3_subset_1(X15,X16) = k4_xboole_0(X15,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

cnf(c_0_21,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_25,plain,(
    ! [X11,X12] :
      ( ( k2_zfmisc_1(X11,X12) != k1_xboole_0
        | X11 = k1_xboole_0
        | X12 = k1_xboole_0 )
      & ( X11 != k1_xboole_0
        | k2_zfmisc_1(X11,X12) = k1_xboole_0 )
      & ( X12 != k1_xboole_0
        | k2_zfmisc_1(X11,X12) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_26,plain,(
    ! [X5,X6] :
      ( ~ r1_tarski(X5,X6)
      | k3_xboole_0(X5,X6) = X5 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_27,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
       => ~ ( X2 != k1_xboole_0
            & k7_setfam_1(X1,X2) = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t46_setfam_1])).

cnf(c_0_28,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k3_subset_1(X1,X2),X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | X4 != k7_setfam_1(X1,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,plain,
    ( m1_subset_1(k7_setfam_1(X2,X1),k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_setfam_1(k2_tarski(X1,X2)) ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_32,plain,
    ( m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

fof(c_0_33,plain,(
    ! [X13,X14] : ~ r2_hidden(X13,k2_zfmisc_1(X13,X14)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).

cnf(c_0_34,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_36,plain,(
    ! [X9,X10] : k2_tarski(X9,X10) = k2_tarski(X10,X9) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

fof(c_0_37,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))
    & esk3_0 != k1_xboole_0
    & k7_setfam_1(esk2_0,esk3_0) = k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_27])])])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,k7_setfam_1(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(k3_subset_1(X2,X1),X3) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_28]),c_0_29])).

cnf(c_0_39,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_subset_1(X1,k4_xboole_0(X1,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])])).

cnf(c_0_40,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_34])).

cnf(c_0_42,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_35,c_0_22])).

cnf(c_0_43,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_44,negated_conjecture,
    ( k7_setfam_1(esk2_0,esk3_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_46,plain,
    ( r2_hidden(k4_xboole_0(X1,X2),k7_setfam_1(X1,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ r2_hidden(k1_setfam_1(k2_tarski(X1,X2)),X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_32])])).

cnf(c_0_47,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_48,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_49,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(k3_subset_1(X1,esk1_3(X1,X2,X3)),X2)
    | X3 = k7_setfam_1(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_50,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_44]),c_0_45])])).

cnf(c_0_51,negated_conjecture,
    ( ~ r2_hidden(k3_subset_1(esk2_0,k4_xboole_0(esk2_0,X1)),esk3_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_45]),c_0_44]),c_0_39]),c_0_47])).

cnf(c_0_52,plain,
    ( k3_subset_1(X1,k4_xboole_0(X1,X2)) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_39])).

fof(c_0_53,plain,(
    ! [X30,X31] :
      ( ( ~ m1_subset_1(X30,k1_zfmisc_1(X31))
        | r1_tarski(X30,X31) )
      & ( ~ r1_tarski(X30,X31)
        | m1_subset_1(X30,k1_zfmisc_1(X31)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_54,negated_conjecture,
    ( k7_setfam_1(esk2_0,X1) = k1_xboole_0
    | r2_hidden(k3_subset_1(esk2_0,esk1_3(esk2_0,X1,k1_xboole_0)),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(esk2_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_47])).

cnf(c_0_55,negated_conjecture,
    ( ~ r2_hidden(X1,esk3_0)
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_56,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_57,negated_conjecture,
    ( k7_setfam_1(esk2_0,X1) = esk3_0
    | r2_hidden(k3_subset_1(esk2_0,esk1_3(esk2_0,X1,esk3_0)),X1)
    | r2_hidden(esk1_3(esk2_0,X1,esk3_0),esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_49,c_0_45])).

cnf(c_0_58,negated_conjecture,
    ( k7_setfam_1(esk2_0,k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_54]),c_0_50])])).

cnf(c_0_59,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_60,plain,(
    ! [X32,X33,X34] :
      ( ~ r2_hidden(X32,X33)
      | ~ m1_subset_1(X33,k1_zfmisc_1(X34))
      | m1_subset_1(X32,X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_61,negated_conjecture,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(esk2_0))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(esk1_3(esk2_0,k1_xboole_0,esk3_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_57]),c_0_58]),c_0_50])]),c_0_59])).

cnf(c_0_63,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_64,negated_conjecture,
    ( ~ m1_subset_1(esk1_3(esk2_0,k1_xboole_0,esk3_0),k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_65,negated_conjecture,
    ( m1_subset_1(esk1_3(esk2_0,k1_xboole_0,esk3_0),X1)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_62])).

cnf(c_0_66,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_45])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:46:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.47  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S05BN
% 0.19/0.47  # and selection function SelectUnlessUniqMaxSmallestOrientable.
% 0.19/0.47  #
% 0.19/0.47  # Preprocessing time       : 0.027 s
% 0.19/0.47  # Presaturation interreduction done
% 0.19/0.47  
% 0.19/0.47  # Proof found!
% 0.19/0.47  # SZS status Theorem
% 0.19/0.47  # SZS output start CNFRefutation
% 0.19/0.47  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.19/0.47  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.19/0.47  fof(dt_k6_subset_1, axiom, ![X1, X2]:m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 0.19/0.47  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 0.19/0.47  fof(d8_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(X3=k7_setfam_1(X1,X2)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(X1))=>(r2_hidden(X4,X3)<=>r2_hidden(k3_subset_1(X1,X4),X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_setfam_1)).
% 0.19/0.47  fof(dt_k7_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>m1_subset_1(k7_setfam_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_setfam_1)).
% 0.19/0.47  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 0.19/0.47  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.19/0.47  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.19/0.47  fof(t46_setfam_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>~((X2!=k1_xboole_0&k7_setfam_1(X1,X2)=k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_setfam_1)).
% 0.19/0.47  fof(t152_zfmisc_1, axiom, ![X1, X2]:~(r2_hidden(X1,k2_zfmisc_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 0.19/0.47  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.19/0.47  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.47  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 0.19/0.47  fof(c_0_14, plain, ![X7, X8]:k4_xboole_0(X7,k4_xboole_0(X7,X8))=k3_xboole_0(X7,X8), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.19/0.47  fof(c_0_15, plain, ![X28, X29]:k1_setfam_1(k2_tarski(X28,X29))=k3_xboole_0(X28,X29), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.19/0.47  fof(c_0_16, plain, ![X17, X18]:m1_subset_1(k6_subset_1(X17,X18),k1_zfmisc_1(X17)), inference(variable_rename,[status(thm)],[dt_k6_subset_1])).
% 0.19/0.47  fof(c_0_17, plain, ![X19, X20]:k6_subset_1(X19,X20)=k4_xboole_0(X19,X20), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 0.19/0.47  fof(c_0_18, plain, ![X21, X22, X23, X24]:(((~r2_hidden(X24,X23)|r2_hidden(k3_subset_1(X21,X24),X22)|~m1_subset_1(X24,k1_zfmisc_1(X21))|X23!=k7_setfam_1(X21,X22)|~m1_subset_1(X23,k1_zfmisc_1(k1_zfmisc_1(X21)))|~m1_subset_1(X22,k1_zfmisc_1(k1_zfmisc_1(X21))))&(~r2_hidden(k3_subset_1(X21,X24),X22)|r2_hidden(X24,X23)|~m1_subset_1(X24,k1_zfmisc_1(X21))|X23!=k7_setfam_1(X21,X22)|~m1_subset_1(X23,k1_zfmisc_1(k1_zfmisc_1(X21)))|~m1_subset_1(X22,k1_zfmisc_1(k1_zfmisc_1(X21)))))&((m1_subset_1(esk1_3(X21,X22,X23),k1_zfmisc_1(X21))|X23=k7_setfam_1(X21,X22)|~m1_subset_1(X23,k1_zfmisc_1(k1_zfmisc_1(X21)))|~m1_subset_1(X22,k1_zfmisc_1(k1_zfmisc_1(X21))))&((~r2_hidden(esk1_3(X21,X22,X23),X23)|~r2_hidden(k3_subset_1(X21,esk1_3(X21,X22,X23)),X22)|X23=k7_setfam_1(X21,X22)|~m1_subset_1(X23,k1_zfmisc_1(k1_zfmisc_1(X21)))|~m1_subset_1(X22,k1_zfmisc_1(k1_zfmisc_1(X21))))&(r2_hidden(esk1_3(X21,X22,X23),X23)|r2_hidden(k3_subset_1(X21,esk1_3(X21,X22,X23)),X22)|X23=k7_setfam_1(X21,X22)|~m1_subset_1(X23,k1_zfmisc_1(k1_zfmisc_1(X21)))|~m1_subset_1(X22,k1_zfmisc_1(k1_zfmisc_1(X21))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_setfam_1])])])])])).
% 0.19/0.47  fof(c_0_19, plain, ![X26, X27]:(~m1_subset_1(X27,k1_zfmisc_1(k1_zfmisc_1(X26)))|m1_subset_1(k7_setfam_1(X26,X27),k1_zfmisc_1(k1_zfmisc_1(X26)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_setfam_1])])).
% 0.19/0.47  fof(c_0_20, plain, ![X15, X16]:(~m1_subset_1(X16,k1_zfmisc_1(X15))|k3_subset_1(X15,X16)=k4_xboole_0(X15,X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.19/0.47  cnf(c_0_21, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.47  cnf(c_0_22, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.47  cnf(c_0_23, plain, (m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.47  cnf(c_0_24, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.47  fof(c_0_25, plain, ![X11, X12]:((k2_zfmisc_1(X11,X12)!=k1_xboole_0|(X11=k1_xboole_0|X12=k1_xboole_0))&((X11!=k1_xboole_0|k2_zfmisc_1(X11,X12)=k1_xboole_0)&(X12!=k1_xboole_0|k2_zfmisc_1(X11,X12)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.19/0.47  fof(c_0_26, plain, ![X5, X6]:(~r1_tarski(X5,X6)|k3_xboole_0(X5,X6)=X5), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.19/0.47  fof(c_0_27, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>~((X2!=k1_xboole_0&k7_setfam_1(X1,X2)=k1_xboole_0)))), inference(assume_negation,[status(cth)],[t46_setfam_1])).
% 0.19/0.47  cnf(c_0_28, plain, (r2_hidden(X2,X4)|~r2_hidden(k3_subset_1(X1,X2),X3)|~m1_subset_1(X2,k1_zfmisc_1(X1))|X4!=k7_setfam_1(X1,X3)|~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1)))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.47  cnf(c_0_29, plain, (m1_subset_1(k7_setfam_1(X2,X1),k1_zfmisc_1(k1_zfmisc_1(X2)))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.47  cnf(c_0_30, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.47  cnf(c_0_31, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_setfam_1(k2_tarski(X1,X2))), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 0.19/0.47  cnf(c_0_32, plain, (m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_23, c_0_24])).
% 0.19/0.47  fof(c_0_33, plain, ![X13, X14]:~r2_hidden(X13,k2_zfmisc_1(X13,X14)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).
% 0.19/0.47  cnf(c_0_34, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.47  cnf(c_0_35, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.47  fof(c_0_36, plain, ![X9, X10]:k2_tarski(X9,X10)=k2_tarski(X10,X9), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.19/0.47  fof(c_0_37, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))&(esk3_0!=k1_xboole_0&k7_setfam_1(esk2_0,esk3_0)=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_27])])])).
% 0.19/0.47  cnf(c_0_38, plain, (r2_hidden(X1,k7_setfam_1(X2,X3))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(k3_subset_1(X2,X1),X3)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_28]), c_0_29])).
% 0.19/0.47  cnf(c_0_39, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_subset_1(X1,k4_xboole_0(X1,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])])).
% 0.19/0.47  cnf(c_0_40, plain, (~r2_hidden(X1,k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.47  cnf(c_0_41, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_34])).
% 0.19/0.47  cnf(c_0_42, plain, (k1_setfam_1(k2_tarski(X1,X2))=X1|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_35, c_0_22])).
% 0.19/0.47  cnf(c_0_43, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.47  cnf(c_0_44, negated_conjecture, (k7_setfam_1(esk2_0,esk3_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.47  cnf(c_0_45, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.47  cnf(c_0_46, plain, (r2_hidden(k4_xboole_0(X1,X2),k7_setfam_1(X1,X3))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))|~r2_hidden(k1_setfam_1(k2_tarski(X1,X2)),X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_32])])).
% 0.19/0.47  cnf(c_0_47, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.19/0.47  cnf(c_0_48, plain, (k1_setfam_1(k2_tarski(X1,X2))=X2|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.19/0.47  cnf(c_0_49, plain, (r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(k3_subset_1(X1,esk1_3(X1,X2,X3)),X2)|X3=k7_setfam_1(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.47  cnf(c_0_50, negated_conjecture, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_44]), c_0_45])])).
% 0.19/0.47  cnf(c_0_51, negated_conjecture, (~r2_hidden(k3_subset_1(esk2_0,k4_xboole_0(esk2_0,X1)),esk3_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_45]), c_0_44]), c_0_39]), c_0_47])).
% 0.19/0.47  cnf(c_0_52, plain, (k3_subset_1(X1,k4_xboole_0(X1,X2))=X2|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_48, c_0_39])).
% 0.19/0.47  fof(c_0_53, plain, ![X30, X31]:((~m1_subset_1(X30,k1_zfmisc_1(X31))|r1_tarski(X30,X31))&(~r1_tarski(X30,X31)|m1_subset_1(X30,k1_zfmisc_1(X31)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.47  cnf(c_0_54, negated_conjecture, (k7_setfam_1(esk2_0,X1)=k1_xboole_0|r2_hidden(k3_subset_1(esk2_0,esk1_3(esk2_0,X1,k1_xboole_0)),X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_47])).
% 0.19/0.47  cnf(c_0_55, negated_conjecture, (~r2_hidden(X1,esk3_0)|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.19/0.47  cnf(c_0_56, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.19/0.47  cnf(c_0_57, negated_conjecture, (k7_setfam_1(esk2_0,X1)=esk3_0|r2_hidden(k3_subset_1(esk2_0,esk1_3(esk2_0,X1,esk3_0)),X1)|r2_hidden(esk1_3(esk2_0,X1,esk3_0),esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))), inference(spm,[status(thm)],[c_0_49, c_0_45])).
% 0.19/0.47  cnf(c_0_58, negated_conjecture, (k7_setfam_1(esk2_0,k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_54]), c_0_50])])).
% 0.19/0.47  cnf(c_0_59, negated_conjecture, (esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.47  fof(c_0_60, plain, ![X32, X33, X34]:(~r2_hidden(X32,X33)|~m1_subset_1(X33,k1_zfmisc_1(X34))|m1_subset_1(X32,X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.19/0.47  cnf(c_0_61, negated_conjecture, (~m1_subset_1(X1,k1_zfmisc_1(esk2_0))|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.19/0.47  cnf(c_0_62, negated_conjecture, (r2_hidden(esk1_3(esk2_0,k1_xboole_0,esk3_0),esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_57]), c_0_58]), c_0_50])]), c_0_59])).
% 0.19/0.47  cnf(c_0_63, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.19/0.47  cnf(c_0_64, negated_conjecture, (~m1_subset_1(esk1_3(esk2_0,k1_xboole_0,esk3_0),k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.19/0.47  cnf(c_0_65, negated_conjecture, (m1_subset_1(esk1_3(esk2_0,k1_xboole_0,esk3_0),X1)|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_63, c_0_62])).
% 0.19/0.47  cnf(c_0_66, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_45])]), ['proof']).
% 0.19/0.47  # SZS output end CNFRefutation
% 0.19/0.47  # Proof object total steps             : 67
% 0.19/0.47  # Proof object clause steps            : 38
% 0.19/0.47  # Proof object formula steps           : 29
% 0.19/0.47  # Proof object conjectures             : 17
% 0.19/0.47  # Proof object clause conjectures      : 14
% 0.19/0.47  # Proof object formula conjectures     : 3
% 0.19/0.47  # Proof object initial clauses used    : 17
% 0.19/0.47  # Proof object initial formulas used   : 14
% 0.19/0.47  # Proof object generating inferences   : 16
% 0.19/0.47  # Proof object simplifying inferences  : 24
% 0.19/0.47  # Training examples: 0 positive, 0 negative
% 0.19/0.47  # Parsed axioms                        : 14
% 0.19/0.47  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.47  # Initial clauses                      : 23
% 0.19/0.47  # Removed in clause preprocessing      : 2
% 0.19/0.47  # Initial clauses in saturation        : 21
% 0.19/0.47  # Processed clauses                    : 883
% 0.19/0.47  # ...of these trivial                  : 20
% 0.19/0.47  # ...subsumed                          : 530
% 0.19/0.47  # ...remaining for further processing  : 333
% 0.19/0.47  # Other redundant clauses eliminated   : 4
% 0.19/0.47  # Clauses deleted for lack of memory   : 0
% 0.19/0.47  # Backward-subsumed                    : 1
% 0.19/0.47  # Backward-rewritten                   : 7
% 0.19/0.47  # Generated clauses                    : 3288
% 0.19/0.47  # ...of the previous two non-trivial   : 3039
% 0.19/0.47  # Contextual simplify-reflections      : 8
% 0.19/0.47  # Paramodulations                      : 3284
% 0.19/0.47  # Factorizations                       : 0
% 0.19/0.47  # Equation resolutions                 : 4
% 0.19/0.47  # Propositional unsat checks           : 0
% 0.19/0.47  #    Propositional check models        : 0
% 0.19/0.47  #    Propositional check unsatisfiable : 0
% 0.19/0.47  #    Propositional clauses             : 0
% 0.19/0.47  #    Propositional clauses after purity: 0
% 0.19/0.47  #    Propositional unsat core size     : 0
% 0.19/0.47  #    Propositional preprocessing time  : 0.000
% 0.19/0.47  #    Propositional encoding time       : 0.000
% 0.19/0.47  #    Propositional solver time         : 0.000
% 0.19/0.47  #    Success case prop preproc time    : 0.000
% 0.19/0.47  #    Success case prop encoding time   : 0.000
% 0.19/0.47  #    Success case prop solver time     : 0.000
% 0.19/0.47  # Current number of processed clauses  : 300
% 0.19/0.47  #    Positive orientable unit clauses  : 48
% 0.19/0.47  #    Positive unorientable unit clauses: 3
% 0.19/0.47  #    Negative unit clauses             : 5
% 0.19/0.47  #    Non-unit-clauses                  : 244
% 0.19/0.47  # Current number of unprocessed clauses: 2172
% 0.19/0.47  # ...number of literals in the above   : 8148
% 0.19/0.47  # Current number of archived formulas  : 0
% 0.19/0.47  # Current number of archived clauses   : 31
% 0.19/0.47  # Clause-clause subsumption calls (NU) : 29225
% 0.19/0.47  # Rec. Clause-clause subsumption calls : 6162
% 0.19/0.47  # Non-unit clause-clause subsumptions  : 521
% 0.19/0.47  # Unit Clause-clause subsumption calls : 460
% 0.19/0.47  # Rewrite failures with RHS unbound    : 0
% 0.19/0.47  # BW rewrite match attempts            : 34
% 0.19/0.47  # BW rewrite match successes           : 23
% 0.19/0.47  # Condensation attempts                : 0
% 0.19/0.47  # Condensation successes               : 0
% 0.19/0.47  # Termbank termtop insertions          : 99321
% 0.19/0.47  
% 0.19/0.47  # -------------------------------------------------
% 0.19/0.47  # User time                : 0.128 s
% 0.19/0.47  # System time              : 0.007 s
% 0.19/0.47  # Total time               : 0.135 s
% 0.19/0.47  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
