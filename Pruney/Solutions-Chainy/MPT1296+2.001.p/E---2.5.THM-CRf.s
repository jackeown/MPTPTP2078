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
% DateTime   : Thu Dec  3 11:12:57 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 176 expanded)
%              Number of clauses        :   42 (  75 expanded)
%              Number of leaves         :   21 (  47 expanded)
%              Depth                    :   14
%              Number of atoms          :  171 ( 312 expanded)
%              Number of equality atoms :   78 ( 169 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t22_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = k3_subset_1(X1,k1_subset_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

fof(d3_subset_1,axiom,(
    ! [X1] : k1_subset_1(X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(t48_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( X2 != k1_xboole_0
       => k5_setfam_1(X1,k7_setfam_1(X1,X2)) = k7_subset_1(X1,k2_subset_1(X1),k6_setfam_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_setfam_1)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(t33_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => k3_subset_1(X1,k7_subset_1(X1,X2,X3)) = k4_subset_1(X1,k3_subset_1(X1,X2),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_subset_1)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t12_tops_2,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( X2 != k1_xboole_0
       => k5_setfam_1(X1,k7_setfam_1(X1,X2)) = k3_subset_1(X1,k6_setfam_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_tops_2)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(dt_k5_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => m1_subset_1(k5_setfam_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_setfam_1)).

fof(dt_k7_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => m1_subset_1(k7_setfam_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_setfam_1)).

fof(d10_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( ( X2 != k1_xboole_0
         => k8_setfam_1(X1,X2) = k6_setfam_1(X1,X2) )
        & ( X2 = k1_xboole_0
         => k8_setfam_1(X1,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).

fof(dt_k8_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => m1_subset_1(k8_setfam_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_setfam_1)).

fof(c_0_21,plain,(
    ! [X6,X7] : k4_xboole_0(X6,X7) = k5_xboole_0(X6,k3_xboole_0(X6,X7)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_22,plain,(
    ! [X34,X35] : k1_setfam_1(k2_tarski(X34,X35)) = k3_xboole_0(X34,X35) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_23,plain,(
    ! [X21] : k2_subset_1(X21) = k3_subset_1(X21,k1_subset_1(X21)) ),
    inference(variable_rename,[status(thm)],[t22_subset_1])).

fof(c_0_24,plain,(
    ! [X13] : k1_subset_1(X13) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[d3_subset_1])).

fof(c_0_25,plain,(
    ! [X14,X15] :
      ( ~ m1_subset_1(X15,k1_zfmisc_1(X14))
      | k3_subset_1(X14,X15) = k4_xboole_0(X14,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

cnf(c_0_26,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_28,plain,(
    ! [X10] : k3_xboole_0(X10,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_29,plain,(
    ! [X38,X39] :
      ( ~ m1_subset_1(X39,k1_zfmisc_1(k1_zfmisc_1(X38)))
      | X39 = k1_xboole_0
      | k5_setfam_1(X38,k7_setfam_1(X38,X39)) = k7_subset_1(X38,k2_subset_1(X38),k6_setfam_1(X38,X39)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_setfam_1])])).

cnf(c_0_30,plain,
    ( k2_subset_1(X1) = k3_subset_1(X1,k1_subset_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( k1_subset_1(X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_34,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_35,plain,(
    ! [X12] : k5_xboole_0(X12,k1_xboole_0) = X12 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

fof(c_0_36,plain,(
    ! [X25] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X25)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

fof(c_0_37,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_38,plain,(
    ! [X18,X19,X20] :
      ( ~ m1_subset_1(X19,k1_zfmisc_1(X18))
      | ~ m1_subset_1(X20,k1_zfmisc_1(X18))
      | k4_subset_1(X18,X19,X20) = k2_xboole_0(X19,X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

fof(c_0_39,plain,(
    ! [X22,X23,X24] :
      ( ~ m1_subset_1(X23,k1_zfmisc_1(X22))
      | ~ m1_subset_1(X24,k1_zfmisc_1(X22))
      | k3_subset_1(X22,k7_subset_1(X22,X23,X24)) = k4_subset_1(X22,k3_subset_1(X22,X23),X24) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t33_subset_1])])])).

cnf(c_0_40,plain,
    ( X1 = k1_xboole_0
    | k5_setfam_1(X2,k7_setfam_1(X2,X1)) = k7_subset_1(X2,k2_subset_1(X2),k6_setfam_1(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_41,plain,
    ( k2_subset_1(X1) = k3_subset_1(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_42,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_43,plain,
    ( k1_setfam_1(k2_tarski(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_34,c_0_27])).

cnf(c_0_44,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_45,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_46,plain,(
    ! [X16,X17] :
      ( ~ m1_subset_1(X17,k1_zfmisc_1(X16))
      | k3_subset_1(X16,k3_subset_1(X16,X17)) = X17 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

fof(c_0_47,plain,(
    ! [X36,X37] :
      ( ( ~ m1_subset_1(X36,k1_zfmisc_1(X37))
        | r1_tarski(X36,X37) )
      & ( ~ r1_tarski(X36,X37)
        | m1_subset_1(X36,k1_zfmisc_1(X37)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_48,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_49,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_50,plain,
    ( k3_subset_1(X2,k7_subset_1(X2,X1,X3)) = k4_subset_1(X2,k3_subset_1(X2,X1),X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_51,plain,
    ( X1 = k1_xboole_0
    | k5_setfam_1(X2,k7_setfam_1(X2,X1)) = k7_subset_1(X2,k3_subset_1(X2,k1_xboole_0),k6_setfam_1(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(rw,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_52,plain,
    ( k3_subset_1(X1,k1_xboole_0) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44]),c_0_45])])).

cnf(c_0_53,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_54,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_55,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_48])).

cnf(c_0_56,plain,
    ( k3_subset_1(X1,k7_subset_1(X1,X2,X3)) = k2_xboole_0(k3_subset_1(X1,X2),X3)
    | ~ m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_57,plain,
    ( k7_subset_1(X1,X1,k6_setfam_1(X1,X2)) = k5_setfam_1(X1,k7_setfam_1(X1,X2))
    | X2 = k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(rw,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_58,plain,
    ( k3_subset_1(X1,X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_52]),c_0_45])])).

cnf(c_0_59,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

fof(c_0_60,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
       => ( X2 != k1_xboole_0
         => k5_setfam_1(X1,k7_setfam_1(X1,X2)) = k3_subset_1(X1,k6_setfam_1(X1,X2)) ) ) ),
    inference(assume_negation,[status(cth)],[t12_tops_2])).

cnf(c_0_61,plain,
    ( k3_subset_1(X1,k5_setfam_1(X1,k7_setfam_1(X1,X2))) = k2_xboole_0(k1_xboole_0,k6_setfam_1(X1,X2))
    | X2 = k1_xboole_0
    | ~ m1_subset_1(k6_setfam_1(X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58]),c_0_58]),c_0_45]),c_0_59])])).

fof(c_0_62,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(esk1_0)))
    & esk2_0 != k1_xboole_0
    & k5_setfam_1(esk1_0,k7_setfam_1(esk1_0,esk2_0)) != k3_subset_1(esk1_0,k6_setfam_1(esk1_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_60])])])).

cnf(c_0_63,plain,
    ( k3_subset_1(X1,k2_xboole_0(k1_xboole_0,k6_setfam_1(X1,X2))) = k5_setfam_1(X1,k7_setfam_1(X1,X2))
    | X2 = k1_xboole_0
    | ~ m1_subset_1(k5_setfam_1(X1,k7_setfam_1(X1,X2)),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k6_setfam_1(X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_53,c_0_61])).

cnf(c_0_64,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_65,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

fof(c_0_66,plain,(
    ! [X8,X9] :
      ( ~ r1_tarski(X8,X9)
      | k2_xboole_0(X8,X9) = X9 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

fof(c_0_67,plain,(
    ! [X11] : r1_tarski(k1_xboole_0,X11) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_68,negated_conjecture,
    ( k3_subset_1(esk1_0,k2_xboole_0(k1_xboole_0,k6_setfam_1(esk1_0,esk2_0))) = k5_setfam_1(esk1_0,k7_setfam_1(esk1_0,esk2_0))
    | ~ m1_subset_1(k5_setfam_1(esk1_0,k7_setfam_1(esk1_0,esk2_0)),k1_zfmisc_1(esk1_0))
    | ~ m1_subset_1(k6_setfam_1(esk1_0,esk2_0),k1_zfmisc_1(esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65])).

cnf(c_0_69,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_70,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_71,negated_conjecture,
    ( k5_setfam_1(esk1_0,k7_setfam_1(esk1_0,esk2_0)) != k3_subset_1(esk1_0,k6_setfam_1(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

fof(c_0_72,plain,(
    ! [X28,X29] :
      ( ~ m1_subset_1(X29,k1_zfmisc_1(k1_zfmisc_1(X28)))
      | m1_subset_1(k5_setfam_1(X28,X29),k1_zfmisc_1(X28)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_setfam_1])])).

cnf(c_0_73,negated_conjecture,
    ( ~ m1_subset_1(k5_setfam_1(esk1_0,k7_setfam_1(esk1_0,esk2_0)),k1_zfmisc_1(esk1_0))
    | ~ m1_subset_1(k6_setfam_1(esk1_0,esk2_0),k1_zfmisc_1(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_70])]),c_0_71])).

cnf(c_0_74,plain,
    ( m1_subset_1(k5_setfam_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

fof(c_0_75,plain,(
    ! [X30,X31] :
      ( ~ m1_subset_1(X31,k1_zfmisc_1(k1_zfmisc_1(X30)))
      | m1_subset_1(k7_setfam_1(X30,X31),k1_zfmisc_1(k1_zfmisc_1(X30))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_setfam_1])])).

cnf(c_0_76,negated_conjecture,
    ( ~ m1_subset_1(k7_setfam_1(esk1_0,esk2_0),k1_zfmisc_1(k1_zfmisc_1(esk1_0)))
    | ~ m1_subset_1(k6_setfam_1(esk1_0,esk2_0),k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_77,plain,
    ( m1_subset_1(k7_setfam_1(X2,X1),k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

fof(c_0_78,plain,(
    ! [X26,X27] :
      ( ( X27 = k1_xboole_0
        | k8_setfam_1(X26,X27) = k6_setfam_1(X26,X27)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k1_zfmisc_1(X26))) )
      & ( X27 != k1_xboole_0
        | k8_setfam_1(X26,X27) = X26
        | ~ m1_subset_1(X27,k1_zfmisc_1(k1_zfmisc_1(X26))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_setfam_1])])])).

cnf(c_0_79,negated_conjecture,
    ( ~ m1_subset_1(k6_setfam_1(esk1_0,esk2_0),k1_zfmisc_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_64])])).

cnf(c_0_80,plain,
    ( X1 = k1_xboole_0
    | k8_setfam_1(X2,X1) = k6_setfam_1(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

fof(c_0_81,plain,(
    ! [X32,X33] :
      ( ~ m1_subset_1(X33,k1_zfmisc_1(k1_zfmisc_1(X32)))
      | m1_subset_1(k8_setfam_1(X32,X33),k1_zfmisc_1(X32)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_setfam_1])])).

cnf(c_0_82,negated_conjecture,
    ( ~ m1_subset_1(k8_setfam_1(esk1_0,esk2_0),k1_zfmisc_1(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_64])]),c_0_65])).

cnf(c_0_83,plain,
    ( m1_subset_1(k8_setfam_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_84,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_64])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:09:05 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.53  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S05BN
% 0.21/0.53  # and selection function SelectUnlessUniqMaxSmallestOrientable.
% 0.21/0.53  #
% 0.21/0.53  # Preprocessing time       : 0.027 s
% 0.21/0.53  # Presaturation interreduction done
% 0.21/0.53  
% 0.21/0.53  # Proof found!
% 0.21/0.53  # SZS status Theorem
% 0.21/0.53  # SZS output start CNFRefutation
% 0.21/0.53  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.21/0.53  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.21/0.53  fof(t22_subset_1, axiom, ![X1]:k2_subset_1(X1)=k3_subset_1(X1,k1_subset_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_subset_1)).
% 0.21/0.53  fof(d3_subset_1, axiom, ![X1]:k1_subset_1(X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 0.21/0.53  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 0.21/0.53  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 0.21/0.53  fof(t48_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(X2!=k1_xboole_0=>k5_setfam_1(X1,k7_setfam_1(X1,X2))=k7_subset_1(X1,k2_subset_1(X1),k6_setfam_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_setfam_1)).
% 0.21/0.53  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 0.21/0.53  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 0.21/0.53  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.21/0.53  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 0.21/0.53  fof(t33_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k3_subset_1(X1,k7_subset_1(X1,X2,X3))=k4_subset_1(X1,k3_subset_1(X1,X2),X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_subset_1)).
% 0.21/0.53  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 0.21/0.53  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.21/0.53  fof(t12_tops_2, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(X2!=k1_xboole_0=>k5_setfam_1(X1,k7_setfam_1(X1,X2))=k3_subset_1(X1,k6_setfam_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_tops_2)).
% 0.21/0.53  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.21/0.53  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.21/0.53  fof(dt_k5_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>m1_subset_1(k5_setfam_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_setfam_1)).
% 0.21/0.53  fof(dt_k7_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>m1_subset_1(k7_setfam_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_setfam_1)).
% 0.21/0.53  fof(d10_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>((X2!=k1_xboole_0=>k8_setfam_1(X1,X2)=k6_setfam_1(X1,X2))&(X2=k1_xboole_0=>k8_setfam_1(X1,X2)=X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_setfam_1)).
% 0.21/0.53  fof(dt_k8_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>m1_subset_1(k8_setfam_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_setfam_1)).
% 0.21/0.53  fof(c_0_21, plain, ![X6, X7]:k4_xboole_0(X6,X7)=k5_xboole_0(X6,k3_xboole_0(X6,X7)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.21/0.53  fof(c_0_22, plain, ![X34, X35]:k1_setfam_1(k2_tarski(X34,X35))=k3_xboole_0(X34,X35), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.21/0.53  fof(c_0_23, plain, ![X21]:k2_subset_1(X21)=k3_subset_1(X21,k1_subset_1(X21)), inference(variable_rename,[status(thm)],[t22_subset_1])).
% 0.21/0.53  fof(c_0_24, plain, ![X13]:k1_subset_1(X13)=k1_xboole_0, inference(variable_rename,[status(thm)],[d3_subset_1])).
% 0.21/0.53  fof(c_0_25, plain, ![X14, X15]:(~m1_subset_1(X15,k1_zfmisc_1(X14))|k3_subset_1(X14,X15)=k4_xboole_0(X14,X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.21/0.53  cnf(c_0_26, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.53  cnf(c_0_27, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.53  fof(c_0_28, plain, ![X10]:k3_xboole_0(X10,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.21/0.53  fof(c_0_29, plain, ![X38, X39]:(~m1_subset_1(X39,k1_zfmisc_1(k1_zfmisc_1(X38)))|(X39=k1_xboole_0|k5_setfam_1(X38,k7_setfam_1(X38,X39))=k7_subset_1(X38,k2_subset_1(X38),k6_setfam_1(X38,X39)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_setfam_1])])).
% 0.21/0.53  cnf(c_0_30, plain, (k2_subset_1(X1)=k3_subset_1(X1,k1_subset_1(X1))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.53  cnf(c_0_31, plain, (k1_subset_1(X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.21/0.53  cnf(c_0_32, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.53  cnf(c_0_33, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_26, c_0_27])).
% 0.21/0.53  cnf(c_0_34, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.21/0.53  fof(c_0_35, plain, ![X12]:k5_xboole_0(X12,k1_xboole_0)=X12, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.21/0.53  fof(c_0_36, plain, ![X25]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X25)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.21/0.53  fof(c_0_37, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.21/0.53  fof(c_0_38, plain, ![X18, X19, X20]:(~m1_subset_1(X19,k1_zfmisc_1(X18))|~m1_subset_1(X20,k1_zfmisc_1(X18))|k4_subset_1(X18,X19,X20)=k2_xboole_0(X19,X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 0.21/0.53  fof(c_0_39, plain, ![X22, X23, X24]:(~m1_subset_1(X23,k1_zfmisc_1(X22))|(~m1_subset_1(X24,k1_zfmisc_1(X22))|k3_subset_1(X22,k7_subset_1(X22,X23,X24))=k4_subset_1(X22,k3_subset_1(X22,X23),X24))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t33_subset_1])])])).
% 0.21/0.53  cnf(c_0_40, plain, (X1=k1_xboole_0|k5_setfam_1(X2,k7_setfam_1(X2,X1))=k7_subset_1(X2,k2_subset_1(X2),k6_setfam_1(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.21/0.53  cnf(c_0_41, plain, (k2_subset_1(X1)=k3_subset_1(X1,k1_xboole_0)), inference(rw,[status(thm)],[c_0_30, c_0_31])).
% 0.21/0.53  cnf(c_0_42, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_32, c_0_33])).
% 0.21/0.53  cnf(c_0_43, plain, (k1_setfam_1(k2_tarski(X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_34, c_0_27])).
% 0.21/0.53  cnf(c_0_44, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.21/0.53  cnf(c_0_45, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.21/0.53  fof(c_0_46, plain, ![X16, X17]:(~m1_subset_1(X17,k1_zfmisc_1(X16))|k3_subset_1(X16,k3_subset_1(X16,X17))=X17), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 0.21/0.53  fof(c_0_47, plain, ![X36, X37]:((~m1_subset_1(X36,k1_zfmisc_1(X37))|r1_tarski(X36,X37))&(~r1_tarski(X36,X37)|m1_subset_1(X36,k1_zfmisc_1(X37)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.21/0.53  cnf(c_0_48, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.21/0.53  cnf(c_0_49, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.21/0.53  cnf(c_0_50, plain, (k3_subset_1(X2,k7_subset_1(X2,X1,X3))=k4_subset_1(X2,k3_subset_1(X2,X1),X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.21/0.53  cnf(c_0_51, plain, (X1=k1_xboole_0|k5_setfam_1(X2,k7_setfam_1(X2,X1))=k7_subset_1(X2,k3_subset_1(X2,k1_xboole_0),k6_setfam_1(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(rw,[status(thm)],[c_0_40, c_0_41])).
% 0.21/0.53  cnf(c_0_52, plain, (k3_subset_1(X1,k1_xboole_0)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44]), c_0_45])])).
% 0.21/0.53  cnf(c_0_53, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.21/0.53  cnf(c_0_54, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.21/0.53  cnf(c_0_55, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_48])).
% 0.21/0.53  cnf(c_0_56, plain, (k3_subset_1(X1,k7_subset_1(X1,X2,X3))=k2_xboole_0(k3_subset_1(X1,X2),X3)|~m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.21/0.53  cnf(c_0_57, plain, (k7_subset_1(X1,X1,k6_setfam_1(X1,X2))=k5_setfam_1(X1,k7_setfam_1(X1,X2))|X2=k1_xboole_0|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(rw,[status(thm)],[c_0_51, c_0_52])).
% 0.21/0.53  cnf(c_0_58, plain, (k3_subset_1(X1,X1)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_52]), c_0_45])])).
% 0.21/0.53  cnf(c_0_59, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.21/0.53  fof(c_0_60, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(X2!=k1_xboole_0=>k5_setfam_1(X1,k7_setfam_1(X1,X2))=k3_subset_1(X1,k6_setfam_1(X1,X2))))), inference(assume_negation,[status(cth)],[t12_tops_2])).
% 0.21/0.53  cnf(c_0_61, plain, (k3_subset_1(X1,k5_setfam_1(X1,k7_setfam_1(X1,X2)))=k2_xboole_0(k1_xboole_0,k6_setfam_1(X1,X2))|X2=k1_xboole_0|~m1_subset_1(k6_setfam_1(X1,X2),k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_58]), c_0_58]), c_0_45]), c_0_59])])).
% 0.21/0.53  fof(c_0_62, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(esk1_0)))&(esk2_0!=k1_xboole_0&k5_setfam_1(esk1_0,k7_setfam_1(esk1_0,esk2_0))!=k3_subset_1(esk1_0,k6_setfam_1(esk1_0,esk2_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_60])])])).
% 0.21/0.53  cnf(c_0_63, plain, (k3_subset_1(X1,k2_xboole_0(k1_xboole_0,k6_setfam_1(X1,X2)))=k5_setfam_1(X1,k7_setfam_1(X1,X2))|X2=k1_xboole_0|~m1_subset_1(k5_setfam_1(X1,k7_setfam_1(X1,X2)),k1_zfmisc_1(X1))|~m1_subset_1(k6_setfam_1(X1,X2),k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(spm,[status(thm)],[c_0_53, c_0_61])).
% 0.21/0.53  cnf(c_0_64, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.21/0.53  cnf(c_0_65, negated_conjecture, (esk2_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.21/0.53  fof(c_0_66, plain, ![X8, X9]:(~r1_tarski(X8,X9)|k2_xboole_0(X8,X9)=X9), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.21/0.53  fof(c_0_67, plain, ![X11]:r1_tarski(k1_xboole_0,X11), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.21/0.53  cnf(c_0_68, negated_conjecture, (k3_subset_1(esk1_0,k2_xboole_0(k1_xboole_0,k6_setfam_1(esk1_0,esk2_0)))=k5_setfam_1(esk1_0,k7_setfam_1(esk1_0,esk2_0))|~m1_subset_1(k5_setfam_1(esk1_0,k7_setfam_1(esk1_0,esk2_0)),k1_zfmisc_1(esk1_0))|~m1_subset_1(k6_setfam_1(esk1_0,esk2_0),k1_zfmisc_1(esk1_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_65])).
% 0.21/0.53  cnf(c_0_69, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.21/0.53  cnf(c_0_70, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.21/0.53  cnf(c_0_71, negated_conjecture, (k5_setfam_1(esk1_0,k7_setfam_1(esk1_0,esk2_0))!=k3_subset_1(esk1_0,k6_setfam_1(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.21/0.53  fof(c_0_72, plain, ![X28, X29]:(~m1_subset_1(X29,k1_zfmisc_1(k1_zfmisc_1(X28)))|m1_subset_1(k5_setfam_1(X28,X29),k1_zfmisc_1(X28))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_setfam_1])])).
% 0.21/0.53  cnf(c_0_73, negated_conjecture, (~m1_subset_1(k5_setfam_1(esk1_0,k7_setfam_1(esk1_0,esk2_0)),k1_zfmisc_1(esk1_0))|~m1_subset_1(k6_setfam_1(esk1_0,esk2_0),k1_zfmisc_1(esk1_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_70])]), c_0_71])).
% 0.21/0.53  cnf(c_0_74, plain, (m1_subset_1(k5_setfam_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.21/0.53  fof(c_0_75, plain, ![X30, X31]:(~m1_subset_1(X31,k1_zfmisc_1(k1_zfmisc_1(X30)))|m1_subset_1(k7_setfam_1(X30,X31),k1_zfmisc_1(k1_zfmisc_1(X30)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_setfam_1])])).
% 0.21/0.53  cnf(c_0_76, negated_conjecture, (~m1_subset_1(k7_setfam_1(esk1_0,esk2_0),k1_zfmisc_1(k1_zfmisc_1(esk1_0)))|~m1_subset_1(k6_setfam_1(esk1_0,esk2_0),k1_zfmisc_1(esk1_0))), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.21/0.53  cnf(c_0_77, plain, (m1_subset_1(k7_setfam_1(X2,X1),k1_zfmisc_1(k1_zfmisc_1(X2)))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.21/0.53  fof(c_0_78, plain, ![X26, X27]:((X27=k1_xboole_0|k8_setfam_1(X26,X27)=k6_setfam_1(X26,X27)|~m1_subset_1(X27,k1_zfmisc_1(k1_zfmisc_1(X26))))&(X27!=k1_xboole_0|k8_setfam_1(X26,X27)=X26|~m1_subset_1(X27,k1_zfmisc_1(k1_zfmisc_1(X26))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_setfam_1])])])).
% 0.21/0.53  cnf(c_0_79, negated_conjecture, (~m1_subset_1(k6_setfam_1(esk1_0,esk2_0),k1_zfmisc_1(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_64])])).
% 0.21/0.53  cnf(c_0_80, plain, (X1=k1_xboole_0|k8_setfam_1(X2,X1)=k6_setfam_1(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_78])).
% 0.21/0.53  fof(c_0_81, plain, ![X32, X33]:(~m1_subset_1(X33,k1_zfmisc_1(k1_zfmisc_1(X32)))|m1_subset_1(k8_setfam_1(X32,X33),k1_zfmisc_1(X32))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_setfam_1])])).
% 0.21/0.53  cnf(c_0_82, negated_conjecture, (~m1_subset_1(k8_setfam_1(esk1_0,esk2_0),k1_zfmisc_1(esk1_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_64])]), c_0_65])).
% 0.21/0.53  cnf(c_0_83, plain, (m1_subset_1(k8_setfam_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_81])).
% 0.21/0.53  cnf(c_0_84, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_64])]), ['proof']).
% 0.21/0.53  # SZS output end CNFRefutation
% 0.21/0.53  # Proof object total steps             : 85
% 0.21/0.53  # Proof object clause steps            : 42
% 0.21/0.53  # Proof object formula steps           : 43
% 0.21/0.53  # Proof object conjectures             : 12
% 0.21/0.53  # Proof object clause conjectures      : 9
% 0.21/0.53  # Proof object formula conjectures     : 3
% 0.21/0.53  # Proof object initial clauses used    : 23
% 0.21/0.53  # Proof object initial formulas used   : 21
% 0.21/0.53  # Proof object generating inferences   : 12
% 0.21/0.53  # Proof object simplifying inferences  : 28
% 0.21/0.53  # Training examples: 0 positive, 0 negative
% 0.21/0.53  # Parsed axioms                        : 22
% 0.21/0.53  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.53  # Initial clauses                      : 28
% 0.21/0.53  # Removed in clause preprocessing      : 4
% 0.21/0.53  # Initial clauses in saturation        : 24
% 0.21/0.53  # Processed clauses                    : 1332
% 0.21/0.53  # ...of these trivial                  : 8
% 0.21/0.53  # ...subsumed                          : 848
% 0.21/0.53  # ...remaining for further processing  : 476
% 0.21/0.53  # Other redundant clauses eliminated   : 3
% 0.21/0.53  # Clauses deleted for lack of memory   : 0
% 0.21/0.53  # Backward-subsumed                    : 20
% 0.21/0.53  # Backward-rewritten                   : 22
% 0.21/0.53  # Generated clauses                    : 3849
% 0.21/0.53  # ...of the previous two non-trivial   : 3679
% 0.21/0.53  # Contextual simplify-reflections      : 30
% 0.21/0.53  # Paramodulations                      : 3845
% 0.21/0.53  # Factorizations                       : 1
% 0.21/0.53  # Equation resolutions                 : 3
% 0.21/0.53  # Propositional unsat checks           : 0
% 0.21/0.53  #    Propositional check models        : 0
% 0.21/0.53  #    Propositional check unsatisfiable : 0
% 0.21/0.53  #    Propositional clauses             : 0
% 0.21/0.53  #    Propositional clauses after purity: 0
% 0.21/0.53  #    Propositional unsat core size     : 0
% 0.21/0.53  #    Propositional preprocessing time  : 0.000
% 0.21/0.53  #    Propositional encoding time       : 0.000
% 0.21/0.53  #    Propositional solver time         : 0.000
% 0.21/0.53  #    Success case prop preproc time    : 0.000
% 0.21/0.53  #    Success case prop encoding time   : 0.000
% 0.21/0.53  #    Success case prop solver time     : 0.000
% 0.21/0.53  # Current number of processed clauses  : 408
% 0.21/0.53  #    Positive orientable unit clauses  : 12
% 0.21/0.53  #    Positive unorientable unit clauses: 0
% 0.21/0.53  #    Negative unit clauses             : 4
% 0.21/0.53  #    Non-unit-clauses                  : 392
% 0.21/0.53  # Current number of unprocessed clauses: 2319
% 0.21/0.53  # ...number of literals in the above   : 17286
% 0.21/0.53  # Current number of archived formulas  : 0
% 0.21/0.53  # Current number of archived clauses   : 69
% 0.21/0.53  # Clause-clause subsumption calls (NU) : 68349
% 0.21/0.53  # Rec. Clause-clause subsumption calls : 11631
% 0.21/0.53  # Non-unit clause-clause subsumptions  : 898
% 0.21/0.53  # Unit Clause-clause subsumption calls : 402
% 0.21/0.53  # Rewrite failures with RHS unbound    : 0
% 0.21/0.53  # BW rewrite match attempts            : 57
% 0.21/0.53  # BW rewrite match successes           : 3
% 0.21/0.53  # Condensation attempts                : 0
% 0.21/0.53  # Condensation successes               : 0
% 0.21/0.53  # Termbank termtop insertions          : 163822
% 0.21/0.53  
% 0.21/0.53  # -------------------------------------------------
% 0.21/0.53  # User time                : 0.180 s
% 0.21/0.53  # System time              : 0.006 s
% 0.21/0.53  # Total time               : 0.186 s
% 0.21/0.53  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
