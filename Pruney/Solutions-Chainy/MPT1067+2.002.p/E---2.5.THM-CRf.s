%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:07:44 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 120 expanded)
%              Number of clauses        :   28 (  42 expanded)
%              Number of leaves         :    8 (  29 expanded)
%              Depth                    :    9
%              Number of atoms          :  158 ( 582 expanded)
%              Number of equality atoms :    8 (  11 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :    9 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t184_funct_2,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,X1,X2)
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1)))
                 => r1_tarski(k5_setfam_1(X1,X4),k5_setfam_1(X1,k6_funct_2(X1,X2,X3,k7_funct_2(X1,X2,X3,X4)))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t184_funct_2)).

fof(d12_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_setfam_1(X2,X1)
    <=> r1_tarski(X1,k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_setfam_1)).

fof(redefinition_k5_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => k5_setfam_1(X1,X2) = k3_tarski(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

fof(t182_funct_2,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,X1,X2)
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1)))
                 => ! [X5] :
                      ( m1_subset_1(X5,k1_zfmisc_1(X1))
                     => ( m1_setfam_1(X4,X5)
                       => m1_setfam_1(k6_funct_2(X1,X2,X3,k7_funct_2(X1,X2,X3,X4)),X5) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_funct_2)).

fof(dt_k6_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X2)
        & v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X2))) )
     => m1_subset_1(k6_funct_2(X1,X2,X3,X4),k1_zfmisc_1(k1_zfmisc_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_funct_2)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(dt_k7_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X2)
        & v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1))) )
     => m1_subset_1(k7_funct_2(X1,X2,X3,X4),k1_zfmisc_1(k1_zfmisc_1(X2))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_funct_2)).

fof(dt_k5_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => m1_subset_1(k5_setfam_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_setfam_1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ~ v1_xboole_0(X2)
           => ! [X3] :
                ( ( v1_funct_1(X3)
                  & v1_funct_2(X3,X1,X2)
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
               => ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1)))
                   => r1_tarski(k5_setfam_1(X1,X4),k5_setfam_1(X1,k6_funct_2(X1,X2,X3,k7_funct_2(X1,X2,X3,X4)))) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t184_funct_2])).

fof(c_0_9,plain,(
    ! [X8,X9] :
      ( ( ~ m1_setfam_1(X9,X8)
        | r1_tarski(X8,k3_tarski(X9)) )
      & ( ~ r1_tarski(X8,k3_tarski(X9))
        | m1_setfam_1(X9,X8) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_setfam_1])])).

fof(c_0_10,plain,(
    ! [X12,X13] :
      ( ~ m1_subset_1(X13,k1_zfmisc_1(k1_zfmisc_1(X12)))
      | k5_setfam_1(X12,X13) = k3_tarski(X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k5_setfam_1])])).

fof(c_0_11,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0)
    & ~ v1_xboole_0(esk2_0)
    & v1_funct_1(esk3_0)
    & v1_funct_2(esk3_0,esk1_0,esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    & m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk1_0)))
    & ~ r1_tarski(k5_setfam_1(esk1_0,esk4_0),k5_setfam_1(esk1_0,k6_funct_2(esk1_0,esk2_0,esk3_0,k7_funct_2(esk1_0,esk2_0,esk3_0,esk4_0)))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).

cnf(c_0_12,plain,
    ( r1_tarski(X2,k3_tarski(X1))
    | ~ m1_setfam_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( k5_setfam_1(X2,X1) = k3_tarski(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_14,plain,(
    ! [X22,X23,X24,X25,X26] :
      ( v1_xboole_0(X22)
      | v1_xboole_0(X23)
      | ~ v1_funct_1(X24)
      | ~ v1_funct_2(X24,X22,X23)
      | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))
      | ~ m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(X22)))
      | ~ m1_subset_1(X26,k1_zfmisc_1(X22))
      | ~ m1_setfam_1(X25,X26)
      | m1_setfam_1(k6_funct_2(X22,X23,X24,k7_funct_2(X22,X23,X24,X25)),X26) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t182_funct_2])])])])).

cnf(c_0_15,negated_conjecture,
    ( ~ r1_tarski(k5_setfam_1(esk1_0,esk4_0),k5_setfam_1(esk1_0,k6_funct_2(esk1_0,esk2_0,esk3_0,k7_funct_2(esk1_0,esk2_0,esk3_0,esk4_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( r1_tarski(X1,k5_setfam_1(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_setfam_1(X3,X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_17,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | m1_setfam_1(k6_funct_2(X1,X2,X3,k7_funct_2(X1,X2,X3,X4)),X5)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(X1))
    | ~ m1_setfam_1(X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,negated_conjecture,
    ( v1_funct_2(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_21,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_22,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_23,plain,(
    ! [X14,X15,X16,X17] :
      ( v1_xboole_0(X14)
      | v1_xboole_0(X15)
      | ~ v1_funct_1(X16)
      | ~ v1_funct_2(X16,X14,X15)
      | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))
      | ~ m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(X15)))
      | m1_subset_1(k6_funct_2(X14,X15,X16,X17),k1_zfmisc_1(k1_zfmisc_1(X14))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_funct_2])])])).

fof(c_0_24,plain,(
    ! [X6,X7] :
      ( ( r1_tarski(X6,X7)
        | X6 != X7 )
      & ( r1_tarski(X7,X6)
        | X6 != X7 )
      & ( ~ r1_tarski(X6,X7)
        | ~ r1_tarski(X7,X6)
        | X6 = X7 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_25,negated_conjecture,
    ( ~ m1_subset_1(k6_funct_2(esk1_0,esk2_0,esk3_0,k7_funct_2(esk1_0,esk2_0,esk3_0,esk4_0)),k1_zfmisc_1(k1_zfmisc_1(esk1_0)))
    | ~ m1_setfam_1(k6_funct_2(esk1_0,esk2_0,esk3_0,k7_funct_2(esk1_0,esk2_0,esk3_0,esk4_0)),k5_setfam_1(esk1_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_26,negated_conjecture,
    ( m1_setfam_1(k6_funct_2(esk1_0,esk2_0,esk3_0,k7_funct_2(esk1_0,esk2_0,esk3_0,X1)),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(esk1_0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk1_0))
    | ~ m1_setfam_1(X1,X2) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_20])]),c_0_21]),c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_28,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | m1_subset_1(k6_funct_2(X1,X2,X3,X4),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_29,plain,(
    ! [X18,X19,X20,X21] :
      ( v1_xboole_0(X18)
      | v1_xboole_0(X19)
      | ~ v1_funct_1(X20)
      | ~ v1_funct_2(X20,X18,X19)
      | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))
      | ~ m1_subset_1(X21,k1_zfmisc_1(k1_zfmisc_1(X18)))
      | m1_subset_1(k7_funct_2(X18,X19,X20,X21),k1_zfmisc_1(k1_zfmisc_1(X19))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_funct_2])])])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( ~ m1_subset_1(k6_funct_2(esk1_0,esk2_0,esk3_0,k7_funct_2(esk1_0,esk2_0,esk3_0,esk4_0)),k1_zfmisc_1(k1_zfmisc_1(esk1_0)))
    | ~ m1_subset_1(k5_setfam_1(esk1_0,esk4_0),k1_zfmisc_1(esk1_0))
    | ~ m1_setfam_1(esk4_0,k5_setfam_1(esk1_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(k6_funct_2(esk1_0,esk2_0,esk3_0,X1),k1_zfmisc_1(k1_zfmisc_1(esk1_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(esk2_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_18]),c_0_19]),c_0_20])]),c_0_21]),c_0_22])).

cnf(c_0_33,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | m1_subset_1(k7_funct_2(X1,X2,X3,X4),k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_34,plain,
    ( m1_setfam_1(X2,X1)
    | ~ r1_tarski(X1,k3_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_30])).

cnf(c_0_36,negated_conjecture,
    ( ~ m1_subset_1(k7_funct_2(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k1_zfmisc_1(esk2_0)))
    | ~ m1_subset_1(k5_setfam_1(esk1_0,esk4_0),k1_zfmisc_1(esk1_0))
    | ~ m1_setfam_1(esk4_0,k5_setfam_1(esk1_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(k7_funct_2(esk1_0,esk2_0,esk3_0,X1),k1_zfmisc_1(k1_zfmisc_1(esk2_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(esk1_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_18]),c_0_19]),c_0_20])]),c_0_21]),c_0_22])).

cnf(c_0_38,plain,
    ( m1_setfam_1(X1,k3_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_39,negated_conjecture,
    ( ~ m1_subset_1(k5_setfam_1(esk1_0,esk4_0),k1_zfmisc_1(esk1_0))
    | ~ m1_setfam_1(esk4_0,k5_setfam_1(esk1_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_27])])).

cnf(c_0_40,plain,
    ( m1_setfam_1(X1,k5_setfam_1(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_13])).

fof(c_0_41,plain,(
    ! [X10,X11] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(k1_zfmisc_1(X10)))
      | m1_subset_1(k5_setfam_1(X10,X11),k1_zfmisc_1(X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_setfam_1])])).

cnf(c_0_42,negated_conjecture,
    ( ~ m1_subset_1(k5_setfam_1(esk1_0,esk4_0),k1_zfmisc_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_27])])).

cnf(c_0_43,plain,
    ( m1_subset_1(k5_setfam_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_44,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_27])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:38:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.36  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.36  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.36  #
% 0.13/0.36  # Preprocessing time       : 0.013 s
% 0.13/0.36  # Presaturation interreduction done
% 0.13/0.36  
% 0.13/0.36  # Proof found!
% 0.13/0.36  # SZS status Theorem
% 0.13/0.36  # SZS output start CNFRefutation
% 0.13/0.36  fof(t184_funct_2, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1)))=>r1_tarski(k5_setfam_1(X1,X4),k5_setfam_1(X1,k6_funct_2(X1,X2,X3,k7_funct_2(X1,X2,X3,X4)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t184_funct_2)).
% 0.13/0.36  fof(d12_setfam_1, axiom, ![X1, X2]:(m1_setfam_1(X2,X1)<=>r1_tarski(X1,k3_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_setfam_1)).
% 0.13/0.36  fof(redefinition_k5_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>k5_setfam_1(X1,X2)=k3_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_setfam_1)).
% 0.13/0.36  fof(t182_funct_2, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1)))=>![X5]:(m1_subset_1(X5,k1_zfmisc_1(X1))=>(m1_setfam_1(X4,X5)=>m1_setfam_1(k6_funct_2(X1,X2,X3,k7_funct_2(X1,X2,X3,X4)),X5))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_funct_2)).
% 0.13/0.36  fof(dt_k6_funct_2, axiom, ![X1, X2, X3, X4]:((((((~(v1_xboole_0(X1))&~(v1_xboole_0(X2)))&v1_funct_1(X3))&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X2))))=>m1_subset_1(k6_funct_2(X1,X2,X3,X4),k1_zfmisc_1(k1_zfmisc_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_funct_2)).
% 0.13/0.36  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.13/0.36  fof(dt_k7_funct_2, axiom, ![X1, X2, X3, X4]:((((((~(v1_xboole_0(X1))&~(v1_xboole_0(X2)))&v1_funct_1(X3))&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1))))=>m1_subset_1(k7_funct_2(X1,X2,X3,X4),k1_zfmisc_1(k1_zfmisc_1(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_funct_2)).
% 0.13/0.36  fof(dt_k5_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>m1_subset_1(k5_setfam_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_setfam_1)).
% 0.13/0.36  fof(c_0_8, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1)))=>r1_tarski(k5_setfam_1(X1,X4),k5_setfam_1(X1,k6_funct_2(X1,X2,X3,k7_funct_2(X1,X2,X3,X4))))))))), inference(assume_negation,[status(cth)],[t184_funct_2])).
% 0.13/0.36  fof(c_0_9, plain, ![X8, X9]:((~m1_setfam_1(X9,X8)|r1_tarski(X8,k3_tarski(X9)))&(~r1_tarski(X8,k3_tarski(X9))|m1_setfam_1(X9,X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_setfam_1])])).
% 0.13/0.36  fof(c_0_10, plain, ![X12, X13]:(~m1_subset_1(X13,k1_zfmisc_1(k1_zfmisc_1(X12)))|k5_setfam_1(X12,X13)=k3_tarski(X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k5_setfam_1])])).
% 0.13/0.36  fof(c_0_11, negated_conjecture, (~v1_xboole_0(esk1_0)&(~v1_xboole_0(esk2_0)&(((v1_funct_1(esk3_0)&v1_funct_2(esk3_0,esk1_0,esk2_0))&m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))))&(m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk1_0)))&~r1_tarski(k5_setfam_1(esk1_0,esk4_0),k5_setfam_1(esk1_0,k6_funct_2(esk1_0,esk2_0,esk3_0,k7_funct_2(esk1_0,esk2_0,esk3_0,esk4_0)))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).
% 0.13/0.36  cnf(c_0_12, plain, (r1_tarski(X2,k3_tarski(X1))|~m1_setfam_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.36  cnf(c_0_13, plain, (k5_setfam_1(X2,X1)=k3_tarski(X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.36  fof(c_0_14, plain, ![X22, X23, X24, X25, X26]:(v1_xboole_0(X22)|(v1_xboole_0(X23)|(~v1_funct_1(X24)|~v1_funct_2(X24,X22,X23)|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))|(~m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(X22)))|(~m1_subset_1(X26,k1_zfmisc_1(X22))|(~m1_setfam_1(X25,X26)|m1_setfam_1(k6_funct_2(X22,X23,X24,k7_funct_2(X22,X23,X24,X25)),X26))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t182_funct_2])])])])).
% 0.13/0.36  cnf(c_0_15, negated_conjecture, (~r1_tarski(k5_setfam_1(esk1_0,esk4_0),k5_setfam_1(esk1_0,k6_funct_2(esk1_0,esk2_0,esk3_0,k7_funct_2(esk1_0,esk2_0,esk3_0,esk4_0))))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.36  cnf(c_0_16, plain, (r1_tarski(X1,k5_setfam_1(X2,X3))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))|~m1_setfam_1(X3,X1)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.13/0.36  cnf(c_0_17, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|m1_setfam_1(k6_funct_2(X1,X2,X3,k7_funct_2(X1,X2,X3,X4)),X5)|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1)))|~m1_subset_1(X5,k1_zfmisc_1(X1))|~m1_setfam_1(X4,X5)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.36  cnf(c_0_18, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.36  cnf(c_0_19, negated_conjecture, (v1_funct_2(esk3_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.36  cnf(c_0_20, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.36  cnf(c_0_21, negated_conjecture, (~v1_xboole_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.36  cnf(c_0_22, negated_conjecture, (~v1_xboole_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.36  fof(c_0_23, plain, ![X14, X15, X16, X17]:(v1_xboole_0(X14)|v1_xboole_0(X15)|~v1_funct_1(X16)|~v1_funct_2(X16,X14,X15)|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))|~m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(X15)))|m1_subset_1(k6_funct_2(X14,X15,X16,X17),k1_zfmisc_1(k1_zfmisc_1(X14)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_funct_2])])])).
% 0.13/0.36  fof(c_0_24, plain, ![X6, X7]:(((r1_tarski(X6,X7)|X6!=X7)&(r1_tarski(X7,X6)|X6!=X7))&(~r1_tarski(X6,X7)|~r1_tarski(X7,X6)|X6=X7)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.13/0.36  cnf(c_0_25, negated_conjecture, (~m1_subset_1(k6_funct_2(esk1_0,esk2_0,esk3_0,k7_funct_2(esk1_0,esk2_0,esk3_0,esk4_0)),k1_zfmisc_1(k1_zfmisc_1(esk1_0)))|~m1_setfam_1(k6_funct_2(esk1_0,esk2_0,esk3_0,k7_funct_2(esk1_0,esk2_0,esk3_0,esk4_0)),k5_setfam_1(esk1_0,esk4_0))), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.13/0.36  cnf(c_0_26, negated_conjecture, (m1_setfam_1(k6_funct_2(esk1_0,esk2_0,esk3_0,k7_funct_2(esk1_0,esk2_0,esk3_0,X1)),X2)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(esk1_0)))|~m1_subset_1(X2,k1_zfmisc_1(esk1_0))|~m1_setfam_1(X1,X2)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19]), c_0_20])]), c_0_21]), c_0_22])).
% 0.13/0.36  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.36  cnf(c_0_28, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|m1_subset_1(k6_funct_2(X1,X2,X3,X4),k1_zfmisc_1(k1_zfmisc_1(X1)))|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.36  fof(c_0_29, plain, ![X18, X19, X20, X21]:(v1_xboole_0(X18)|v1_xboole_0(X19)|~v1_funct_1(X20)|~v1_funct_2(X20,X18,X19)|~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))|~m1_subset_1(X21,k1_zfmisc_1(k1_zfmisc_1(X18)))|m1_subset_1(k7_funct_2(X18,X19,X20,X21),k1_zfmisc_1(k1_zfmisc_1(X19)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_funct_2])])])).
% 0.13/0.36  cnf(c_0_30, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.36  cnf(c_0_31, negated_conjecture, (~m1_subset_1(k6_funct_2(esk1_0,esk2_0,esk3_0,k7_funct_2(esk1_0,esk2_0,esk3_0,esk4_0)),k1_zfmisc_1(k1_zfmisc_1(esk1_0)))|~m1_subset_1(k5_setfam_1(esk1_0,esk4_0),k1_zfmisc_1(esk1_0))|~m1_setfam_1(esk4_0,k5_setfam_1(esk1_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27])])).
% 0.13/0.36  cnf(c_0_32, negated_conjecture, (m1_subset_1(k6_funct_2(esk1_0,esk2_0,esk3_0,X1),k1_zfmisc_1(k1_zfmisc_1(esk1_0)))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_18]), c_0_19]), c_0_20])]), c_0_21]), c_0_22])).
% 0.13/0.36  cnf(c_0_33, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|m1_subset_1(k7_funct_2(X1,X2,X3,X4),k1_zfmisc_1(k1_zfmisc_1(X2)))|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.36  cnf(c_0_34, plain, (m1_setfam_1(X2,X1)|~r1_tarski(X1,k3_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.36  cnf(c_0_35, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_30])).
% 0.13/0.36  cnf(c_0_36, negated_conjecture, (~m1_subset_1(k7_funct_2(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k1_zfmisc_1(esk2_0)))|~m1_subset_1(k5_setfam_1(esk1_0,esk4_0),k1_zfmisc_1(esk1_0))|~m1_setfam_1(esk4_0,k5_setfam_1(esk1_0,esk4_0))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.13/0.36  cnf(c_0_37, negated_conjecture, (m1_subset_1(k7_funct_2(esk1_0,esk2_0,esk3_0,X1),k1_zfmisc_1(k1_zfmisc_1(esk2_0)))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(esk1_0)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_18]), c_0_19]), c_0_20])]), c_0_21]), c_0_22])).
% 0.13/0.36  cnf(c_0_38, plain, (m1_setfam_1(X1,k3_tarski(X1))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.13/0.36  cnf(c_0_39, negated_conjecture, (~m1_subset_1(k5_setfam_1(esk1_0,esk4_0),k1_zfmisc_1(esk1_0))|~m1_setfam_1(esk4_0,k5_setfam_1(esk1_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_27])])).
% 0.13/0.36  cnf(c_0_40, plain, (m1_setfam_1(X1,k5_setfam_1(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(spm,[status(thm)],[c_0_38, c_0_13])).
% 0.13/0.36  fof(c_0_41, plain, ![X10, X11]:(~m1_subset_1(X11,k1_zfmisc_1(k1_zfmisc_1(X10)))|m1_subset_1(k5_setfam_1(X10,X11),k1_zfmisc_1(X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_setfam_1])])).
% 0.13/0.36  cnf(c_0_42, negated_conjecture, (~m1_subset_1(k5_setfam_1(esk1_0,esk4_0),k1_zfmisc_1(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_27])])).
% 0.13/0.36  cnf(c_0_43, plain, (m1_subset_1(k5_setfam_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.13/0.36  cnf(c_0_44, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_27])]), ['proof']).
% 0.13/0.36  # SZS output end CNFRefutation
% 0.13/0.36  # Proof object total steps             : 45
% 0.13/0.36  # Proof object clause steps            : 28
% 0.13/0.36  # Proof object formula steps           : 17
% 0.13/0.36  # Proof object conjectures             : 19
% 0.13/0.36  # Proof object clause conjectures      : 16
% 0.13/0.36  # Proof object formula conjectures     : 3
% 0.13/0.36  # Proof object initial clauses used    : 15
% 0.13/0.36  # Proof object initial formulas used   : 8
% 0.13/0.36  # Proof object generating inferences   : 12
% 0.13/0.36  # Proof object simplifying inferences  : 24
% 0.13/0.36  # Training examples: 0 positive, 0 negative
% 0.13/0.36  # Parsed axioms                        : 8
% 0.13/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.36  # Initial clauses                      : 17
% 0.13/0.36  # Removed in clause preprocessing      : 0
% 0.13/0.36  # Initial clauses in saturation        : 17
% 0.13/0.36  # Processed clauses                    : 52
% 0.13/0.36  # ...of these trivial                  : 0
% 0.13/0.36  # ...subsumed                          : 3
% 0.13/0.36  # ...remaining for further processing  : 49
% 0.13/0.36  # Other redundant clauses eliminated   : 2
% 0.13/0.36  # Clauses deleted for lack of memory   : 0
% 0.13/0.36  # Backward-subsumed                    : 2
% 0.13/0.36  # Backward-rewritten                   : 0
% 0.13/0.36  # Generated clauses                    : 59
% 0.13/0.36  # ...of the previous two non-trivial   : 54
% 0.13/0.36  # Contextual simplify-reflections      : 0
% 0.13/0.36  # Paramodulations                      : 57
% 0.13/0.36  # Factorizations                       : 0
% 0.13/0.36  # Equation resolutions                 : 2
% 0.13/0.36  # Propositional unsat checks           : 0
% 0.13/0.36  #    Propositional check models        : 0
% 0.13/0.36  #    Propositional check unsatisfiable : 0
% 0.13/0.36  #    Propositional clauses             : 0
% 0.13/0.36  #    Propositional clauses after purity: 0
% 0.13/0.36  #    Propositional unsat core size     : 0
% 0.13/0.36  #    Propositional preprocessing time  : 0.000
% 0.13/0.36  #    Propositional encoding time       : 0.000
% 0.13/0.36  #    Propositional solver time         : 0.000
% 0.13/0.36  #    Success case prop preproc time    : 0.000
% 0.13/0.36  #    Success case prop encoding time   : 0.000
% 0.13/0.36  #    Success case prop solver time     : 0.000
% 0.13/0.36  # Current number of processed clauses  : 29
% 0.13/0.36  #    Positive orientable unit clauses  : 6
% 0.13/0.36  #    Positive unorientable unit clauses: 0
% 0.13/0.36  #    Negative unit clauses             : 4
% 0.13/0.36  #    Non-unit-clauses                  : 19
% 0.13/0.36  # Current number of unprocessed clauses: 33
% 0.13/0.36  # ...number of literals in the above   : 136
% 0.13/0.36  # Current number of archived formulas  : 0
% 0.13/0.36  # Current number of archived clauses   : 18
% 0.13/0.36  # Clause-clause subsumption calls (NU) : 173
% 0.13/0.36  # Rec. Clause-clause subsumption calls : 58
% 0.13/0.36  # Non-unit clause-clause subsumptions  : 5
% 0.13/0.36  # Unit Clause-clause subsumption calls : 3
% 0.13/0.36  # Rewrite failures with RHS unbound    : 0
% 0.13/0.36  # BW rewrite match attempts            : 0
% 0.13/0.36  # BW rewrite match successes           : 0
% 0.13/0.36  # Condensation attempts                : 0
% 0.13/0.36  # Condensation successes               : 0
% 0.13/0.36  # Termbank termtop insertions          : 2888
% 0.13/0.36  
% 0.13/0.36  # -------------------------------------------------
% 0.13/0.36  # User time                : 0.015 s
% 0.13/0.36  # System time              : 0.003 s
% 0.13/0.36  # Total time               : 0.018 s
% 0.13/0.36  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
