%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:07:43 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 230 expanded)
%              Number of clauses        :   33 (  78 expanded)
%              Number of leaves         :    8 (  56 expanded)
%              Depth                    :   11
%              Number of atoms          :  179 (1153 expanded)
%              Number of equality atoms :    9 (  21 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t183_funct_2,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,X1,X2)
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X2)))
                 => r1_tarski(k5_setfam_1(X2,k7_funct_2(X1,X2,X3,k6_funct_2(X1,X2,X3,X4))),k5_setfam_1(X2,X4)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t183_funct_2)).

fof(redefinition_k5_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => k5_setfam_1(X1,X2) = k3_tarski(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(dt_k7_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X2)
        & v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1))) )
     => m1_subset_1(k7_funct_2(X1,X2,X3,X4),k1_zfmisc_1(k1_zfmisc_1(X2))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_funct_2)).

fof(d12_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_setfam_1(X2,X1)
    <=> r1_tarski(X1,k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_setfam_1)).

fof(dt_k6_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X2)
        & v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X2))) )
     => m1_subset_1(k6_funct_2(X1,X2,X3,X4),k1_zfmisc_1(k1_zfmisc_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_funct_2)).

fof(t181_funct_2,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,X1,X2)
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X2)))
                 => ! [X5] :
                      ( m1_subset_1(X5,k1_zfmisc_1(X2))
                     => ( m1_setfam_1(k7_funct_2(X1,X2,X3,k6_funct_2(X1,X2,X3,X4)),X5)
                       => m1_setfam_1(X4,X5) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t181_funct_2)).

fof(dt_k5_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => m1_subset_1(k5_setfam_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_setfam_1)).

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
                    ( m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X2)))
                   => r1_tarski(k5_setfam_1(X2,k7_funct_2(X1,X2,X3,k6_funct_2(X1,X2,X3,X4))),k5_setfam_1(X2,X4)) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t183_funct_2])).

fof(c_0_9,plain,(
    ! [X12,X13] :
      ( ~ m1_subset_1(X13,k1_zfmisc_1(k1_zfmisc_1(X12)))
      | k5_setfam_1(X12,X13) = k3_tarski(X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k5_setfam_1])])).

fof(c_0_10,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0)
    & ~ v1_xboole_0(esk2_0)
    & v1_funct_1(esk3_0)
    & v1_funct_2(esk3_0,esk1_0,esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    & m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))
    & ~ r1_tarski(k5_setfam_1(esk2_0,k7_funct_2(esk1_0,esk2_0,esk3_0,k6_funct_2(esk1_0,esk2_0,esk3_0,esk4_0))),k5_setfam_1(esk2_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).

cnf(c_0_11,plain,
    ( k5_setfam_1(X2,X1) = k3_tarski(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_12,plain,(
    ! [X6,X7] :
      ( ( r1_tarski(X6,X7)
        | X6 != X7 )
      & ( r1_tarski(X7,X6)
        | X6 != X7 )
      & ( ~ r1_tarski(X6,X7)
        | ~ r1_tarski(X7,X6)
        | X6 = X7 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_13,negated_conjecture,
    ( ~ r1_tarski(k5_setfam_1(esk2_0,k7_funct_2(esk1_0,esk2_0,esk3_0,k6_funct_2(esk1_0,esk2_0,esk3_0,esk4_0))),k5_setfam_1(esk2_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( k5_setfam_1(X1,X2) = k5_setfam_1(X3,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X3))) ),
    inference(spm,[status(thm)],[c_0_11,c_0_11])).

fof(c_0_15,plain,(
    ! [X18,X19,X20,X21] :
      ( v1_xboole_0(X18)
      | v1_xboole_0(X19)
      | ~ v1_funct_1(X20)
      | ~ v1_funct_2(X20,X18,X19)
      | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))
      | ~ m1_subset_1(X21,k1_zfmisc_1(k1_zfmisc_1(X18)))
      | m1_subset_1(k7_funct_2(X18,X19,X20,X21),k1_zfmisc_1(k1_zfmisc_1(X19))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_funct_2])])])).

fof(c_0_16,plain,(
    ! [X8,X9] :
      ( ( ~ m1_setfam_1(X9,X8)
        | r1_tarski(X8,k3_tarski(X9)) )
      & ( ~ r1_tarski(X8,k3_tarski(X9))
        | m1_setfam_1(X9,X8) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_setfam_1])])).

cnf(c_0_17,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( ~ m1_subset_1(k7_funct_2(esk1_0,esk2_0,esk3_0,k6_funct_2(esk1_0,esk2_0,esk3_0,esk4_0)),k1_zfmisc_1(k1_zfmisc_1(esk2_0)))
    | ~ m1_subset_1(k7_funct_2(esk1_0,esk2_0,esk3_0,k6_funct_2(esk1_0,esk2_0,esk3_0,esk4_0)),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ r1_tarski(k5_setfam_1(X1,k7_funct_2(esk1_0,esk2_0,esk3_0,k6_funct_2(esk1_0,esk2_0,esk3_0,esk4_0))),k5_setfam_1(esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_19,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | m1_subset_1(k7_funct_2(X1,X2,X3,X4),k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_21,negated_conjecture,
    ( v1_funct_2(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_22,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_23,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_24,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_25,plain,(
    ! [X14,X15,X16,X17] :
      ( v1_xboole_0(X14)
      | v1_xboole_0(X15)
      | ~ v1_funct_1(X16)
      | ~ v1_funct_2(X16,X14,X15)
      | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))
      | ~ m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(X15)))
      | m1_subset_1(k6_funct_2(X14,X15,X16,X17),k1_zfmisc_1(k1_zfmisc_1(X14))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_funct_2])])])).

fof(c_0_26,plain,(
    ! [X22,X23,X24,X25,X26] :
      ( v1_xboole_0(X22)
      | v1_xboole_0(X23)
      | ~ v1_funct_1(X24)
      | ~ v1_funct_2(X24,X22,X23)
      | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))
      | ~ m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(X23)))
      | ~ m1_subset_1(X26,k1_zfmisc_1(X23))
      | ~ m1_setfam_1(k7_funct_2(X22,X23,X24,k6_funct_2(X22,X23,X24,X25)),X26)
      | m1_setfam_1(X25,X26) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t181_funct_2])])])])).

cnf(c_0_27,plain,
    ( m1_setfam_1(X2,X1)
    | ~ r1_tarski(X1,k3_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_17])).

fof(c_0_29,plain,(
    ! [X10,X11] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(k1_zfmisc_1(X10)))
      | m1_subset_1(k5_setfam_1(X10,X11),k1_zfmisc_1(X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_setfam_1])])).

cnf(c_0_30,negated_conjecture,
    ( ~ m1_subset_1(k7_funct_2(esk1_0,esk2_0,esk3_0,k6_funct_2(esk1_0,esk2_0,esk3_0,esk4_0)),k1_zfmisc_1(k1_zfmisc_1(esk2_0)))
    | ~ m1_subset_1(k7_funct_2(esk1_0,esk2_0,esk3_0,k6_funct_2(esk1_0,esk2_0,esk3_0,esk4_0)),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ r1_tarski(k3_tarski(k7_funct_2(esk1_0,esk2_0,esk3_0,k6_funct_2(esk1_0,esk2_0,esk3_0,esk4_0))),k5_setfam_1(esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_11])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(k7_funct_2(esk1_0,esk2_0,esk3_0,X1),k1_zfmisc_1(k1_zfmisc_1(esk2_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(esk1_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_22])]),c_0_23]),c_0_24])).

cnf(c_0_32,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | m1_subset_1(k6_funct_2(X1,X2,X3,X4),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | m1_setfam_1(X4,X5)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(X2))
    | ~ m1_setfam_1(k7_funct_2(X1,X2,X3,k6_funct_2(X1,X2,X3,X4)),X5) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( m1_setfam_1(X1,k3_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_35,plain,
    ( m1_subset_1(k5_setfam_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,negated_conjecture,
    ( ~ m1_subset_1(k7_funct_2(esk1_0,esk2_0,esk3_0,k6_funct_2(esk1_0,esk2_0,esk3_0,esk4_0)),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(k6_funct_2(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k1_zfmisc_1(esk1_0)))
    | ~ r1_tarski(k3_tarski(k7_funct_2(esk1_0,esk2_0,esk3_0,k6_funct_2(esk1_0,esk2_0,esk3_0,esk4_0))),k5_setfam_1(esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(k6_funct_2(esk1_0,esk2_0,esk3_0,X1),k1_zfmisc_1(k1_zfmisc_1(esk1_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(esk2_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_20]),c_0_21]),c_0_22])]),c_0_23]),c_0_24])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_39,plain,
    ( r1_tarski(X2,k3_tarski(X1))
    | ~ m1_setfam_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_40,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | m1_setfam_1(X3,k3_tarski(k7_funct_2(X1,X2,X4,k6_funct_2(X1,X2,X4,X3))))
    | ~ v1_funct_2(X4,X1,X2)
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(k3_tarski(k7_funct_2(X1,X2,X4,k6_funct_2(X1,X2,X4,X3))),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_41,plain,
    ( m1_subset_1(k3_tarski(X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(spm,[status(thm)],[c_0_35,c_0_11])).

cnf(c_0_42,negated_conjecture,
    ( ~ m1_subset_1(k7_funct_2(esk1_0,esk2_0,esk3_0,k6_funct_2(esk1_0,esk2_0,esk3_0,esk4_0)),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ r1_tarski(k3_tarski(k7_funct_2(esk1_0,esk2_0,esk3_0,k6_funct_2(esk1_0,esk2_0,esk3_0,esk4_0))),k5_setfam_1(esk2_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38])])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,k5_setfam_1(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_setfam_1(X3,X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_11])).

cnf(c_0_44,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | m1_setfam_1(X3,k3_tarski(k7_funct_2(X2,X1,X4,k6_funct_2(X2,X1,X4,X3))))
    | ~ v1_funct_2(X4,X2,X1)
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(k7_funct_2(X2,X1,X4,k6_funct_2(X2,X1,X4,X3)),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_45,negated_conjecture,
    ( ~ m1_subset_1(k7_funct_2(esk1_0,esk2_0,esk3_0,k6_funct_2(esk1_0,esk2_0,esk3_0,esk4_0)),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_setfam_1(esk4_0,k3_tarski(k7_funct_2(esk1_0,esk2_0,esk3_0,k6_funct_2(esk1_0,esk2_0,esk3_0,esk4_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_38])])).

cnf(c_0_46,negated_conjecture,
    ( m1_setfam_1(X1,k3_tarski(k7_funct_2(esk1_0,esk2_0,esk3_0,k6_funct_2(esk1_0,esk2_0,esk3_0,X1))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(esk2_0))) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_31]),c_0_21]),c_0_22]),c_0_20])]),c_0_23]),c_0_24]),c_0_37])).

cnf(c_0_47,negated_conjecture,
    ( ~ m1_subset_1(k7_funct_2(esk1_0,esk2_0,esk3_0,k6_funct_2(esk1_0,esk2_0,esk3_0,esk4_0)),k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_38])])).

cnf(c_0_48,negated_conjecture,
    ( ~ m1_subset_1(k6_funct_2(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k1_zfmisc_1(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_47,c_0_31])).

cnf(c_0_49,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_37]),c_0_38])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:28:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.39  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.39  #
% 0.20/0.39  # Preprocessing time       : 0.028 s
% 0.20/0.39  # Presaturation interreduction done
% 0.20/0.39  
% 0.20/0.39  # Proof found!
% 0.20/0.39  # SZS status Theorem
% 0.20/0.39  # SZS output start CNFRefutation
% 0.20/0.39  fof(t183_funct_2, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X2)))=>r1_tarski(k5_setfam_1(X2,k7_funct_2(X1,X2,X3,k6_funct_2(X1,X2,X3,X4))),k5_setfam_1(X2,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t183_funct_2)).
% 0.20/0.39  fof(redefinition_k5_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>k5_setfam_1(X1,X2)=k3_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_setfam_1)).
% 0.20/0.39  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.39  fof(dt_k7_funct_2, axiom, ![X1, X2, X3, X4]:((((((~(v1_xboole_0(X1))&~(v1_xboole_0(X2)))&v1_funct_1(X3))&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1))))=>m1_subset_1(k7_funct_2(X1,X2,X3,X4),k1_zfmisc_1(k1_zfmisc_1(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_funct_2)).
% 0.20/0.39  fof(d12_setfam_1, axiom, ![X1, X2]:(m1_setfam_1(X2,X1)<=>r1_tarski(X1,k3_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_setfam_1)).
% 0.20/0.39  fof(dt_k6_funct_2, axiom, ![X1, X2, X3, X4]:((((((~(v1_xboole_0(X1))&~(v1_xboole_0(X2)))&v1_funct_1(X3))&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X2))))=>m1_subset_1(k6_funct_2(X1,X2,X3,X4),k1_zfmisc_1(k1_zfmisc_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_funct_2)).
% 0.20/0.39  fof(t181_funct_2, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X2)))=>![X5]:(m1_subset_1(X5,k1_zfmisc_1(X2))=>(m1_setfam_1(k7_funct_2(X1,X2,X3,k6_funct_2(X1,X2,X3,X4)),X5)=>m1_setfam_1(X4,X5))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t181_funct_2)).
% 0.20/0.39  fof(dt_k5_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>m1_subset_1(k5_setfam_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_setfam_1)).
% 0.20/0.39  fof(c_0_8, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X2)))=>r1_tarski(k5_setfam_1(X2,k7_funct_2(X1,X2,X3,k6_funct_2(X1,X2,X3,X4))),k5_setfam_1(X2,X4))))))), inference(assume_negation,[status(cth)],[t183_funct_2])).
% 0.20/0.39  fof(c_0_9, plain, ![X12, X13]:(~m1_subset_1(X13,k1_zfmisc_1(k1_zfmisc_1(X12)))|k5_setfam_1(X12,X13)=k3_tarski(X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k5_setfam_1])])).
% 0.20/0.39  fof(c_0_10, negated_conjecture, (~v1_xboole_0(esk1_0)&(~v1_xboole_0(esk2_0)&(((v1_funct_1(esk3_0)&v1_funct_2(esk3_0,esk1_0,esk2_0))&m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))))&(m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))&~r1_tarski(k5_setfam_1(esk2_0,k7_funct_2(esk1_0,esk2_0,esk3_0,k6_funct_2(esk1_0,esk2_0,esk3_0,esk4_0))),k5_setfam_1(esk2_0,esk4_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).
% 0.20/0.39  cnf(c_0_11, plain, (k5_setfam_1(X2,X1)=k3_tarski(X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.39  fof(c_0_12, plain, ![X6, X7]:(((r1_tarski(X6,X7)|X6!=X7)&(r1_tarski(X7,X6)|X6!=X7))&(~r1_tarski(X6,X7)|~r1_tarski(X7,X6)|X6=X7)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.39  cnf(c_0_13, negated_conjecture, (~r1_tarski(k5_setfam_1(esk2_0,k7_funct_2(esk1_0,esk2_0,esk3_0,k6_funct_2(esk1_0,esk2_0,esk3_0,esk4_0))),k5_setfam_1(esk2_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.39  cnf(c_0_14, plain, (k5_setfam_1(X1,X2)=k5_setfam_1(X3,X2)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X3)))), inference(spm,[status(thm)],[c_0_11, c_0_11])).
% 0.20/0.39  fof(c_0_15, plain, ![X18, X19, X20, X21]:(v1_xboole_0(X18)|v1_xboole_0(X19)|~v1_funct_1(X20)|~v1_funct_2(X20,X18,X19)|~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))|~m1_subset_1(X21,k1_zfmisc_1(k1_zfmisc_1(X18)))|m1_subset_1(k7_funct_2(X18,X19,X20,X21),k1_zfmisc_1(k1_zfmisc_1(X19)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_funct_2])])])).
% 0.20/0.39  fof(c_0_16, plain, ![X8, X9]:((~m1_setfam_1(X9,X8)|r1_tarski(X8,k3_tarski(X9)))&(~r1_tarski(X8,k3_tarski(X9))|m1_setfam_1(X9,X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_setfam_1])])).
% 0.20/0.39  cnf(c_0_17, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.39  cnf(c_0_18, negated_conjecture, (~m1_subset_1(k7_funct_2(esk1_0,esk2_0,esk3_0,k6_funct_2(esk1_0,esk2_0,esk3_0,esk4_0)),k1_zfmisc_1(k1_zfmisc_1(esk2_0)))|~m1_subset_1(k7_funct_2(esk1_0,esk2_0,esk3_0,k6_funct_2(esk1_0,esk2_0,esk3_0,esk4_0)),k1_zfmisc_1(k1_zfmisc_1(X1)))|~r1_tarski(k5_setfam_1(X1,k7_funct_2(esk1_0,esk2_0,esk3_0,k6_funct_2(esk1_0,esk2_0,esk3_0,esk4_0))),k5_setfam_1(esk2_0,esk4_0))), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.20/0.39  cnf(c_0_19, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|m1_subset_1(k7_funct_2(X1,X2,X3,X4),k1_zfmisc_1(k1_zfmisc_1(X2)))|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.39  cnf(c_0_20, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.39  cnf(c_0_21, negated_conjecture, (v1_funct_2(esk3_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.39  cnf(c_0_22, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.39  cnf(c_0_23, negated_conjecture, (~v1_xboole_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.39  cnf(c_0_24, negated_conjecture, (~v1_xboole_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.39  fof(c_0_25, plain, ![X14, X15, X16, X17]:(v1_xboole_0(X14)|v1_xboole_0(X15)|~v1_funct_1(X16)|~v1_funct_2(X16,X14,X15)|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))|~m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(X15)))|m1_subset_1(k6_funct_2(X14,X15,X16,X17),k1_zfmisc_1(k1_zfmisc_1(X14)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_funct_2])])])).
% 0.20/0.39  fof(c_0_26, plain, ![X22, X23, X24, X25, X26]:(v1_xboole_0(X22)|(v1_xboole_0(X23)|(~v1_funct_1(X24)|~v1_funct_2(X24,X22,X23)|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))|(~m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(X23)))|(~m1_subset_1(X26,k1_zfmisc_1(X23))|(~m1_setfam_1(k7_funct_2(X22,X23,X24,k6_funct_2(X22,X23,X24,X25)),X26)|m1_setfam_1(X25,X26))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t181_funct_2])])])])).
% 0.20/0.39  cnf(c_0_27, plain, (m1_setfam_1(X2,X1)|~r1_tarski(X1,k3_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.39  cnf(c_0_28, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_17])).
% 0.20/0.39  fof(c_0_29, plain, ![X10, X11]:(~m1_subset_1(X11,k1_zfmisc_1(k1_zfmisc_1(X10)))|m1_subset_1(k5_setfam_1(X10,X11),k1_zfmisc_1(X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_setfam_1])])).
% 0.20/0.39  cnf(c_0_30, negated_conjecture, (~m1_subset_1(k7_funct_2(esk1_0,esk2_0,esk3_0,k6_funct_2(esk1_0,esk2_0,esk3_0,esk4_0)),k1_zfmisc_1(k1_zfmisc_1(esk2_0)))|~m1_subset_1(k7_funct_2(esk1_0,esk2_0,esk3_0,k6_funct_2(esk1_0,esk2_0,esk3_0,esk4_0)),k1_zfmisc_1(k1_zfmisc_1(X1)))|~r1_tarski(k3_tarski(k7_funct_2(esk1_0,esk2_0,esk3_0,k6_funct_2(esk1_0,esk2_0,esk3_0,esk4_0))),k5_setfam_1(esk2_0,esk4_0))), inference(spm,[status(thm)],[c_0_18, c_0_11])).
% 0.20/0.39  cnf(c_0_31, negated_conjecture, (m1_subset_1(k7_funct_2(esk1_0,esk2_0,esk3_0,X1),k1_zfmisc_1(k1_zfmisc_1(esk2_0)))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(esk1_0)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21]), c_0_22])]), c_0_23]), c_0_24])).
% 0.20/0.39  cnf(c_0_32, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|m1_subset_1(k6_funct_2(X1,X2,X3,X4),k1_zfmisc_1(k1_zfmisc_1(X1)))|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.39  cnf(c_0_33, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|m1_setfam_1(X4,X5)|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X2)))|~m1_subset_1(X5,k1_zfmisc_1(X2))|~m1_setfam_1(k7_funct_2(X1,X2,X3,k6_funct_2(X1,X2,X3,X4)),X5)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.39  cnf(c_0_34, plain, (m1_setfam_1(X1,k3_tarski(X1))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.20/0.39  cnf(c_0_35, plain, (m1_subset_1(k5_setfam_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.39  cnf(c_0_36, negated_conjecture, (~m1_subset_1(k7_funct_2(esk1_0,esk2_0,esk3_0,k6_funct_2(esk1_0,esk2_0,esk3_0,esk4_0)),k1_zfmisc_1(k1_zfmisc_1(X1)))|~m1_subset_1(k6_funct_2(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k1_zfmisc_1(esk1_0)))|~r1_tarski(k3_tarski(k7_funct_2(esk1_0,esk2_0,esk3_0,k6_funct_2(esk1_0,esk2_0,esk3_0,esk4_0))),k5_setfam_1(esk2_0,esk4_0))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.20/0.39  cnf(c_0_37, negated_conjecture, (m1_subset_1(k6_funct_2(esk1_0,esk2_0,esk3_0,X1),k1_zfmisc_1(k1_zfmisc_1(esk1_0)))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_20]), c_0_21]), c_0_22])]), c_0_23]), c_0_24])).
% 0.20/0.39  cnf(c_0_38, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.39  cnf(c_0_39, plain, (r1_tarski(X2,k3_tarski(X1))|~m1_setfam_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.39  cnf(c_0_40, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|m1_setfam_1(X3,k3_tarski(k7_funct_2(X1,X2,X4,k6_funct_2(X1,X2,X4,X3))))|~v1_funct_2(X4,X1,X2)|~v1_funct_1(X4)|~m1_subset_1(k3_tarski(k7_funct_2(X1,X2,X4,k6_funct_2(X1,X2,X4,X3))),k1_zfmisc_1(X2))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.20/0.39  cnf(c_0_41, plain, (m1_subset_1(k3_tarski(X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(spm,[status(thm)],[c_0_35, c_0_11])).
% 0.20/0.39  cnf(c_0_42, negated_conjecture, (~m1_subset_1(k7_funct_2(esk1_0,esk2_0,esk3_0,k6_funct_2(esk1_0,esk2_0,esk3_0,esk4_0)),k1_zfmisc_1(k1_zfmisc_1(X1)))|~r1_tarski(k3_tarski(k7_funct_2(esk1_0,esk2_0,esk3_0,k6_funct_2(esk1_0,esk2_0,esk3_0,esk4_0))),k5_setfam_1(esk2_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38])])).
% 0.20/0.39  cnf(c_0_43, plain, (r1_tarski(X1,k5_setfam_1(X2,X3))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))|~m1_setfam_1(X3,X1)), inference(spm,[status(thm)],[c_0_39, c_0_11])).
% 0.20/0.39  cnf(c_0_44, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|m1_setfam_1(X3,k3_tarski(k7_funct_2(X2,X1,X4,k6_funct_2(X2,X1,X4,X3))))|~v1_funct_2(X4,X2,X1)|~v1_funct_1(X4)|~m1_subset_1(k7_funct_2(X2,X1,X4,k6_funct_2(X2,X1,X4,X3)),k1_zfmisc_1(k1_zfmisc_1(X1)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.20/0.39  cnf(c_0_45, negated_conjecture, (~m1_subset_1(k7_funct_2(esk1_0,esk2_0,esk3_0,k6_funct_2(esk1_0,esk2_0,esk3_0,esk4_0)),k1_zfmisc_1(k1_zfmisc_1(X1)))|~m1_setfam_1(esk4_0,k3_tarski(k7_funct_2(esk1_0,esk2_0,esk3_0,k6_funct_2(esk1_0,esk2_0,esk3_0,esk4_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_38])])).
% 0.20/0.39  cnf(c_0_46, negated_conjecture, (m1_setfam_1(X1,k3_tarski(k7_funct_2(esk1_0,esk2_0,esk3_0,k6_funct_2(esk1_0,esk2_0,esk3_0,X1))))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_31]), c_0_21]), c_0_22]), c_0_20])]), c_0_23]), c_0_24]), c_0_37])).
% 0.20/0.39  cnf(c_0_47, negated_conjecture, (~m1_subset_1(k7_funct_2(esk1_0,esk2_0,esk3_0,k6_funct_2(esk1_0,esk2_0,esk3_0,esk4_0)),k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_38])])).
% 0.20/0.39  cnf(c_0_48, negated_conjecture, (~m1_subset_1(k6_funct_2(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k1_zfmisc_1(esk1_0)))), inference(spm,[status(thm)],[c_0_47, c_0_31])).
% 0.20/0.39  cnf(c_0_49, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_37]), c_0_38])]), ['proof']).
% 0.20/0.39  # SZS output end CNFRefutation
% 0.20/0.39  # Proof object total steps             : 50
% 0.20/0.39  # Proof object clause steps            : 33
% 0.20/0.39  # Proof object formula steps           : 17
% 0.20/0.39  # Proof object conjectures             : 21
% 0.20/0.39  # Proof object clause conjectures      : 18
% 0.20/0.39  # Proof object formula conjectures     : 3
% 0.20/0.39  # Proof object initial clauses used    : 15
% 0.20/0.39  # Proof object initial formulas used   : 8
% 0.20/0.39  # Proof object generating inferences   : 17
% 0.20/0.39  # Proof object simplifying inferences  : 26
% 0.20/0.39  # Training examples: 0 positive, 0 negative
% 0.20/0.39  # Parsed axioms                        : 8
% 0.20/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.39  # Initial clauses                      : 17
% 0.20/0.39  # Removed in clause preprocessing      : 0
% 0.20/0.39  # Initial clauses in saturation        : 17
% 0.20/0.39  # Processed clauses                    : 284
% 0.20/0.39  # ...of these trivial                  : 1
% 0.20/0.39  # ...subsumed                          : 182
% 0.20/0.39  # ...remaining for further processing  : 101
% 0.20/0.39  # Other redundant clauses eliminated   : 2
% 0.20/0.39  # Clauses deleted for lack of memory   : 0
% 0.20/0.39  # Backward-subsumed                    : 8
% 0.20/0.39  # Backward-rewritten                   : 4
% 0.20/0.39  # Generated clauses                    : 320
% 0.20/0.39  # ...of the previous two non-trivial   : 309
% 0.20/0.39  # Contextual simplify-reflections      : 1
% 0.20/0.39  # Paramodulations                      : 318
% 0.20/0.39  # Factorizations                       : 0
% 0.20/0.39  # Equation resolutions                 : 2
% 0.20/0.39  # Propositional unsat checks           : 0
% 0.20/0.39  #    Propositional check models        : 0
% 0.20/0.39  #    Propositional check unsatisfiable : 0
% 0.20/0.39  #    Propositional clauses             : 0
% 0.20/0.39  #    Propositional clauses after purity: 0
% 0.20/0.39  #    Propositional unsat core size     : 0
% 0.20/0.39  #    Propositional preprocessing time  : 0.000
% 0.20/0.39  #    Propositional encoding time       : 0.000
% 0.20/0.39  #    Propositional solver time         : 0.000
% 0.20/0.39  #    Success case prop preproc time    : 0.000
% 0.20/0.39  #    Success case prop encoding time   : 0.000
% 0.20/0.39  #    Success case prop solver time     : 0.000
% 0.20/0.39  # Current number of processed clauses  : 71
% 0.20/0.39  #    Positive orientable unit clauses  : 9
% 0.20/0.39  #    Positive unorientable unit clauses: 0
% 0.20/0.39  #    Negative unit clauses             : 6
% 0.20/0.39  #    Non-unit-clauses                  : 56
% 0.20/0.39  # Current number of unprocessed clauses: 47
% 0.20/0.39  # ...number of literals in the above   : 321
% 0.20/0.39  # Current number of archived formulas  : 0
% 0.20/0.39  # Current number of archived clauses   : 28
% 0.20/0.39  # Clause-clause subsumption calls (NU) : 2119
% 0.20/0.39  # Rec. Clause-clause subsumption calls : 645
% 0.20/0.39  # Non-unit clause-clause subsumptions  : 183
% 0.20/0.39  # Unit Clause-clause subsumption calls : 30
% 0.20/0.39  # Rewrite failures with RHS unbound    : 0
% 0.20/0.39  # BW rewrite match attempts            : 2
% 0.20/0.39  # BW rewrite match successes           : 2
% 0.20/0.39  # Condensation attempts                : 0
% 0.20/0.39  # Condensation successes               : 0
% 0.20/0.39  # Termbank termtop insertions          : 11807
% 0.20/0.39  
% 0.20/0.39  # -------------------------------------------------
% 0.20/0.39  # User time                : 0.041 s
% 0.20/0.39  # System time              : 0.006 s
% 0.20/0.39  # Total time               : 0.048 s
% 0.20/0.39  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
