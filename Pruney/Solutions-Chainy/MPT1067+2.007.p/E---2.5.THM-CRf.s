%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:07:44 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 129 expanded)
%              Number of clauses        :   29 (  45 expanded)
%              Number of leaves         :   10 (  32 expanded)
%              Depth                    :   10
%              Number of atoms          :  198 ( 628 expanded)
%              Number of equality atoms :   10 (  19 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal clause size      :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d12_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_setfam_1(X2,X1)
    <=> r1_tarski(X1,k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_setfam_1)).

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

fof(dt_k5_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => m1_subset_1(k5_setfam_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_setfam_1)).

fof(redefinition_k5_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => k5_setfam_1(X1,X2) = k3_tarski(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

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

fof(t60_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( m1_setfam_1(X2,X1)
      <=> k5_setfam_1(X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_setfam_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

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

fof(t100_zfmisc_1,axiom,(
    ! [X1] : r1_tarski(X1,k1_zfmisc_1(k3_tarski(X1))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_zfmisc_1)).

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

fof(c_0_10,plain,(
    ! [X7,X8] :
      ( ( ~ m1_setfam_1(X8,X7)
        | r1_tarski(X7,k3_tarski(X8)) )
      & ( ~ r1_tarski(X7,k3_tarski(X8))
        | m1_setfam_1(X8,X7) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_setfam_1])])).

fof(c_0_11,plain,(
    ! [X25,X26,X27,X28,X29] :
      ( v1_xboole_0(X25)
      | v1_xboole_0(X26)
      | ~ v1_funct_1(X27)
      | ~ v1_funct_2(X27,X25,X26)
      | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))
      | ~ m1_subset_1(X28,k1_zfmisc_1(k1_zfmisc_1(X25)))
      | ~ m1_subset_1(X29,k1_zfmisc_1(X25))
      | ~ m1_setfam_1(X28,X29)
      | m1_setfam_1(k6_funct_2(X25,X26,X27,k7_funct_2(X25,X26,X27,X28)),X29) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t182_funct_2])])])])).

fof(c_0_12,plain,(
    ! [X9,X10] :
      ( ~ m1_subset_1(X10,k1_zfmisc_1(k1_zfmisc_1(X9)))
      | m1_subset_1(k5_setfam_1(X9,X10),k1_zfmisc_1(X9)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_setfam_1])])).

fof(c_0_13,plain,(
    ! [X11,X12] :
      ( ~ m1_subset_1(X12,k1_zfmisc_1(k1_zfmisc_1(X11)))
      | k5_setfam_1(X11,X12) = k3_tarski(X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k5_setfam_1])])).

cnf(c_0_14,plain,
    ( r1_tarski(X2,k3_tarski(X1))
    | ~ m1_setfam_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | m1_setfam_1(k6_funct_2(X1,X2,X3,k7_funct_2(X1,X2,X3,X4)),X5)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(X1))
    | ~ m1_setfam_1(X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( m1_subset_1(k5_setfam_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( k5_setfam_1(X2,X1) = k3_tarski(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_18,negated_conjecture,(
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

cnf(c_0_19,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | r1_tarski(X3,k3_tarski(k6_funct_2(X1,X2,X4,k7_funct_2(X1,X2,X4,X5))))
    | ~ v1_funct_2(X4,X1,X2)
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_setfam_1(X5,X3) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_20,plain,
    ( m1_subset_1(k3_tarski(X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

fof(c_0_21,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0)
    & ~ v1_xboole_0(esk2_0)
    & v1_funct_1(esk3_0)
    & v1_funct_2(esk3_0,esk1_0,esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    & m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk1_0)))
    & ~ r1_tarski(k5_setfam_1(esk1_0,esk4_0),k5_setfam_1(esk1_0,k6_funct_2(esk1_0,esk2_0,esk3_0,k7_funct_2(esk1_0,esk2_0,esk3_0,esk4_0)))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_18])])])])).

fof(c_0_22,plain,(
    ! [X15,X16] :
      ( ( ~ m1_setfam_1(X16,X15)
        | k5_setfam_1(X15,X16) = X15
        | ~ m1_subset_1(X16,k1_zfmisc_1(k1_zfmisc_1(X15))) )
      & ( k5_setfam_1(X15,X16) != X15
        | m1_setfam_1(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k1_zfmisc_1(X15))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_setfam_1])])])).

cnf(c_0_23,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | r1_tarski(k3_tarski(X3),k3_tarski(k6_funct_2(X2,X1,X4,k7_funct_2(X2,X1,X4,X5))))
    | ~ v1_funct_2(X4,X2,X1)
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_setfam_1(X5,k3_tarski(X3)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,plain,
    ( m1_setfam_1(X2,X1)
    | k5_setfam_1(X1,X2) != X1
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( ~ r1_tarski(k5_setfam_1(esk1_0,esk4_0),k5_setfam_1(esk1_0,k6_funct_2(esk1_0,esk2_0,esk3_0,k7_funct_2(esk1_0,esk2_0,esk3_0,esk4_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( v1_xboole_0(X1)
    | r1_tarski(k3_tarski(esk4_0),k3_tarski(k6_funct_2(esk1_0,X1,X2,k7_funct_2(esk1_0,X1,X2,X3))))
    | ~ v1_funct_2(X2,esk1_0,X1)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(esk1_0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(esk1_0)))
    | ~ m1_setfam_1(X3,k3_tarski(esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])).

cnf(c_0_29,plain,
    ( m1_setfam_1(X1,X2)
    | k3_tarski(X1) != X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_17])).

fof(c_0_30,plain,(
    ! [X13,X14] :
      ( ( ~ m1_subset_1(X13,k1_zfmisc_1(X14))
        | r1_tarski(X13,X14) )
      & ( ~ r1_tarski(X13,X14)
        | m1_subset_1(X13,k1_zfmisc_1(X14)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_31,negated_conjecture,
    ( ~ r1_tarski(k3_tarski(esk4_0),k5_setfam_1(esk1_0,k6_funct_2(esk1_0,esk2_0,esk3_0,k7_funct_2(esk1_0,esk2_0,esk3_0,esk4_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_17]),c_0_24])])).

fof(c_0_32,plain,(
    ! [X17,X18,X19,X20] :
      ( v1_xboole_0(X17)
      | v1_xboole_0(X18)
      | ~ v1_funct_1(X19)
      | ~ v1_funct_2(X19,X17,X18)
      | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))
      | ~ m1_subset_1(X20,k1_zfmisc_1(k1_zfmisc_1(X18)))
      | m1_subset_1(k6_funct_2(X17,X18,X19,X20),k1_zfmisc_1(k1_zfmisc_1(X17))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_funct_2])])])).

cnf(c_0_33,negated_conjecture,
    ( v1_xboole_0(X1)
    | r1_tarski(k3_tarski(esk4_0),k3_tarski(k6_funct_2(esk1_0,X1,X2,k7_funct_2(esk1_0,X1,X2,X3))))
    | k3_tarski(X3) != k3_tarski(esk4_0)
    | ~ v1_funct_2(X2,esk1_0,X1)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(k3_tarski(esk4_0))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(esk1_0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_34,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_35,plain,(
    ! [X6] : r1_tarski(X6,k1_zfmisc_1(k3_tarski(X6))) ),
    inference(variable_rename,[status(thm)],[t100_zfmisc_1])).

cnf(c_0_36,negated_conjecture,
    ( ~ m1_subset_1(k6_funct_2(esk1_0,esk2_0,esk3_0,k7_funct_2(esk1_0,esk2_0,esk3_0,esk4_0)),k1_zfmisc_1(k1_zfmisc_1(esk1_0)))
    | ~ r1_tarski(k3_tarski(esk4_0),k3_tarski(k6_funct_2(esk1_0,esk2_0,esk3_0,k7_funct_2(esk1_0,esk2_0,esk3_0,esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_17])).

cnf(c_0_37,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | m1_subset_1(k6_funct_2(X1,X2,X3,X4),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_38,negated_conjecture,
    ( v1_funct_2(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_39,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_41,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_42,negated_conjecture,
    ( v1_xboole_0(X1)
    | r1_tarski(k3_tarski(esk4_0),k3_tarski(k6_funct_2(esk1_0,X1,X2,k7_funct_2(esk1_0,X1,X2,X3))))
    | k3_tarski(X3) != k3_tarski(esk4_0)
    | ~ v1_funct_2(X2,esk1_0,X1)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(esk1_0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(esk1_0)))
    | ~ r1_tarski(X3,k1_zfmisc_1(k3_tarski(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,k1_zfmisc_1(k3_tarski(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_44,negated_conjecture,
    ( ~ m1_subset_1(k7_funct_2(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k1_zfmisc_1(esk2_0)))
    | ~ r1_tarski(k3_tarski(esk4_0),k3_tarski(k6_funct_2(esk1_0,esk2_0,esk3_0,k7_funct_2(esk1_0,esk2_0,esk3_0,esk4_0)))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38]),c_0_39]),c_0_40])]),c_0_41]),c_0_25])).

cnf(c_0_45,negated_conjecture,
    ( v1_xboole_0(X1)
    | r1_tarski(k3_tarski(esk4_0),k3_tarski(k6_funct_2(esk1_0,X1,X2,k7_funct_2(esk1_0,X1,X2,esk4_0))))
    | ~ v1_funct_2(X2,esk1_0,X1)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(esk1_0,X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_24])])).

fof(c_0_46,plain,(
    ! [X21,X22,X23,X24] :
      ( v1_xboole_0(X21)
      | v1_xboole_0(X22)
      | ~ v1_funct_1(X23)
      | ~ v1_funct_2(X23,X21,X22)
      | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))
      | ~ m1_subset_1(X24,k1_zfmisc_1(k1_zfmisc_1(X21)))
      | m1_subset_1(k7_funct_2(X21,X22,X23,X24),k1_zfmisc_1(k1_zfmisc_1(X22))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_funct_2])])])).

cnf(c_0_47,negated_conjecture,
    ( ~ m1_subset_1(k7_funct_2(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k1_zfmisc_1(esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_38]),c_0_39]),c_0_40])]),c_0_41])).

cnf(c_0_48,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | m1_subset_1(k7_funct_2(X1,X2,X3,X4),k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_49,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_38]),c_0_39]),c_0_40]),c_0_24])]),c_0_41]),c_0_25]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:38:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.57  # AutoSched0-Mode selected heuristic G_E___208_B02_F1_AE_CS_SP_PS_S0Y
% 0.20/0.57  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.57  #
% 0.20/0.57  # Preprocessing time       : 0.027 s
% 0.20/0.57  # Presaturation interreduction done
% 0.20/0.57  
% 0.20/0.57  # Proof found!
% 0.20/0.57  # SZS status Theorem
% 0.20/0.57  # SZS output start CNFRefutation
% 0.20/0.57  fof(d12_setfam_1, axiom, ![X1, X2]:(m1_setfam_1(X2,X1)<=>r1_tarski(X1,k3_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_setfam_1)).
% 0.20/0.57  fof(t182_funct_2, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1)))=>![X5]:(m1_subset_1(X5,k1_zfmisc_1(X1))=>(m1_setfam_1(X4,X5)=>m1_setfam_1(k6_funct_2(X1,X2,X3,k7_funct_2(X1,X2,X3,X4)),X5))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_funct_2)).
% 0.20/0.57  fof(dt_k5_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>m1_subset_1(k5_setfam_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_setfam_1)).
% 0.20/0.57  fof(redefinition_k5_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>k5_setfam_1(X1,X2)=k3_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_setfam_1)).
% 0.20/0.57  fof(t184_funct_2, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1)))=>r1_tarski(k5_setfam_1(X1,X4),k5_setfam_1(X1,k6_funct_2(X1,X2,X3,k7_funct_2(X1,X2,X3,X4)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t184_funct_2)).
% 0.20/0.57  fof(t60_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(m1_setfam_1(X2,X1)<=>k5_setfam_1(X1,X2)=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_setfam_1)).
% 0.20/0.57  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.57  fof(dt_k6_funct_2, axiom, ![X1, X2, X3, X4]:((((((~(v1_xboole_0(X1))&~(v1_xboole_0(X2)))&v1_funct_1(X3))&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X2))))=>m1_subset_1(k6_funct_2(X1,X2,X3,X4),k1_zfmisc_1(k1_zfmisc_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_funct_2)).
% 0.20/0.57  fof(t100_zfmisc_1, axiom, ![X1]:r1_tarski(X1,k1_zfmisc_1(k3_tarski(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_zfmisc_1)).
% 0.20/0.57  fof(dt_k7_funct_2, axiom, ![X1, X2, X3, X4]:((((((~(v1_xboole_0(X1))&~(v1_xboole_0(X2)))&v1_funct_1(X3))&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1))))=>m1_subset_1(k7_funct_2(X1,X2,X3,X4),k1_zfmisc_1(k1_zfmisc_1(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_funct_2)).
% 0.20/0.57  fof(c_0_10, plain, ![X7, X8]:((~m1_setfam_1(X8,X7)|r1_tarski(X7,k3_tarski(X8)))&(~r1_tarski(X7,k3_tarski(X8))|m1_setfam_1(X8,X7))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_setfam_1])])).
% 0.20/0.57  fof(c_0_11, plain, ![X25, X26, X27, X28, X29]:(v1_xboole_0(X25)|(v1_xboole_0(X26)|(~v1_funct_1(X27)|~v1_funct_2(X27,X25,X26)|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))|(~m1_subset_1(X28,k1_zfmisc_1(k1_zfmisc_1(X25)))|(~m1_subset_1(X29,k1_zfmisc_1(X25))|(~m1_setfam_1(X28,X29)|m1_setfam_1(k6_funct_2(X25,X26,X27,k7_funct_2(X25,X26,X27,X28)),X29))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t182_funct_2])])])])).
% 0.20/0.57  fof(c_0_12, plain, ![X9, X10]:(~m1_subset_1(X10,k1_zfmisc_1(k1_zfmisc_1(X9)))|m1_subset_1(k5_setfam_1(X9,X10),k1_zfmisc_1(X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_setfam_1])])).
% 0.20/0.57  fof(c_0_13, plain, ![X11, X12]:(~m1_subset_1(X12,k1_zfmisc_1(k1_zfmisc_1(X11)))|k5_setfam_1(X11,X12)=k3_tarski(X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k5_setfam_1])])).
% 0.20/0.57  cnf(c_0_14, plain, (r1_tarski(X2,k3_tarski(X1))|~m1_setfam_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.57  cnf(c_0_15, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|m1_setfam_1(k6_funct_2(X1,X2,X3,k7_funct_2(X1,X2,X3,X4)),X5)|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1)))|~m1_subset_1(X5,k1_zfmisc_1(X1))|~m1_setfam_1(X4,X5)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.57  cnf(c_0_16, plain, (m1_subset_1(k5_setfam_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.57  cnf(c_0_17, plain, (k5_setfam_1(X2,X1)=k3_tarski(X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.57  fof(c_0_18, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1)))=>r1_tarski(k5_setfam_1(X1,X4),k5_setfam_1(X1,k6_funct_2(X1,X2,X3,k7_funct_2(X1,X2,X3,X4))))))))), inference(assume_negation,[status(cth)],[t184_funct_2])).
% 0.20/0.57  cnf(c_0_19, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|r1_tarski(X3,k3_tarski(k6_funct_2(X1,X2,X4,k7_funct_2(X1,X2,X4,X5))))|~v1_funct_2(X4,X1,X2)|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(X1)))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_setfam_1(X5,X3)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.20/0.57  cnf(c_0_20, plain, (m1_subset_1(k3_tarski(X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.20/0.57  fof(c_0_21, negated_conjecture, (~v1_xboole_0(esk1_0)&(~v1_xboole_0(esk2_0)&(((v1_funct_1(esk3_0)&v1_funct_2(esk3_0,esk1_0,esk2_0))&m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))))&(m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk1_0)))&~r1_tarski(k5_setfam_1(esk1_0,esk4_0),k5_setfam_1(esk1_0,k6_funct_2(esk1_0,esk2_0,esk3_0,k7_funct_2(esk1_0,esk2_0,esk3_0,esk4_0)))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_18])])])])).
% 0.20/0.57  fof(c_0_22, plain, ![X15, X16]:((~m1_setfam_1(X16,X15)|k5_setfam_1(X15,X16)=X15|~m1_subset_1(X16,k1_zfmisc_1(k1_zfmisc_1(X15))))&(k5_setfam_1(X15,X16)!=X15|m1_setfam_1(X16,X15)|~m1_subset_1(X16,k1_zfmisc_1(k1_zfmisc_1(X15))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_setfam_1])])])).
% 0.20/0.57  cnf(c_0_23, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|r1_tarski(k3_tarski(X3),k3_tarski(k6_funct_2(X2,X1,X4,k7_funct_2(X2,X1,X4,X5))))|~v1_funct_2(X4,X2,X1)|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))|~m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(X2)))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))|~m1_setfam_1(X5,k3_tarski(X3))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.20/0.57  cnf(c_0_24, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.57  cnf(c_0_25, negated_conjecture, (~v1_xboole_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.57  cnf(c_0_26, plain, (m1_setfam_1(X2,X1)|k5_setfam_1(X1,X2)!=X1|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.57  cnf(c_0_27, negated_conjecture, (~r1_tarski(k5_setfam_1(esk1_0,esk4_0),k5_setfam_1(esk1_0,k6_funct_2(esk1_0,esk2_0,esk3_0,k7_funct_2(esk1_0,esk2_0,esk3_0,esk4_0))))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.57  cnf(c_0_28, negated_conjecture, (v1_xboole_0(X1)|r1_tarski(k3_tarski(esk4_0),k3_tarski(k6_funct_2(esk1_0,X1,X2,k7_funct_2(esk1_0,X1,X2,X3))))|~v1_funct_2(X2,esk1_0,X1)|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(esk1_0,X1)))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(esk1_0)))|~m1_setfam_1(X3,k3_tarski(esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25])).
% 0.20/0.57  cnf(c_0_29, plain, (m1_setfam_1(X1,X2)|k3_tarski(X1)!=X2|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(spm,[status(thm)],[c_0_26, c_0_17])).
% 0.20/0.57  fof(c_0_30, plain, ![X13, X14]:((~m1_subset_1(X13,k1_zfmisc_1(X14))|r1_tarski(X13,X14))&(~r1_tarski(X13,X14)|m1_subset_1(X13,k1_zfmisc_1(X14)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.57  cnf(c_0_31, negated_conjecture, (~r1_tarski(k3_tarski(esk4_0),k5_setfam_1(esk1_0,k6_funct_2(esk1_0,esk2_0,esk3_0,k7_funct_2(esk1_0,esk2_0,esk3_0,esk4_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_17]), c_0_24])])).
% 0.20/0.57  fof(c_0_32, plain, ![X17, X18, X19, X20]:(v1_xboole_0(X17)|v1_xboole_0(X18)|~v1_funct_1(X19)|~v1_funct_2(X19,X17,X18)|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))|~m1_subset_1(X20,k1_zfmisc_1(k1_zfmisc_1(X18)))|m1_subset_1(k6_funct_2(X17,X18,X19,X20),k1_zfmisc_1(k1_zfmisc_1(X17)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_funct_2])])])).
% 0.20/0.57  cnf(c_0_33, negated_conjecture, (v1_xboole_0(X1)|r1_tarski(k3_tarski(esk4_0),k3_tarski(k6_funct_2(esk1_0,X1,X2,k7_funct_2(esk1_0,X1,X2,X3))))|k3_tarski(X3)!=k3_tarski(esk4_0)|~v1_funct_2(X2,esk1_0,X1)|~v1_funct_1(X2)|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(k3_tarski(esk4_0))))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(esk1_0,X1)))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(esk1_0)))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.20/0.57  cnf(c_0_34, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.57  fof(c_0_35, plain, ![X6]:r1_tarski(X6,k1_zfmisc_1(k3_tarski(X6))), inference(variable_rename,[status(thm)],[t100_zfmisc_1])).
% 0.20/0.57  cnf(c_0_36, negated_conjecture, (~m1_subset_1(k6_funct_2(esk1_0,esk2_0,esk3_0,k7_funct_2(esk1_0,esk2_0,esk3_0,esk4_0)),k1_zfmisc_1(k1_zfmisc_1(esk1_0)))|~r1_tarski(k3_tarski(esk4_0),k3_tarski(k6_funct_2(esk1_0,esk2_0,esk3_0,k7_funct_2(esk1_0,esk2_0,esk3_0,esk4_0))))), inference(spm,[status(thm)],[c_0_31, c_0_17])).
% 0.20/0.57  cnf(c_0_37, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|m1_subset_1(k6_funct_2(X1,X2,X3,X4),k1_zfmisc_1(k1_zfmisc_1(X1)))|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.57  cnf(c_0_38, negated_conjecture, (v1_funct_2(esk3_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.57  cnf(c_0_39, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.57  cnf(c_0_40, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.57  cnf(c_0_41, negated_conjecture, (~v1_xboole_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.57  cnf(c_0_42, negated_conjecture, (v1_xboole_0(X1)|r1_tarski(k3_tarski(esk4_0),k3_tarski(k6_funct_2(esk1_0,X1,X2,k7_funct_2(esk1_0,X1,X2,X3))))|k3_tarski(X3)!=k3_tarski(esk4_0)|~v1_funct_2(X2,esk1_0,X1)|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(esk1_0,X1)))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(esk1_0)))|~r1_tarski(X3,k1_zfmisc_1(k3_tarski(esk4_0)))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.20/0.57  cnf(c_0_43, plain, (r1_tarski(X1,k1_zfmisc_1(k3_tarski(X1)))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.57  cnf(c_0_44, negated_conjecture, (~m1_subset_1(k7_funct_2(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k1_zfmisc_1(esk2_0)))|~r1_tarski(k3_tarski(esk4_0),k3_tarski(k6_funct_2(esk1_0,esk2_0,esk3_0,k7_funct_2(esk1_0,esk2_0,esk3_0,esk4_0))))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38]), c_0_39]), c_0_40])]), c_0_41]), c_0_25])).
% 0.20/0.57  cnf(c_0_45, negated_conjecture, (v1_xboole_0(X1)|r1_tarski(k3_tarski(esk4_0),k3_tarski(k6_funct_2(esk1_0,X1,X2,k7_funct_2(esk1_0,X1,X2,esk4_0))))|~v1_funct_2(X2,esk1_0,X1)|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(esk1_0,X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_24])])).
% 0.20/0.57  fof(c_0_46, plain, ![X21, X22, X23, X24]:(v1_xboole_0(X21)|v1_xboole_0(X22)|~v1_funct_1(X23)|~v1_funct_2(X23,X21,X22)|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))|~m1_subset_1(X24,k1_zfmisc_1(k1_zfmisc_1(X21)))|m1_subset_1(k7_funct_2(X21,X22,X23,X24),k1_zfmisc_1(k1_zfmisc_1(X22)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_funct_2])])])).
% 0.20/0.57  cnf(c_0_47, negated_conjecture, (~m1_subset_1(k7_funct_2(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k1_zfmisc_1(esk2_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_38]), c_0_39]), c_0_40])]), c_0_41])).
% 0.20/0.57  cnf(c_0_48, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|m1_subset_1(k7_funct_2(X1,X2,X3,X4),k1_zfmisc_1(k1_zfmisc_1(X2)))|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.20/0.57  cnf(c_0_49, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_38]), c_0_39]), c_0_40]), c_0_24])]), c_0_41]), c_0_25]), ['proof']).
% 0.20/0.57  # SZS output end CNFRefutation
% 0.20/0.57  # Proof object total steps             : 50
% 0.20/0.57  # Proof object clause steps            : 29
% 0.20/0.57  # Proof object formula steps           : 21
% 0.20/0.57  # Proof object conjectures             : 19
% 0.20/0.57  # Proof object clause conjectures      : 16
% 0.20/0.57  # Proof object formula conjectures     : 3
% 0.20/0.57  # Proof object initial clauses used    : 16
% 0.20/0.57  # Proof object initial formulas used   : 10
% 0.20/0.57  # Proof object generating inferences   : 13
% 0.20/0.57  # Proof object simplifying inferences  : 23
% 0.20/0.57  # Training examples: 0 positive, 0 negative
% 0.20/0.57  # Parsed axioms                        : 10
% 0.20/0.57  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.57  # Initial clauses                      : 19
% 0.20/0.57  # Removed in clause preprocessing      : 0
% 0.20/0.57  # Initial clauses in saturation        : 19
% 0.20/0.57  # Processed clauses                    : 1024
% 0.20/0.57  # ...of these trivial                  : 0
% 0.20/0.57  # ...subsumed                          : 337
% 0.20/0.57  # ...remaining for further processing  : 687
% 0.20/0.57  # Other redundant clauses eliminated   : 0
% 0.20/0.57  # Clauses deleted for lack of memory   : 0
% 0.20/0.57  # Backward-subsumed                    : 9
% 0.20/0.57  # Backward-rewritten                   : 0
% 0.20/0.57  # Generated clauses                    : 4766
% 0.20/0.57  # ...of the previous two non-trivial   : 4305
% 0.20/0.57  # Contextual simplify-reflections      : 2
% 0.20/0.57  # Paramodulations                      : 4766
% 0.20/0.57  # Factorizations                       : 0
% 0.20/0.57  # Equation resolutions                 : 0
% 0.20/0.57  # Propositional unsat checks           : 0
% 0.20/0.57  #    Propositional check models        : 0
% 0.20/0.57  #    Propositional check unsatisfiable : 0
% 0.20/0.57  #    Propositional clauses             : 0
% 0.20/0.57  #    Propositional clauses after purity: 0
% 0.20/0.57  #    Propositional unsat core size     : 0
% 0.20/0.57  #    Propositional preprocessing time  : 0.000
% 0.20/0.57  #    Propositional encoding time       : 0.000
% 0.20/0.57  #    Propositional solver time         : 0.000
% 0.20/0.57  #    Success case prop preproc time    : 0.000
% 0.20/0.57  #    Success case prop encoding time   : 0.000
% 0.20/0.57  #    Success case prop solver time     : 0.000
% 0.20/0.57  # Current number of processed clauses  : 659
% 0.20/0.57  #    Positive orientable unit clauses  : 10
% 0.20/0.57  #    Positive unorientable unit clauses: 0
% 0.20/0.57  #    Negative unit clauses             : 8
% 0.20/0.57  #    Non-unit-clauses                  : 641
% 0.20/0.57  # Current number of unprocessed clauses: 3316
% 0.20/0.57  # ...number of literals in the above   : 21170
% 0.20/0.57  # Current number of archived formulas  : 0
% 0.20/0.57  # Current number of archived clauses   : 28
% 0.20/0.57  # Clause-clause subsumption calls (NU) : 151001
% 0.20/0.57  # Rec. Clause-clause subsumption calls : 46308
% 0.20/0.57  # Non-unit clause-clause subsumptions  : 345
% 0.20/0.57  # Unit Clause-clause subsumption calls : 71
% 0.20/0.57  # Rewrite failures with RHS unbound    : 0
% 0.20/0.57  # BW rewrite match attempts            : 1
% 0.20/0.57  # BW rewrite match successes           : 0
% 0.20/0.57  # Condensation attempts                : 0
% 0.20/0.57  # Condensation successes               : 0
% 0.20/0.57  # Termbank termtop insertions          : 184276
% 0.20/0.57  
% 0.20/0.57  # -------------------------------------------------
% 0.20/0.57  # User time                : 0.225 s
% 0.20/0.57  # System time              : 0.009 s
% 0.20/0.57  # Total time               : 0.234 s
% 0.20/0.57  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
