%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:07:44 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 128 expanded)
%              Number of clauses        :   30 (  44 expanded)
%              Number of leaves         :   10 (  32 expanded)
%              Depth                    :    9
%              Number of atoms          :  178 ( 608 expanded)
%              Number of equality atoms :   11 (  14 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :    9 (   3 average)
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

fof(redefinition_k5_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => k5_setfam_1(X1,X2) = k3_tarski(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

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

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t95_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k3_tarski(X1),k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_zfmisc_1)).

fof(t99_zfmisc_1,axiom,(
    ! [X1] : k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

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

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

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

fof(c_0_10,negated_conjecture,(
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

fof(c_0_11,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0)
    & ~ v1_xboole_0(esk2_0)
    & v1_funct_1(esk3_0)
    & v1_funct_2(esk3_0,esk1_0,esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    & m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk1_0)))
    & ~ r1_tarski(k5_setfam_1(esk1_0,esk4_0),k5_setfam_1(esk1_0,k6_funct_2(esk1_0,esk2_0,esk3_0,k7_funct_2(esk1_0,esk2_0,esk3_0,esk4_0)))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).

fof(c_0_12,plain,(
    ! [X13,X14] :
      ( ~ m1_subset_1(X14,k1_zfmisc_1(k1_zfmisc_1(X13)))
      | k5_setfam_1(X13,X14) = k3_tarski(X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k5_setfam_1])])).

fof(c_0_13,plain,(
    ! [X11,X12] :
      ( ( ~ m1_setfam_1(X12,X11)
        | r1_tarski(X11,k3_tarski(X12)) )
      & ( ~ r1_tarski(X11,k3_tarski(X12))
        | m1_setfam_1(X12,X11) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_setfam_1])])).

fof(c_0_14,plain,(
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

cnf(c_0_15,negated_conjecture,
    ( ~ r1_tarski(k5_setfam_1(esk1_0,esk4_0),k5_setfam_1(esk1_0,k6_funct_2(esk1_0,esk2_0,esk3_0,k7_funct_2(esk1_0,esk2_0,esk3_0,esk4_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( k5_setfam_1(X2,X1) = k3_tarski(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( r1_tarski(X2,k3_tarski(X1))
    | ~ m1_setfam_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
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

fof(c_0_20,plain,(
    ! [X6,X7] :
      ( ( r1_tarski(X6,X7)
        | X6 != X7 )
      & ( r1_tarski(X7,X6)
        | X6 != X7 )
      & ( ~ r1_tarski(X6,X7)
        | ~ r1_tarski(X7,X6)
        | X6 = X7 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_21,negated_conjecture,
    ( ~ r1_tarski(k3_tarski(esk4_0),k5_setfam_1(esk1_0,k6_funct_2(esk1_0,esk2_0,esk3_0,k7_funct_2(esk1_0,esk2_0,esk3_0,esk4_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])])).

cnf(c_0_22,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | r1_tarski(X3,k3_tarski(k6_funct_2(X1,X2,X4,k7_funct_2(X1,X2,X4,X5))))
    | ~ v1_funct_2(X4,X1,X2)
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_setfam_1(X5,X3) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_23,plain,
    ( m1_setfam_1(X2,X1)
    | ~ r1_tarski(X1,k3_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_25,plain,(
    ! [X8,X9] :
      ( ~ r1_tarski(X8,X9)
      | r1_tarski(k3_tarski(X8),k3_tarski(X9)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t95_zfmisc_1])])).

fof(c_0_26,plain,(
    ! [X10] : k3_tarski(k1_zfmisc_1(X10)) = X10 ),
    inference(variable_rename,[status(thm)],[t99_zfmisc_1])).

cnf(c_0_27,negated_conjecture,
    ( ~ m1_subset_1(k6_funct_2(esk1_0,esk2_0,esk3_0,k7_funct_2(esk1_0,esk2_0,esk3_0,esk4_0)),k1_zfmisc_1(k1_zfmisc_1(esk1_0)))
    | ~ r1_tarski(k3_tarski(esk4_0),k3_tarski(k6_funct_2(esk1_0,esk2_0,esk3_0,k7_funct_2(esk1_0,esk2_0,esk3_0,esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_21,c_0_16])).

cnf(c_0_28,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | r1_tarski(X3,k3_tarski(k6_funct_2(X2,X1,X4,k7_funct_2(X2,X1,X4,X5))))
    | ~ v1_funct_2(X4,X2,X1)
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_tarski(X3,k3_tarski(X5)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( v1_funct_2(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_30,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_24])).

cnf(c_0_33,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_34,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_35,plain,(
    ! [X17,X18,X19,X20] :
      ( v1_xboole_0(X17)
      | v1_xboole_0(X18)
      | ~ v1_funct_1(X19)
      | ~ v1_funct_2(X19,X17,X18)
      | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))
      | ~ m1_subset_1(X20,k1_zfmisc_1(k1_zfmisc_1(X18)))
      | m1_subset_1(k6_funct_2(X17,X18,X19,X20),k1_zfmisc_1(k1_zfmisc_1(X17))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_funct_2])])])).

fof(c_0_36,plain,(
    ! [X15,X16] :
      ( ( ~ m1_subset_1(X15,k1_zfmisc_1(X16))
        | r1_tarski(X15,X16) )
      & ( ~ r1_tarski(X15,X16)
        | m1_subset_1(X15,k1_zfmisc_1(X16)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_37,plain,
    ( r1_tarski(k3_tarski(X1),k3_tarski(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_38,plain,
    ( k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_39,negated_conjecture,
    ( ~ m1_subset_1(k6_funct_2(esk1_0,esk2_0,esk3_0,k7_funct_2(esk1_0,esk2_0,esk3_0,esk4_0)),k1_zfmisc_1(k1_zfmisc_1(esk1_0)))
    | ~ m1_subset_1(k3_tarski(esk4_0),k1_zfmisc_1(esk1_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29]),c_0_30]),c_0_31]),c_0_17]),c_0_32])]),c_0_33]),c_0_34])).

cnf(c_0_40,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | m1_subset_1(k6_funct_2(X1,X2,X3,X4),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_41,plain,(
    ! [X21,X22,X23,X24] :
      ( v1_xboole_0(X21)
      | v1_xboole_0(X22)
      | ~ v1_funct_1(X23)
      | ~ v1_funct_2(X23,X21,X22)
      | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))
      | ~ m1_subset_1(X24,k1_zfmisc_1(k1_zfmisc_1(X21)))
      | m1_subset_1(k7_funct_2(X21,X22,X23,X24),k1_zfmisc_1(k1_zfmisc_1(X22))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_funct_2])])])).

cnf(c_0_42,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_43,plain,
    ( r1_tarski(k3_tarski(X1),X2)
    | ~ r1_tarski(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_44,negated_conjecture,
    ( ~ m1_subset_1(k7_funct_2(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k1_zfmisc_1(esk2_0)))
    | ~ m1_subset_1(k3_tarski(esk4_0),k1_zfmisc_1(esk1_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_29]),c_0_30]),c_0_31])]),c_0_33]),c_0_34])).

cnf(c_0_45,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | m1_subset_1(k7_funct_2(X1,X2,X3,X4),k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_46,plain,
    ( m1_subset_1(k3_tarski(X1),k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_47,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_48,negated_conjecture,
    ( ~ m1_subset_1(k3_tarski(esk4_0),k1_zfmisc_1(esk1_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_29]),c_0_30]),c_0_31]),c_0_17])]),c_0_33]),c_0_34])).

cnf(c_0_49,plain,
    ( m1_subset_1(k3_tarski(X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_50,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_17])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:10:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.43  # AutoSched0-Mode selected heuristic G_E___208_B02_F1_AE_CS_SP_PS_S0Y
% 0.20/0.43  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.43  #
% 0.20/0.43  # Preprocessing time       : 0.027 s
% 0.20/0.43  # Presaturation interreduction done
% 0.20/0.43  
% 0.20/0.43  # Proof found!
% 0.20/0.43  # SZS status Theorem
% 0.20/0.43  # SZS output start CNFRefutation
% 0.20/0.43  fof(t184_funct_2, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1)))=>r1_tarski(k5_setfam_1(X1,X4),k5_setfam_1(X1,k6_funct_2(X1,X2,X3,k7_funct_2(X1,X2,X3,X4)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t184_funct_2)).
% 0.20/0.43  fof(redefinition_k5_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>k5_setfam_1(X1,X2)=k3_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_setfam_1)).
% 0.20/0.43  fof(d12_setfam_1, axiom, ![X1, X2]:(m1_setfam_1(X2,X1)<=>r1_tarski(X1,k3_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_setfam_1)).
% 0.20/0.43  fof(t182_funct_2, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1)))=>![X5]:(m1_subset_1(X5,k1_zfmisc_1(X1))=>(m1_setfam_1(X4,X5)=>m1_setfam_1(k6_funct_2(X1,X2,X3,k7_funct_2(X1,X2,X3,X4)),X5))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_funct_2)).
% 0.20/0.43  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.43  fof(t95_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>r1_tarski(k3_tarski(X1),k3_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_zfmisc_1)).
% 0.20/0.43  fof(t99_zfmisc_1, axiom, ![X1]:k3_tarski(k1_zfmisc_1(X1))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 0.20/0.43  fof(dt_k6_funct_2, axiom, ![X1, X2, X3, X4]:((((((~(v1_xboole_0(X1))&~(v1_xboole_0(X2)))&v1_funct_1(X3))&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X2))))=>m1_subset_1(k6_funct_2(X1,X2,X3,X4),k1_zfmisc_1(k1_zfmisc_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_funct_2)).
% 0.20/0.43  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.43  fof(dt_k7_funct_2, axiom, ![X1, X2, X3, X4]:((((((~(v1_xboole_0(X1))&~(v1_xboole_0(X2)))&v1_funct_1(X3))&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1))))=>m1_subset_1(k7_funct_2(X1,X2,X3,X4),k1_zfmisc_1(k1_zfmisc_1(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_funct_2)).
% 0.20/0.43  fof(c_0_10, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1)))=>r1_tarski(k5_setfam_1(X1,X4),k5_setfam_1(X1,k6_funct_2(X1,X2,X3,k7_funct_2(X1,X2,X3,X4))))))))), inference(assume_negation,[status(cth)],[t184_funct_2])).
% 0.20/0.43  fof(c_0_11, negated_conjecture, (~v1_xboole_0(esk1_0)&(~v1_xboole_0(esk2_0)&(((v1_funct_1(esk3_0)&v1_funct_2(esk3_0,esk1_0,esk2_0))&m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))))&(m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk1_0)))&~r1_tarski(k5_setfam_1(esk1_0,esk4_0),k5_setfam_1(esk1_0,k6_funct_2(esk1_0,esk2_0,esk3_0,k7_funct_2(esk1_0,esk2_0,esk3_0,esk4_0)))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).
% 0.20/0.43  fof(c_0_12, plain, ![X13, X14]:(~m1_subset_1(X14,k1_zfmisc_1(k1_zfmisc_1(X13)))|k5_setfam_1(X13,X14)=k3_tarski(X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k5_setfam_1])])).
% 0.20/0.43  fof(c_0_13, plain, ![X11, X12]:((~m1_setfam_1(X12,X11)|r1_tarski(X11,k3_tarski(X12)))&(~r1_tarski(X11,k3_tarski(X12))|m1_setfam_1(X12,X11))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_setfam_1])])).
% 0.20/0.43  fof(c_0_14, plain, ![X25, X26, X27, X28, X29]:(v1_xboole_0(X25)|(v1_xboole_0(X26)|(~v1_funct_1(X27)|~v1_funct_2(X27,X25,X26)|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))|(~m1_subset_1(X28,k1_zfmisc_1(k1_zfmisc_1(X25)))|(~m1_subset_1(X29,k1_zfmisc_1(X25))|(~m1_setfam_1(X28,X29)|m1_setfam_1(k6_funct_2(X25,X26,X27,k7_funct_2(X25,X26,X27,X28)),X29))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t182_funct_2])])])])).
% 0.20/0.43  cnf(c_0_15, negated_conjecture, (~r1_tarski(k5_setfam_1(esk1_0,esk4_0),k5_setfam_1(esk1_0,k6_funct_2(esk1_0,esk2_0,esk3_0,k7_funct_2(esk1_0,esk2_0,esk3_0,esk4_0))))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.43  cnf(c_0_16, plain, (k5_setfam_1(X2,X1)=k3_tarski(X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.43  cnf(c_0_17, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.43  cnf(c_0_18, plain, (r1_tarski(X2,k3_tarski(X1))|~m1_setfam_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.43  cnf(c_0_19, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|m1_setfam_1(k6_funct_2(X1,X2,X3,k7_funct_2(X1,X2,X3,X4)),X5)|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1)))|~m1_subset_1(X5,k1_zfmisc_1(X1))|~m1_setfam_1(X4,X5)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.43  fof(c_0_20, plain, ![X6, X7]:(((r1_tarski(X6,X7)|X6!=X7)&(r1_tarski(X7,X6)|X6!=X7))&(~r1_tarski(X6,X7)|~r1_tarski(X7,X6)|X6=X7)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.43  cnf(c_0_21, negated_conjecture, (~r1_tarski(k3_tarski(esk4_0),k5_setfam_1(esk1_0,k6_funct_2(esk1_0,esk2_0,esk3_0,k7_funct_2(esk1_0,esk2_0,esk3_0,esk4_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17])])).
% 0.20/0.43  cnf(c_0_22, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|r1_tarski(X3,k3_tarski(k6_funct_2(X1,X2,X4,k7_funct_2(X1,X2,X4,X5))))|~v1_funct_2(X4,X1,X2)|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(X1)))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_setfam_1(X5,X3)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.20/0.43  cnf(c_0_23, plain, (m1_setfam_1(X2,X1)|~r1_tarski(X1,k3_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.43  cnf(c_0_24, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.43  fof(c_0_25, plain, ![X8, X9]:(~r1_tarski(X8,X9)|r1_tarski(k3_tarski(X8),k3_tarski(X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t95_zfmisc_1])])).
% 0.20/0.43  fof(c_0_26, plain, ![X10]:k3_tarski(k1_zfmisc_1(X10))=X10, inference(variable_rename,[status(thm)],[t99_zfmisc_1])).
% 0.20/0.43  cnf(c_0_27, negated_conjecture, (~m1_subset_1(k6_funct_2(esk1_0,esk2_0,esk3_0,k7_funct_2(esk1_0,esk2_0,esk3_0,esk4_0)),k1_zfmisc_1(k1_zfmisc_1(esk1_0)))|~r1_tarski(k3_tarski(esk4_0),k3_tarski(k6_funct_2(esk1_0,esk2_0,esk3_0,k7_funct_2(esk1_0,esk2_0,esk3_0,esk4_0))))), inference(spm,[status(thm)],[c_0_21, c_0_16])).
% 0.20/0.43  cnf(c_0_28, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|r1_tarski(X3,k3_tarski(k6_funct_2(X2,X1,X4,k7_funct_2(X2,X1,X4,X5))))|~v1_funct_2(X4,X2,X1)|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))|~m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(X2)))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_tarski(X3,k3_tarski(X5))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.20/0.43  cnf(c_0_29, negated_conjecture, (v1_funct_2(esk3_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.43  cnf(c_0_30, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.43  cnf(c_0_31, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.43  cnf(c_0_32, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_24])).
% 0.20/0.43  cnf(c_0_33, negated_conjecture, (~v1_xboole_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.43  cnf(c_0_34, negated_conjecture, (~v1_xboole_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.43  fof(c_0_35, plain, ![X17, X18, X19, X20]:(v1_xboole_0(X17)|v1_xboole_0(X18)|~v1_funct_1(X19)|~v1_funct_2(X19,X17,X18)|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))|~m1_subset_1(X20,k1_zfmisc_1(k1_zfmisc_1(X18)))|m1_subset_1(k6_funct_2(X17,X18,X19,X20),k1_zfmisc_1(k1_zfmisc_1(X17)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_funct_2])])])).
% 0.20/0.43  fof(c_0_36, plain, ![X15, X16]:((~m1_subset_1(X15,k1_zfmisc_1(X16))|r1_tarski(X15,X16))&(~r1_tarski(X15,X16)|m1_subset_1(X15,k1_zfmisc_1(X16)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.43  cnf(c_0_37, plain, (r1_tarski(k3_tarski(X1),k3_tarski(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.43  cnf(c_0_38, plain, (k3_tarski(k1_zfmisc_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.43  cnf(c_0_39, negated_conjecture, (~m1_subset_1(k6_funct_2(esk1_0,esk2_0,esk3_0,k7_funct_2(esk1_0,esk2_0,esk3_0,esk4_0)),k1_zfmisc_1(k1_zfmisc_1(esk1_0)))|~m1_subset_1(k3_tarski(esk4_0),k1_zfmisc_1(esk1_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29]), c_0_30]), c_0_31]), c_0_17]), c_0_32])]), c_0_33]), c_0_34])).
% 0.20/0.43  cnf(c_0_40, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|m1_subset_1(k6_funct_2(X1,X2,X3,X4),k1_zfmisc_1(k1_zfmisc_1(X1)))|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.43  fof(c_0_41, plain, ![X21, X22, X23, X24]:(v1_xboole_0(X21)|v1_xboole_0(X22)|~v1_funct_1(X23)|~v1_funct_2(X23,X21,X22)|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))|~m1_subset_1(X24,k1_zfmisc_1(k1_zfmisc_1(X21)))|m1_subset_1(k7_funct_2(X21,X22,X23,X24),k1_zfmisc_1(k1_zfmisc_1(X22)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_funct_2])])])).
% 0.20/0.43  cnf(c_0_42, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.43  cnf(c_0_43, plain, (r1_tarski(k3_tarski(X1),X2)|~r1_tarski(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.20/0.43  cnf(c_0_44, negated_conjecture, (~m1_subset_1(k7_funct_2(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k1_zfmisc_1(esk2_0)))|~m1_subset_1(k3_tarski(esk4_0),k1_zfmisc_1(esk1_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_29]), c_0_30]), c_0_31])]), c_0_33]), c_0_34])).
% 0.20/0.43  cnf(c_0_45, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|m1_subset_1(k7_funct_2(X1,X2,X3,X4),k1_zfmisc_1(k1_zfmisc_1(X2)))|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.20/0.43  cnf(c_0_46, plain, (m1_subset_1(k3_tarski(X1),k1_zfmisc_1(X2))|~r1_tarski(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.20/0.43  cnf(c_0_47, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.43  cnf(c_0_48, negated_conjecture, (~m1_subset_1(k3_tarski(esk4_0),k1_zfmisc_1(esk1_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_29]), c_0_30]), c_0_31]), c_0_17])]), c_0_33]), c_0_34])).
% 0.20/0.43  cnf(c_0_49, plain, (m1_subset_1(k3_tarski(X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.20/0.43  cnf(c_0_50, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_17])]), ['proof']).
% 0.20/0.43  # SZS output end CNFRefutation
% 0.20/0.43  # Proof object total steps             : 51
% 0.20/0.43  # Proof object clause steps            : 30
% 0.20/0.43  # Proof object formula steps           : 21
% 0.20/0.43  # Proof object conjectures             : 16
% 0.20/0.43  # Proof object clause conjectures      : 13
% 0.20/0.43  # Proof object formula conjectures     : 3
% 0.20/0.43  # Proof object initial clauses used    : 18
% 0.20/0.43  # Proof object initial formulas used   : 10
% 0.20/0.43  # Proof object generating inferences   : 11
% 0.20/0.43  # Proof object simplifying inferences  : 26
% 0.20/0.43  # Training examples: 0 positive, 0 negative
% 0.20/0.43  # Parsed axioms                        : 10
% 0.20/0.43  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.43  # Initial clauses                      : 20
% 0.20/0.43  # Removed in clause preprocessing      : 0
% 0.20/0.43  # Initial clauses in saturation        : 20
% 0.20/0.43  # Processed clauses                    : 494
% 0.20/0.43  # ...of these trivial                  : 0
% 0.20/0.43  # ...subsumed                          : 136
% 0.20/0.43  # ...remaining for further processing  : 358
% 0.20/0.43  # Other redundant clauses eliminated   : 2
% 0.20/0.43  # Clauses deleted for lack of memory   : 0
% 0.20/0.43  # Backward-subsumed                    : 0
% 0.20/0.43  # Backward-rewritten                   : 0
% 0.20/0.43  # Generated clauses                    : 1537
% 0.20/0.43  # ...of the previous two non-trivial   : 1484
% 0.20/0.43  # Contextual simplify-reflections      : 0
% 0.20/0.43  # Paramodulations                      : 1535
% 0.20/0.43  # Factorizations                       : 0
% 0.20/0.43  # Equation resolutions                 : 2
% 0.20/0.43  # Propositional unsat checks           : 0
% 0.20/0.43  #    Propositional check models        : 0
% 0.20/0.43  #    Propositional check unsatisfiable : 0
% 0.20/0.43  #    Propositional clauses             : 0
% 0.20/0.43  #    Propositional clauses after purity: 0
% 0.20/0.43  #    Propositional unsat core size     : 0
% 0.20/0.43  #    Propositional preprocessing time  : 0.000
% 0.20/0.43  #    Propositional encoding time       : 0.000
% 0.20/0.43  #    Propositional solver time         : 0.000
% 0.20/0.43  #    Success case prop preproc time    : 0.000
% 0.20/0.43  #    Success case prop encoding time   : 0.000
% 0.20/0.43  #    Success case prop solver time     : 0.000
% 0.20/0.43  # Current number of processed clauses  : 337
% 0.20/0.43  #    Positive orientable unit clauses  : 7
% 0.20/0.43  #    Positive unorientable unit clauses: 0
% 0.20/0.43  #    Negative unit clauses             : 48
% 0.20/0.43  #    Non-unit-clauses                  : 282
% 0.20/0.43  # Current number of unprocessed clauses: 1029
% 0.20/0.43  # ...number of literals in the above   : 3235
% 0.20/0.43  # Current number of archived formulas  : 0
% 0.20/0.43  # Current number of archived clauses   : 19
% 0.20/0.43  # Clause-clause subsumption calls (NU) : 10376
% 0.20/0.43  # Rec. Clause-clause subsumption calls : 9171
% 0.20/0.43  # Non-unit clause-clause subsumptions  : 121
% 0.20/0.43  # Unit Clause-clause subsumption calls : 185
% 0.20/0.43  # Rewrite failures with RHS unbound    : 0
% 0.20/0.43  # BW rewrite match attempts            : 6
% 0.20/0.43  # BW rewrite match successes           : 0
% 0.20/0.43  # Condensation attempts                : 0
% 0.20/0.43  # Condensation successes               : 0
% 0.20/0.43  # Termbank termtop insertions          : 40229
% 0.20/0.43  
% 0.20/0.43  # -------------------------------------------------
% 0.20/0.43  # User time                : 0.076 s
% 0.20/0.43  # System time              : 0.007 s
% 0.20/0.43  # Total time               : 0.083 s
% 0.20/0.43  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
