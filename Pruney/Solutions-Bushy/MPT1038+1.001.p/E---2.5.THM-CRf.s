%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1038+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:37 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 317 expanded)
%              Number of clauses        :   36 ( 112 expanded)
%              Number of leaves         :    7 (  74 expanded)
%              Depth                    :   11
%              Number of atoms          :  180 (2178 expanded)
%              Number of equality atoms :    9 (  12 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t152_funct_2,conjecture,(
    ! [X1,X2] :
      ( ( v1_funct_1(X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => ! [X3] :
          ( ( v1_funct_1(X3)
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
         => ! [X4] :
              ( ( v1_funct_1(X4)
                & v1_funct_2(X4,X1,X1)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
             => ( ( r1_partfun1(X2,X4)
                  & r1_partfun1(X3,X4) )
               => r1_partfun1(X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_2)).

fof(t158_partfun1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
         => ! [X5] :
              ( ( v1_funct_1(X5)
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
             => ( ( r1_partfun1(X3,X5)
                  & r1_partfun1(X4,X5)
                  & v1_partfun1(X5,X1) )
               => r1_partfun1(X3,X4) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_partfun1)).

fof(cc5_funct_2,axiom,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
         => ( ( v1_funct_1(X3)
              & v1_funct_2(X3,X1,X2) )
           => ( v1_funct_1(X3)
              & v1_partfun1(X3,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

fof(cc4_relset_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
         => v1_xboole_0(X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

fof(t8_boole,axiom,(
    ! [X1,X2] :
      ~ ( v1_xboole_0(X1)
        & X1 != X2
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(reflexivity_r1_partfun1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X2)
        & v1_funct_1(X2) )
     => r1_partfun1(X1,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r1_partfun1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_funct_1(X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
       => ! [X3] :
            ( ( v1_funct_1(X3)
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
           => ! [X4] :
                ( ( v1_funct_1(X4)
                  & v1_funct_2(X4,X1,X1)
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
               => ( ( r1_partfun1(X2,X4)
                    & r1_partfun1(X3,X4) )
                 => r1_partfun1(X2,X3) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t152_funct_2])).

fof(c_0_8,plain,(
    ! [X17,X18,X19,X20,X21] :
      ( ~ v1_funct_1(X19)
      | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))
      | ~ v1_funct_1(X20)
      | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))
      | ~ v1_funct_1(X21)
      | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))
      | ~ r1_partfun1(X19,X21)
      | ~ r1_partfun1(X20,X21)
      | ~ v1_partfun1(X21,X17)
      | r1_partfun1(X19,X20) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t158_partfun1])])])).

fof(c_0_9,negated_conjecture,
    ( v1_funct_1(esk2_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))
    & v1_funct_1(esk3_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))
    & v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,esk1_0,esk1_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))
    & r1_partfun1(esk2_0,esk4_0)
    & r1_partfun1(esk3_0,esk4_0)
    & ~ r1_partfun1(esk2_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_10,plain,(
    ! [X12,X13,X14] :
      ( ( v1_funct_1(X14)
        | ~ v1_funct_1(X14)
        | ~ v1_funct_2(X14,X12,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X12,X13)))
        | v1_xboole_0(X13) )
      & ( v1_partfun1(X14,X12)
        | ~ v1_funct_1(X14)
        | ~ v1_funct_2(X14,X12,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X12,X13)))
        | v1_xboole_0(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).

cnf(c_0_11,plain,
    ( r1_partfun1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r1_partfun1(X1,X5)
    | ~ r1_partfun1(X4,X5)
    | ~ v1_partfun1(X5,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( v1_partfun1(X1,X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( v1_funct_2(esk4_0,esk1_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_16,plain,(
    ! [X9,X10,X11] :
      ( ~ v1_xboole_0(X9)
      | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X10,X9)))
      | v1_xboole_0(X11) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).

cnf(c_0_17,negated_conjecture,
    ( r1_partfun1(X1,X2)
    | ~ r1_partfun1(X2,esk4_0)
    | ~ r1_partfun1(X1,esk4_0)
    | ~ v1_partfun1(esk4_0,esk1_0)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13])])).

cnf(c_0_18,negated_conjecture,
    ( v1_partfun1(esk4_0,esk1_0)
    | v1_xboole_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_12]),c_0_15]),c_0_13])])).

fof(c_0_19,plain,(
    ! [X22,X23] :
      ( ~ v1_xboole_0(X22)
      | X22 = X23
      | ~ v1_xboole_0(X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).

cnf(c_0_20,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_22,negated_conjecture,
    ( r1_partfun1(X1,X2)
    | v1_xboole_0(esk1_0)
    | ~ r1_partfun1(X2,esk4_0)
    | ~ r1_partfun1(X1,esk4_0)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_24,negated_conjecture,
    ( r1_partfun1(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_25,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_26,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( v1_xboole_0(esk2_0)
    | ~ v1_xboole_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( r1_partfun1(X1,esk3_0)
    | v1_xboole_0(esk1_0)
    | ~ r1_partfun1(X1,esk4_0)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_25])])).

cnf(c_0_29,negated_conjecture,
    ( r1_partfun1(esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_30,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_31,negated_conjecture,
    ( ~ r1_partfun1(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_32,plain,(
    ! [X6,X7,X8] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | v1_relat_1(X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_33,negated_conjecture,
    ( X1 = esk2_0
    | ~ v1_xboole_0(esk1_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( v1_xboole_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_21]),c_0_29]),c_0_30])]),c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( v1_xboole_0(esk4_0)
    | ~ v1_xboole_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_12])).

cnf(c_0_36,negated_conjecture,
    ( v1_xboole_0(esk3_0)
    | ~ v1_xboole_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_23])).

fof(c_0_37,plain,(
    ! [X15,X16] :
      ( ~ v1_relat_1(X15)
      | ~ v1_funct_1(X15)
      | ~ v1_relat_1(X16)
      | ~ v1_funct_1(X16)
      | r1_partfun1(X15,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[reflexivity_r1_partfun1])])).

cnf(c_0_38,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_39,negated_conjecture,
    ( X1 = esk2_0
    | ~ v1_xboole_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_34])])).

cnf(c_0_40,negated_conjecture,
    ( v1_xboole_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_34])])).

cnf(c_0_41,negated_conjecture,
    ( X1 = esk3_0
    | ~ v1_xboole_0(esk1_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_36])).

cnf(c_0_42,plain,
    ( r1_partfun1(X1,X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_43,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_12])).

cnf(c_0_44,negated_conjecture,
    ( esk2_0 = esk4_0 ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_45,negated_conjecture,
    ( X1 = esk3_0
    | ~ v1_xboole_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_34])])).

cnf(c_0_46,negated_conjecture,
    ( r1_partfun1(X1,X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_13]),c_0_43])])).

cnf(c_0_47,negated_conjecture,
    ( ~ r1_partfun1(esk4_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_31,c_0_44])).

cnf(c_0_48,negated_conjecture,
    ( esk3_0 = esk4_0 ),
    inference(spm,[status(thm)],[c_0_45,c_0_40])).

cnf(c_0_49,negated_conjecture,
    ( r1_partfun1(esk4_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_13]),c_0_43])])).

cnf(c_0_50,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_48]),c_0_49])]),
    [proof]).

%------------------------------------------------------------------------------
