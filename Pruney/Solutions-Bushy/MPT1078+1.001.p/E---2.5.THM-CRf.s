%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1078+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:42 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 410 expanded)
%              Number of clauses        :   51 ( 144 expanded)
%              Number of leaves         :   11 ( 102 expanded)
%              Depth                    :   18
%              Number of atoms          :  313 (2643 expanded)
%              Number of equality atoms :   14 (  53 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t195_funct_2,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3,X4,X5,X6] :
              ( ( v1_funct_1(X6)
                & v1_funct_2(X6,X1,X2)
                & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
             => ! [X7] :
                  ( ( v1_funct_1(X7)
                    & m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
                 => ( ( r1_tarski(k2_relset_1(X1,X2,X6),k1_relset_1(X2,X3,k2_partfun1(X2,X3,X7,X4)))
                      & r1_tarski(X4,X5) )
                   => r2_funct_2(X1,X3,k8_funct_2(X1,X2,X3,X6,k2_partfun1(X2,X3,X7,X4)),k8_funct_2(X1,X2,X3,X6,k2_partfun1(X2,X3,X7,X5))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t195_funct_2)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(dt_k2_partfun1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( v1_funct_1(k2_partfun1(X1,X2,X3,X4))
        & m1_subset_1(k2_partfun1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(redefinition_k2_partfun1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => k2_partfun1(X1,X2,X3,X4) = k7_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t25_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
              & r1_tarski(k2_relat_1(X1),k2_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(t194_funct_2,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3,X4,X5] :
              ( ( v1_funct_1(X5)
                & v1_funct_2(X5,X1,X2)
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
             => ! [X6] :
                  ( ( v1_funct_1(X6)
                    & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
                 => ( r1_tarski(k2_relset_1(X1,X2,X5),k1_relset_1(X2,X3,k2_partfun1(X2,X3,X6,X4)))
                   => r2_funct_2(X1,X3,k8_funct_2(X1,X2,X3,X5,k2_partfun1(X2,X3,X6,X4)),k8_funct_2(X1,X2,X3,X5,X6)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t194_funct_2)).

fof(t104_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_tarski(X1,X2)
       => r1_tarski(k7_relat_1(X3,X1),k7_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_relat_1)).

fof(redefinition_r2_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_funct_2(X1,X2,X3,X4)
      <=> X3 = X4 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

fof(dt_k8_funct_2,axiom,(
    ! [X1,X2,X3,X4,X5] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
     => ( v1_funct_1(k8_funct_2(X1,X2,X3,X4,X5))
        & v1_funct_2(k8_funct_2(X1,X2,X3,X4,X5),X1,X3)
        & m1_subset_1(k8_funct_2(X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_funct_2)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ~ v1_xboole_0(X2)
           => ! [X3,X4,X5,X6] :
                ( ( v1_funct_1(X6)
                  & v1_funct_2(X6,X1,X2)
                  & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
               => ! [X7] :
                    ( ( v1_funct_1(X7)
                      & m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
                   => ( ( r1_tarski(k2_relset_1(X1,X2,X6),k1_relset_1(X2,X3,k2_partfun1(X2,X3,X7,X4)))
                        & r1_tarski(X4,X5) )
                     => r2_funct_2(X1,X3,k8_funct_2(X1,X2,X3,X6,k2_partfun1(X2,X3,X7,X4)),k8_funct_2(X1,X2,X3,X6,k2_partfun1(X2,X3,X7,X5))) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t195_funct_2])).

fof(c_0_12,plain,(
    ! [X8,X9,X10] :
      ( ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
      | v1_relat_1(X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_13,plain,(
    ! [X11,X12,X13,X14] :
      ( ( v1_funct_1(k2_partfun1(X11,X12,X13,X14))
        | ~ v1_funct_1(X13)
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12))) )
      & ( m1_subset_1(k2_partfun1(X11,X12,X13,X14),k1_zfmisc_1(k2_zfmisc_1(X11,X12)))
        | ~ v1_funct_1(X13)
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_partfun1])])])).

fof(c_0_14,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0)
    & ~ v1_xboole_0(esk2_0)
    & v1_funct_1(esk6_0)
    & v1_funct_2(esk6_0,esk1_0,esk2_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    & v1_funct_1(esk7_0)
    & m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))
    & r1_tarski(k2_relset_1(esk1_0,esk2_0,esk6_0),k1_relset_1(esk2_0,esk3_0,k2_partfun1(esk2_0,esk3_0,esk7_0,esk4_0)))
    & r1_tarski(esk4_0,esk5_0)
    & ~ r2_funct_2(esk1_0,esk3_0,k8_funct_2(esk1_0,esk2_0,esk3_0,esk6_0,k2_partfun1(esk2_0,esk3_0,esk7_0,esk4_0)),k8_funct_2(esk1_0,esk2_0,esk3_0,esk6_0,k2_partfun1(esk2_0,esk3_0,esk7_0,esk5_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])).

fof(c_0_15,plain,(
    ! [X23,X24,X25,X26] :
      ( ~ v1_funct_1(X25)
      | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))
      | k2_partfun1(X23,X24,X25,X26) = k7_relat_1(X25,X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).

cnf(c_0_16,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( m1_subset_1(k2_partfun1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_18,plain,(
    ! [X47,X48,X49] :
      ( ~ r1_tarski(X47,X48)
      | ~ r1_tarski(X48,X49)
      | r1_tarski(X47,X49) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_19,plain,(
    ! [X50,X51] :
      ( ( r1_tarski(k1_relat_1(X50),k1_relat_1(X51))
        | ~ r1_tarski(X50,X51)
        | ~ v1_relat_1(X51)
        | ~ v1_relat_1(X50) )
      & ( r1_tarski(k2_relat_1(X50),k2_relat_1(X51))
        | ~ r1_tarski(X50,X51)
        | ~ v1_relat_1(X51)
        | ~ v1_relat_1(X50) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).

cnf(c_0_20,negated_conjecture,
    ( r1_tarski(k2_relset_1(esk1_0,esk2_0,esk6_0),k1_relset_1(esk2_0,esk3_0,k2_partfun1(esk2_0,esk3_0,esk7_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( k2_partfun1(X2,X3,X1,X4) = k7_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_24,plain,(
    ! [X20,X21,X22] :
      ( ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))
      | k1_relset_1(X20,X21,X22) = k1_relat_1(X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_25,plain,
    ( v1_relat_1(k2_partfun1(X1,X2,X3,X4))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(k2_relset_1(esk1_0,esk2_0,esk6_0),k1_relset_1(esk2_0,esk3_0,k7_relat_1(esk7_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_23])])).

cnf(c_0_29,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(spm,[status(thm)],[c_0_25,c_0_21])).

fof(c_0_31,plain,(
    ! [X41,X42,X43,X44,X45,X46] :
      ( v1_xboole_0(X41)
      | v1_xboole_0(X42)
      | ~ v1_funct_1(X45)
      | ~ v1_funct_2(X45,X41,X42)
      | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))
      | ~ v1_funct_1(X46)
      | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))
      | ~ r1_tarski(k2_relset_1(X41,X42,X45),k1_relset_1(X42,X43,k2_partfun1(X42,X43,X46,X44)))
      | r2_funct_2(X41,X43,k8_funct_2(X41,X42,X43,X45,k2_partfun1(X42,X43,X46,X44)),k8_funct_2(X41,X42,X43,X45,X46)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t194_funct_2])])])])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,k1_relat_1(X2))
    | ~ r1_tarski(X1,k1_relat_1(X3))
    | ~ r1_tarski(X3,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(k2_relset_1(esk1_0,esk2_0,esk6_0),k1_relat_1(k7_relat_1(esk7_0,esk4_0)))
    | ~ m1_subset_1(k7_relat_1(esk7_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( v1_relat_1(k7_relat_1(esk7_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_23]),c_0_22])])).

fof(c_0_35,plain,(
    ! [X38,X39,X40] :
      ( ~ v1_relat_1(X40)
      | ~ r1_tarski(X38,X39)
      | r1_tarski(k7_relat_1(X40,X38),k7_relat_1(X40,X39)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t104_relat_1])])).

cnf(c_0_36,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | r2_funct_2(X1,X5,k8_funct_2(X1,X2,X5,X3,k2_partfun1(X2,X5,X4,X6)),k8_funct_2(X1,X2,X5,X3,X4))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X5)))
    | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X5,k2_partfun1(X2,X5,X4,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(k2_relset_1(esk1_0,esk2_0,esk6_0),k1_relat_1(X1))
    | ~ r1_tarski(k7_relat_1(esk7_0,esk4_0),X1)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(k7_relat_1(esk7_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])])).

cnf(c_0_38,plain,
    ( r1_tarski(k7_relat_1(X1,X2),k7_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_39,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_23])).

cnf(c_0_40,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | r2_funct_2(X1,X3,k8_funct_2(X1,X2,X3,X4,k7_relat_1(X5,X6)),k8_funct_2(X1,X2,X3,X4,X5))
    | ~ r1_tarski(k2_relset_1(X1,X2,X4),k1_relset_1(X2,X3,k7_relat_1(X5,X6)))
    | ~ v1_funct_2(X4,X1,X2)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_21])).

cnf(c_0_41,plain,
    ( m1_subset_1(k7_relat_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(spm,[status(thm)],[c_0_17,c_0_21])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(k2_relset_1(esk1_0,esk2_0,esk6_0),k1_relat_1(k7_relat_1(esk7_0,X1)))
    | ~ r1_tarski(esk4_0,X1)
    | ~ m1_subset_1(k7_relat_1(esk7_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_34]),c_0_39])])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_44,plain,(
    ! [X30,X31,X32,X33] :
      ( ( ~ r2_funct_2(X30,X31,X32,X33)
        | X32 = X33
        | ~ v1_funct_1(X32)
        | ~ v1_funct_2(X32,X30,X31)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))
        | ~ v1_funct_1(X33)
        | ~ v1_funct_2(X33,X30,X31)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) )
      & ( X32 != X33
        | r2_funct_2(X30,X31,X32,X33)
        | ~ v1_funct_1(X32)
        | ~ v1_funct_2(X32,X30,X31)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))
        | ~ v1_funct_1(X33)
        | ~ v1_funct_2(X33,X30,X31)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_funct_2])])])).

cnf(c_0_45,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | r2_funct_2(X2,X3,k8_funct_2(X2,X1,X3,X4,k7_relat_1(X5,X6)),k8_funct_2(X2,X1,X3,X4,X5))
    | ~ r1_tarski(k2_relset_1(X2,X1,X4),k1_relat_1(k7_relat_1(X5,X6)))
    | ~ v1_funct_2(X4,X2,X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_29]),c_0_41])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(k2_relset_1(esk1_0,esk2_0,esk6_0),k1_relat_1(k7_relat_1(esk7_0,esk5_0)))
    | ~ m1_subset_1(k7_relat_1(esk7_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_47,negated_conjecture,
    ( v1_funct_2(esk6_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_48,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_50,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_51,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_52,plain,
    ( v1_funct_1(k2_partfun1(X1,X2,X3,X4))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_53,plain,
    ( X3 = X4
    | ~ r2_funct_2(X1,X2,X3,X4)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_54,negated_conjecture,
    ( r2_funct_2(esk1_0,X1,k8_funct_2(esk1_0,esk2_0,X1,esk6_0,k7_relat_1(esk7_0,esk5_0)),k8_funct_2(esk1_0,esk2_0,X1,esk6_0,esk7_0))
    | ~ m1_subset_1(k7_relat_1(esk7_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,X1))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47]),c_0_22]),c_0_48]),c_0_49])]),c_0_50]),c_0_51])).

fof(c_0_55,plain,(
    ! [X15,X16,X17,X18,X19] :
      ( ( v1_funct_1(k8_funct_2(X15,X16,X17,X18,X19))
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,X15,X16)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))
        | ~ v1_funct_1(X19)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X16,X17))) )
      & ( v1_funct_2(k8_funct_2(X15,X16,X17,X18,X19),X15,X17)
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,X15,X16)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))
        | ~ v1_funct_1(X19)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X16,X17))) )
      & ( m1_subset_1(k8_funct_2(X15,X16,X17,X18,X19),k1_zfmisc_1(k2_zfmisc_1(X15,X17)))
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,X15,X16)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))
        | ~ v1_funct_1(X19)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X16,X17))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_funct_2])])])).

cnf(c_0_56,plain,
    ( v1_funct_1(k7_relat_1(X1,X2))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_21])).

cnf(c_0_57,negated_conjecture,
    ( k8_funct_2(esk1_0,esk2_0,X1,esk6_0,k7_relat_1(esk7_0,esk5_0)) = k8_funct_2(esk1_0,esk2_0,X1,esk6_0,esk7_0)
    | ~ v1_funct_2(k8_funct_2(esk1_0,esk2_0,X1,esk6_0,k7_relat_1(esk7_0,esk5_0)),esk1_0,X1)
    | ~ v1_funct_2(k8_funct_2(esk1_0,esk2_0,X1,esk6_0,esk7_0),esk1_0,X1)
    | ~ v1_funct_1(k8_funct_2(esk1_0,esk2_0,X1,esk6_0,k7_relat_1(esk7_0,esk5_0)))
    | ~ v1_funct_1(k8_funct_2(esk1_0,esk2_0,X1,esk6_0,esk7_0))
    | ~ m1_subset_1(k8_funct_2(esk1_0,esk2_0,X1,esk6_0,k7_relat_1(esk7_0,esk5_0)),k1_zfmisc_1(k2_zfmisc_1(esk1_0,X1)))
    | ~ m1_subset_1(k8_funct_2(esk1_0,esk2_0,X1,esk6_0,esk7_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,X1)))
    | ~ m1_subset_1(k7_relat_1(esk7_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,X1))) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_58,plain,
    ( v1_funct_2(k8_funct_2(X1,X2,X3,X4,X5),X1,X3)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_59,negated_conjecture,
    ( v1_funct_1(k7_relat_1(esk7_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_23]),c_0_22])])).

cnf(c_0_60,negated_conjecture,
    ( m1_subset_1(k7_relat_1(esk7_0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_22])).

cnf(c_0_61,negated_conjecture,
    ( k8_funct_2(esk1_0,esk2_0,X1,esk6_0,k7_relat_1(esk7_0,esk5_0)) = k8_funct_2(esk1_0,esk2_0,X1,esk6_0,esk7_0)
    | ~ v1_funct_2(k8_funct_2(esk1_0,esk2_0,X1,esk6_0,esk7_0),esk1_0,X1)
    | ~ v1_funct_1(k8_funct_2(esk1_0,esk2_0,X1,esk6_0,k7_relat_1(esk7_0,esk5_0)))
    | ~ v1_funct_1(k8_funct_2(esk1_0,esk2_0,X1,esk6_0,esk7_0))
    | ~ m1_subset_1(k8_funct_2(esk1_0,esk2_0,X1,esk6_0,k7_relat_1(esk7_0,esk5_0)),k1_zfmisc_1(k2_zfmisc_1(esk1_0,X1)))
    | ~ m1_subset_1(k8_funct_2(esk1_0,esk2_0,X1,esk6_0,esk7_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,X1)))
    | ~ m1_subset_1(k7_relat_1(esk7_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,X1))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_47]),c_0_59]),c_0_48]),c_0_49])]),c_0_60])).

cnf(c_0_62,plain,
    ( v1_funct_1(k8_funct_2(X1,X2,X3,X4,X5))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_63,negated_conjecture,
    ( ~ r2_funct_2(esk1_0,esk3_0,k8_funct_2(esk1_0,esk2_0,esk3_0,esk6_0,k2_partfun1(esk2_0,esk3_0,esk7_0,esk4_0)),k8_funct_2(esk1_0,esk2_0,esk3_0,esk6_0,k2_partfun1(esk2_0,esk3_0,esk7_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_64,negated_conjecture,
    ( k8_funct_2(esk1_0,esk2_0,X1,esk6_0,k7_relat_1(esk7_0,esk5_0)) = k8_funct_2(esk1_0,esk2_0,X1,esk6_0,esk7_0)
    | ~ v1_funct_2(k8_funct_2(esk1_0,esk2_0,X1,esk6_0,esk7_0),esk1_0,X1)
    | ~ v1_funct_1(k8_funct_2(esk1_0,esk2_0,X1,esk6_0,esk7_0))
    | ~ m1_subset_1(k8_funct_2(esk1_0,esk2_0,X1,esk6_0,k7_relat_1(esk7_0,esk5_0)),k1_zfmisc_1(k2_zfmisc_1(esk1_0,X1)))
    | ~ m1_subset_1(k8_funct_2(esk1_0,esk2_0,X1,esk6_0,esk7_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,X1)))
    | ~ m1_subset_1(k7_relat_1(esk7_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,X1))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_47]),c_0_59]),c_0_48]),c_0_49])]),c_0_60])).

cnf(c_0_65,plain,
    ( m1_subset_1(k8_funct_2(X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_66,negated_conjecture,
    ( ~ r2_funct_2(esk1_0,esk3_0,k8_funct_2(esk1_0,esk2_0,esk3_0,esk6_0,k2_partfun1(esk2_0,esk3_0,esk7_0,esk4_0)),k8_funct_2(esk1_0,esk2_0,esk3_0,esk6_0,k7_relat_1(esk7_0,esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_21]),c_0_22]),c_0_23])])).

cnf(c_0_67,negated_conjecture,
    ( k8_funct_2(esk1_0,esk2_0,X1,esk6_0,k7_relat_1(esk7_0,esk5_0)) = k8_funct_2(esk1_0,esk2_0,X1,esk6_0,esk7_0)
    | ~ v1_funct_2(k8_funct_2(esk1_0,esk2_0,X1,esk6_0,esk7_0),esk1_0,X1)
    | ~ v1_funct_1(k8_funct_2(esk1_0,esk2_0,X1,esk6_0,esk7_0))
    | ~ m1_subset_1(k8_funct_2(esk1_0,esk2_0,X1,esk6_0,esk7_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,X1)))
    | ~ m1_subset_1(k7_relat_1(esk7_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,X1))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_47]),c_0_59]),c_0_48]),c_0_49])]),c_0_60])).

cnf(c_0_68,negated_conjecture,
    ( r2_funct_2(esk1_0,esk3_0,k8_funct_2(esk1_0,esk2_0,esk3_0,esk6_0,k2_partfun1(esk2_0,esk3_0,esk7_0,esk4_0)),k8_funct_2(esk1_0,esk2_0,esk3_0,esk6_0,esk7_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_20]),c_0_47]),c_0_22]),c_0_48]),c_0_23]),c_0_49])]),c_0_50]),c_0_51])).

cnf(c_0_69,negated_conjecture,
    ( ~ v1_funct_2(k8_funct_2(esk1_0,esk2_0,esk3_0,esk6_0,esk7_0),esk1_0,esk3_0)
    | ~ v1_funct_1(k8_funct_2(esk1_0,esk2_0,esk3_0,esk6_0,esk7_0))
    | ~ m1_subset_1(k8_funct_2(esk1_0,esk2_0,esk3_0,esk6_0,esk7_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0)))
    | ~ m1_subset_1(k7_relat_1(esk7_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_68]),c_0_23])])).

cnf(c_0_70,negated_conjecture,
    ( ~ v1_funct_2(k8_funct_2(esk1_0,esk2_0,esk3_0,esk6_0,esk7_0),esk1_0,esk3_0)
    | ~ v1_funct_1(k8_funct_2(esk1_0,esk2_0,esk3_0,esk6_0,esk7_0))
    | ~ m1_subset_1(k8_funct_2(esk1_0,esk2_0,esk3_0,esk6_0,esk7_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_60]),c_0_23])])).

cnf(c_0_71,negated_conjecture,
    ( ~ v1_funct_1(k8_funct_2(esk1_0,esk2_0,esk3_0,esk6_0,esk7_0))
    | ~ m1_subset_1(k8_funct_2(esk1_0,esk2_0,esk3_0,esk6_0,esk7_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_58]),c_0_47]),c_0_22]),c_0_48]),c_0_23]),c_0_49])])).

cnf(c_0_72,negated_conjecture,
    ( ~ m1_subset_1(k8_funct_2(esk1_0,esk2_0,esk3_0,esk6_0,esk7_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_62]),c_0_47]),c_0_22]),c_0_48]),c_0_23]),c_0_49])])).

cnf(c_0_73,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_65]),c_0_47]),c_0_22]),c_0_48]),c_0_23]),c_0_49])]),
    [proof]).

%------------------------------------------------------------------------------
