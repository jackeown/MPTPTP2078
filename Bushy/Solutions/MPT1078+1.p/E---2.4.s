%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : funct_2__t195_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:40 EDT 2019

% Result     : Theorem 0.90s
% Output     : CNFRefutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 639 expanded)
%              Number of clauses        :   60 ( 226 expanded)
%              Number of leaves         :   13 ( 153 expanded)
%              Depth                    :   14
%              Number of atoms          :  307 (4248 expanded)
%              Number of equality atoms :   21 (  41 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   18 (   2 average)
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
    file('/export/starexec/sandbox2/benchmark/funct_2__t195_funct_2.p',t195_funct_2)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t195_funct_2.p',redefinition_k2_relset_1)).

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
    file('/export/starexec/sandbox2/benchmark/funct_2__t195_funct_2.p',t194_funct_2)).

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
    file('/export/starexec/sandbox2/benchmark/funct_2__t195_funct_2.p',dt_k8_funct_2)).

fof(dt_k2_partfun1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( v1_funct_1(k2_partfun1(X1,X2,X3,X4))
        & m1_subset_1(k2_partfun1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t195_funct_2.p',dt_k2_partfun1)).

fof(t104_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_tarski(X1,X2)
       => r1_tarski(k7_relat_1(X3,X1),k7_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t195_funct_2.p',t104_relat_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t195_funct_2.p',cc1_relset_1)).

fof(redefinition_k2_partfun1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => k2_partfun1(X1,X2,X3,X4) = k7_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t195_funct_2.p',redefinition_k2_partfun1)).

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
    file('/export/starexec/sandbox2/benchmark/funct_2__t195_funct_2.p',redefinition_r2_funct_2)).

fof(t25_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
              & r1_tarski(k2_relat_1(X1),k2_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t195_funct_2.p',t25_relat_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t195_funct_2.p',redefinition_k1_relset_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t195_funct_2.p',t1_xboole_1)).

fof(symmetry_r2_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_funct_2(X1,X2,X3,X4)
       => r2_funct_2(X1,X2,X4,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t195_funct_2.p',symmetry_r2_funct_2)).

fof(c_0_13,negated_conjecture,(
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

fof(c_0_14,plain,(
    ! [X43,X44,X45] :
      ( ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))
      | k2_relset_1(X43,X44,X45) = k2_relat_1(X45) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_15,negated_conjecture,
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
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).

fof(c_0_16,plain,(
    ! [X68,X69,X70,X71,X72,X73] :
      ( v1_xboole_0(X68)
      | v1_xboole_0(X69)
      | ~ v1_funct_1(X72)
      | ~ v1_funct_2(X72,X68,X69)
      | ~ m1_subset_1(X72,k1_zfmisc_1(k2_zfmisc_1(X68,X69)))
      | ~ v1_funct_1(X73)
      | ~ m1_subset_1(X73,k1_zfmisc_1(k2_zfmisc_1(X69,X70)))
      | ~ r1_tarski(k2_relset_1(X68,X69,X72),k1_relset_1(X69,X70,k2_partfun1(X69,X70,X73,X71)))
      | r2_funct_2(X68,X70,k8_funct_2(X68,X69,X70,X72,k2_partfun1(X69,X70,X73,X71)),k8_funct_2(X68,X69,X70,X72,X73)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t194_funct_2])])])])).

cnf(c_0_17,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | r2_funct_2(X1,X5,k8_funct_2(X1,X2,X5,X3,k2_partfun1(X2,X5,X4,X6)),k8_funct_2(X1,X2,X5,X3,X4))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X5)))
    | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X5,k2_partfun1(X2,X5,X4,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( v1_funct_2(esk6_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( k2_relset_1(esk1_0,esk2_0,esk6_0) = k2_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,negated_conjecture,
    ( r2_funct_2(esk1_0,X1,k8_funct_2(esk1_0,esk2_0,X1,esk6_0,k2_partfun1(esk2_0,X1,X2,X3)),k8_funct_2(esk1_0,esk2_0,X1,esk6_0,X2))
    | ~ r1_tarski(k2_relat_1(esk6_0),k1_relset_1(esk2_0,X1,k2_partfun1(esk2_0,X1,X2,X3)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(esk2_0,X1)))
    | ~ v1_funct_1(X2) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_18]),c_0_22])]),c_0_23]),c_0_24])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_27,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(k2_relset_1(esk1_0,esk2_0,esk6_0),k1_relset_1(esk2_0,esk3_0,k2_partfun1(esk2_0,esk3_0,esk7_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_29,plain,(
    ! [X29,X30,X31,X32,X33] :
      ( ( v1_funct_1(k8_funct_2(X29,X30,X31,X32,X33))
        | ~ v1_funct_1(X32)
        | ~ v1_funct_2(X32,X29,X30)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))
        | ~ v1_funct_1(X33)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) )
      & ( v1_funct_2(k8_funct_2(X29,X30,X31,X32,X33),X29,X31)
        | ~ v1_funct_1(X32)
        | ~ v1_funct_2(X32,X29,X30)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))
        | ~ v1_funct_1(X33)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) )
      & ( m1_subset_1(k8_funct_2(X29,X30,X31,X32,X33),k1_zfmisc_1(k2_zfmisc_1(X29,X31)))
        | ~ v1_funct_1(X32)
        | ~ v1_funct_2(X32,X29,X30)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))
        | ~ v1_funct_1(X33)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_funct_2])])])).

fof(c_0_30,plain,(
    ! [X20,X21,X22,X23] :
      ( ( v1_funct_1(k2_partfun1(X20,X21,X22,X23))
        | ~ v1_funct_1(X22)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) )
      & ( m1_subset_1(k2_partfun1(X20,X21,X22,X23),k1_zfmisc_1(k2_zfmisc_1(X20,X21)))
        | ~ v1_funct_1(X22)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_partfun1])])])).

fof(c_0_31,plain,(
    ! [X65,X66,X67] :
      ( ~ v1_relat_1(X67)
      | ~ r1_tarski(X65,X66)
      | r1_tarski(k7_relat_1(X67,X65),k7_relat_1(X67,X66)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t104_relat_1])])).

fof(c_0_32,plain,(
    ! [X96,X97,X98] :
      ( ~ m1_subset_1(X98,k1_zfmisc_1(k2_zfmisc_1(X96,X97)))
      | v1_relat_1(X98) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_33,plain,(
    ! [X39,X40,X41,X42] :
      ( ~ v1_funct_1(X41)
      | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))
      | k2_partfun1(X39,X40,X41,X42) = k7_relat_1(X41,X42) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).

fof(c_0_34,plain,(
    ! [X50,X51,X52,X53] :
      ( ( ~ r2_funct_2(X50,X51,X52,X53)
        | X52 = X53
        | ~ v1_funct_1(X52)
        | ~ v1_funct_2(X52,X50,X51)
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51)))
        | ~ v1_funct_1(X53)
        | ~ v1_funct_2(X53,X50,X51)
        | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X50,X51))) )
      & ( X52 != X53
        | r2_funct_2(X50,X51,X52,X53)
        | ~ v1_funct_1(X52)
        | ~ v1_funct_2(X52,X50,X51)
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51)))
        | ~ v1_funct_1(X53)
        | ~ v1_funct_2(X53,X50,X51)
        | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X50,X51))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_funct_2])])])).

cnf(c_0_35,negated_conjecture,
    ( r2_funct_2(esk1_0,esk3_0,k8_funct_2(esk1_0,esk2_0,esk3_0,esk6_0,k2_partfun1(esk2_0,esk3_0,esk7_0,X1)),k8_funct_2(esk1_0,esk2_0,esk3_0,esk6_0,esk7_0))
    | ~ r1_tarski(k2_relat_1(esk6_0),k1_relset_1(esk2_0,esk3_0,k2_partfun1(esk2_0,esk3_0,esk7_0,X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk6_0),k1_relset_1(esk2_0,esk3_0,k2_partfun1(esk2_0,esk3_0,esk7_0,esk4_0))) ),
    inference(rw,[status(thm)],[c_0_28,c_0_21])).

cnf(c_0_37,plain,
    ( v1_funct_1(k8_funct_2(X1,X2,X3,X4,X5))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,plain,
    ( m1_subset_1(k2_partfun1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,plain,
    ( v1_funct_1(k2_partfun1(X1,X2,X3,X4))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,plain,
    ( r1_tarski(k7_relat_1(X1,X2),k7_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_41,negated_conjecture,
    ( r1_tarski(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_42,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_43,plain,
    ( k2_partfun1(X2,X3,X1,X4) = k7_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_44,plain,
    ( X3 = X4
    | ~ r2_funct_2(X1,X2,X3,X4)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_45,negated_conjecture,
    ( r2_funct_2(esk1_0,esk3_0,k8_funct_2(esk1_0,esk2_0,esk3_0,esk6_0,k2_partfun1(esk2_0,esk3_0,esk7_0,esk4_0)),k8_funct_2(esk1_0,esk2_0,esk3_0,esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_46,negated_conjecture,
    ( v1_funct_1(k8_funct_2(esk1_0,esk2_0,X1,esk6_0,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(esk2_0,X1)))
    | ~ v1_funct_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_20]),c_0_18]),c_0_22])])).

cnf(c_0_47,negated_conjecture,
    ( m1_subset_1(k2_partfun1(esk2_0,esk3_0,esk7_0,X1),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_26]),c_0_27])])).

cnf(c_0_48,negated_conjecture,
    ( v1_funct_1(k2_partfun1(esk2_0,esk3_0,esk7_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_26]),c_0_27])])).

cnf(c_0_49,plain,
    ( m1_subset_1(k8_funct_2(X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_50,plain,(
    ! [X79,X80] :
      ( ( r1_tarski(k1_relat_1(X79),k1_relat_1(X80))
        | ~ r1_tarski(X79,X80)
        | ~ v1_relat_1(X80)
        | ~ v1_relat_1(X79) )
      & ( r1_tarski(k2_relat_1(X79),k2_relat_1(X80))
        | ~ r1_tarski(X79,X80)
        | ~ v1_relat_1(X80)
        | ~ v1_relat_1(X79) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(k7_relat_1(X1,esk4_0),k7_relat_1(X1,esk5_0))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_52,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_26])).

cnf(c_0_53,negated_conjecture,
    ( k7_relat_1(esk7_0,X1) = k2_partfun1(esk2_0,esk3_0,esk7_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_26]),c_0_27])])).

fof(c_0_54,plain,(
    ! [X36,X37,X38] :
      ( ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))
      | k1_relset_1(X36,X37,X38) = k1_relat_1(X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_55,negated_conjecture,
    ( k8_funct_2(esk1_0,esk2_0,esk3_0,esk6_0,k2_partfun1(esk2_0,esk3_0,esk7_0,esk4_0)) = k8_funct_2(esk1_0,esk2_0,esk3_0,esk6_0,esk7_0)
    | ~ m1_subset_1(k8_funct_2(esk1_0,esk2_0,esk3_0,esk6_0,k2_partfun1(esk2_0,esk3_0,esk7_0,esk4_0)),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0)))
    | ~ m1_subset_1(k8_funct_2(esk1_0,esk2_0,esk3_0,esk6_0,esk7_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0)))
    | ~ v1_funct_2(k8_funct_2(esk1_0,esk2_0,esk3_0,esk6_0,k2_partfun1(esk2_0,esk3_0,esk7_0,esk4_0)),esk1_0,esk3_0)
    | ~ v1_funct_2(k8_funct_2(esk1_0,esk2_0,esk3_0,esk6_0,esk7_0),esk1_0,esk3_0)
    | ~ v1_funct_1(k8_funct_2(esk1_0,esk2_0,esk3_0,esk6_0,k2_partfun1(esk2_0,esk3_0,esk7_0,esk4_0)))
    | ~ v1_funct_1(k8_funct_2(esk1_0,esk2_0,esk3_0,esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_56,negated_conjecture,
    ( v1_funct_1(k8_funct_2(esk1_0,esk2_0,esk3_0,esk6_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_26]),c_0_27])])).

cnf(c_0_57,negated_conjecture,
    ( v1_funct_1(k8_funct_2(esk1_0,esk2_0,esk3_0,esk6_0,k2_partfun1(esk2_0,esk3_0,esk7_0,X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48])])).

cnf(c_0_58,negated_conjecture,
    ( m1_subset_1(k8_funct_2(esk1_0,esk2_0,X1,esk6_0,X2),k1_zfmisc_1(k2_zfmisc_1(esk1_0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(esk2_0,X1)))
    | ~ v1_funct_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_20]),c_0_18]),c_0_22])])).

cnf(c_0_59,plain,
    ( v1_funct_2(k8_funct_2(X1,X2,X3,X4,X5),X1,X3)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_60,plain,(
    ! [X76,X77,X78] :
      ( ~ r1_tarski(X76,X77)
      | ~ r1_tarski(X77,X78)
      | r1_tarski(X76,X78) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_61,plain,
    ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(k2_partfun1(esk2_0,esk3_0,esk7_0,esk4_0),k2_partfun1(esk2_0,esk3_0,esk7_0,esk5_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53]),c_0_53])).

cnf(c_0_63,negated_conjecture,
    ( v1_relat_1(k2_partfun1(esk2_0,esk3_0,esk7_0,X1)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_47])).

cnf(c_0_64,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_65,negated_conjecture,
    ( k8_funct_2(esk1_0,esk2_0,esk3_0,esk6_0,k2_partfun1(esk2_0,esk3_0,esk7_0,esk4_0)) = k8_funct_2(esk1_0,esk2_0,esk3_0,esk6_0,esk7_0)
    | ~ m1_subset_1(k8_funct_2(esk1_0,esk2_0,esk3_0,esk6_0,k2_partfun1(esk2_0,esk3_0,esk7_0,esk4_0)),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0)))
    | ~ m1_subset_1(k8_funct_2(esk1_0,esk2_0,esk3_0,esk6_0,esk7_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0)))
    | ~ v1_funct_2(k8_funct_2(esk1_0,esk2_0,esk3_0,esk6_0,k2_partfun1(esk2_0,esk3_0,esk7_0,esk4_0)),esk1_0,esk3_0)
    | ~ v1_funct_2(k8_funct_2(esk1_0,esk2_0,esk3_0,esk6_0,esk7_0),esk1_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_56])]),c_0_57])])).

cnf(c_0_66,negated_conjecture,
    ( m1_subset_1(k8_funct_2(esk1_0,esk2_0,esk3_0,esk6_0,esk7_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_26]),c_0_27])])).

cnf(c_0_67,negated_conjecture,
    ( v1_funct_2(k8_funct_2(esk1_0,esk2_0,X1,esk6_0,X2),esk1_0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(esk2_0,X1)))
    | ~ v1_funct_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_20]),c_0_18]),c_0_22])])).

cnf(c_0_68,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_69,negated_conjecture,
    ( r1_tarski(k1_relat_1(k2_partfun1(esk2_0,esk3_0,esk7_0,esk4_0)),k1_relat_1(k2_partfun1(esk2_0,esk3_0,esk7_0,esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63]),c_0_63])])).

cnf(c_0_70,negated_conjecture,
    ( k1_relset_1(esk2_0,esk3_0,k2_partfun1(esk2_0,esk3_0,esk7_0,X1)) = k1_relat_1(k2_partfun1(esk2_0,esk3_0,esk7_0,X1)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_47])).

cnf(c_0_71,negated_conjecture,
    ( k8_funct_2(esk1_0,esk2_0,esk3_0,esk6_0,k2_partfun1(esk2_0,esk3_0,esk7_0,esk4_0)) = k8_funct_2(esk1_0,esk2_0,esk3_0,esk6_0,esk7_0)
    | ~ m1_subset_1(k8_funct_2(esk1_0,esk2_0,esk3_0,esk6_0,k2_partfun1(esk2_0,esk3_0,esk7_0,esk4_0)),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0)))
    | ~ v1_funct_2(k8_funct_2(esk1_0,esk2_0,esk3_0,esk6_0,k2_partfun1(esk2_0,esk3_0,esk7_0,esk4_0)),esk1_0,esk3_0)
    | ~ v1_funct_2(k8_funct_2(esk1_0,esk2_0,esk3_0,esk6_0,esk7_0),esk1_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_66])])).

cnf(c_0_72,negated_conjecture,
    ( v1_funct_2(k8_funct_2(esk1_0,esk2_0,esk3_0,esk6_0,esk7_0),esk1_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_26]),c_0_27])])).

cnf(c_0_73,negated_conjecture,
    ( v1_funct_2(k8_funct_2(esk1_0,esk2_0,esk3_0,esk6_0,k2_partfun1(esk2_0,esk3_0,esk7_0,X1)),esk1_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_47]),c_0_48])])).

cnf(c_0_74,negated_conjecture,
    ( r1_tarski(X1,k1_relat_1(k2_partfun1(esk2_0,esk3_0,esk7_0,esk5_0)))
    | ~ r1_tarski(X1,k1_relat_1(k2_partfun1(esk2_0,esk3_0,esk7_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_75,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk6_0),k1_relat_1(k2_partfun1(esk2_0,esk3_0,esk7_0,esk4_0))) ),
    inference(rw,[status(thm)],[c_0_36,c_0_70])).

cnf(c_0_76,negated_conjecture,
    ( k8_funct_2(esk1_0,esk2_0,esk3_0,esk6_0,k2_partfun1(esk2_0,esk3_0,esk7_0,esk4_0)) = k8_funct_2(esk1_0,esk2_0,esk3_0,esk6_0,esk7_0)
    | ~ m1_subset_1(k8_funct_2(esk1_0,esk2_0,esk3_0,esk6_0,k2_partfun1(esk2_0,esk3_0,esk7_0,esk4_0)),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_72])]),c_0_73])])).

cnf(c_0_77,negated_conjecture,
    ( m1_subset_1(k8_funct_2(esk1_0,esk2_0,esk3_0,esk6_0,k2_partfun1(esk2_0,esk3_0,esk7_0,X1)),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_47]),c_0_48])])).

fof(c_0_78,plain,(
    ! [X61,X62,X63,X64] :
      ( ~ v1_funct_1(X63)
      | ~ v1_funct_2(X63,X61,X62)
      | ~ m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X61,X62)))
      | ~ v1_funct_1(X64)
      | ~ v1_funct_2(X64,X61,X62)
      | ~ m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X61,X62)))
      | ~ r2_funct_2(X61,X62,X63,X64)
      | r2_funct_2(X61,X62,X64,X63) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r2_funct_2])])).

cnf(c_0_79,negated_conjecture,
    ( r2_funct_2(esk1_0,esk3_0,k8_funct_2(esk1_0,esk2_0,esk3_0,esk6_0,k2_partfun1(esk2_0,esk3_0,esk7_0,X1)),k8_funct_2(esk1_0,esk2_0,esk3_0,esk6_0,esk7_0))
    | ~ r1_tarski(k2_relat_1(esk6_0),k1_relat_1(k2_partfun1(esk2_0,esk3_0,esk7_0,X1))) ),
    inference(rw,[status(thm)],[c_0_35,c_0_70])).

cnf(c_0_80,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk6_0),k1_relat_1(k2_partfun1(esk2_0,esk3_0,esk7_0,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_81,negated_conjecture,
    ( ~ r2_funct_2(esk1_0,esk3_0,k8_funct_2(esk1_0,esk2_0,esk3_0,esk6_0,k2_partfun1(esk2_0,esk3_0,esk7_0,esk4_0)),k8_funct_2(esk1_0,esk2_0,esk3_0,esk6_0,k2_partfun1(esk2_0,esk3_0,esk7_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_82,negated_conjecture,
    ( k8_funct_2(esk1_0,esk2_0,esk3_0,esk6_0,k2_partfun1(esk2_0,esk3_0,esk7_0,esk4_0)) = k8_funct_2(esk1_0,esk2_0,esk3_0,esk6_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_77])])).

cnf(c_0_83,plain,
    ( r2_funct_2(X2,X3,X4,X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_funct_2(X2,X3,X1,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_84,negated_conjecture,
    ( r2_funct_2(esk1_0,esk3_0,k8_funct_2(esk1_0,esk2_0,esk3_0,esk6_0,k2_partfun1(esk2_0,esk3_0,esk7_0,esk5_0)),k8_funct_2(esk1_0,esk2_0,esk3_0,esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_85,negated_conjecture,
    ( ~ r2_funct_2(esk1_0,esk3_0,k8_funct_2(esk1_0,esk2_0,esk3_0,esk6_0,esk7_0),k8_funct_2(esk1_0,esk2_0,esk3_0,esk6_0,k2_partfun1(esk2_0,esk3_0,esk7_0,esk5_0))) ),
    inference(rw,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_86,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_66]),c_0_77]),c_0_72]),c_0_73]),c_0_56]),c_0_57])]),c_0_85]),
    [proof]).
%------------------------------------------------------------------------------
