%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : funct_2__t86_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:50 EDT 2019

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 183 expanded)
%              Number of clauses        :   44 (  66 expanded)
%              Number of leaves         :   15 (  45 expanded)
%              Depth                    :    9
%              Number of atoms          :  262 (1100 expanded)
%              Number of equality atoms :   50 (  60 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   12 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t86_funct_2,conjecture,(
    ! [X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_funct_2(X2,X1,X1)
        & v3_funct_2(X2,X1,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => ! [X3] :
          ( ( v1_funct_1(X3)
            & v1_funct_2(X3,X1,X1)
            & v3_funct_2(X3,X1,X1)
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
         => ( r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,X2,X3),X3)
           => r2_relset_1(X1,X1,X2,k6_partfun1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t86_funct_2.p',t86_funct_2)).

fof(t50_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v1_funct_1(X3) )
         => ( ( k1_relat_1(X2) = X1
              & k1_relat_1(X3) = X1
              & r1_tarski(k2_relat_1(X3),X1)
              & v2_funct_1(X2)
              & k5_relat_1(X3,X2) = X2 )
           => X3 = k6_relat_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t86_funct_2.p',t50_funct_1)).

fof(redefinition_k6_partfun1,axiom,(
    ! [X1] : k6_partfun1(X1) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t86_funct_2.p',redefinition_k6_partfun1)).

fof(dt_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k2_relset_1(X1,X2,X3),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t86_funct_2.p',dt_k2_relset_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t86_funct_2.p',redefinition_k2_relset_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t86_funct_2.p',redefinition_k1_relset_1)).

fof(t67_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_funct_2(X2,X1,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => k1_relset_1(X1,X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t86_funct_2.p',t67_funct_2)).

fof(redefinition_r2_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_relset_1(X1,X2,X3,X4)
      <=> X3 = X4 ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t86_funct_2.p',redefinition_r2_relset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t86_funct_2.p',t3_subset)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t86_funct_2.p',cc1_relset_1)).

fof(dt_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => ( v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))
        & m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t86_funct_2.p',dt_k1_partfun1)).

fof(symmetry_r2_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_relset_1(X1,X2,X3,X4)
       => r2_relset_1(X1,X2,X4,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t86_funct_2.p',symmetry_r2_relset_1)).

fof(cc2_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( v1_funct_1(X3)
          & v3_funct_2(X3,X1,X2) )
       => ( v1_funct_1(X3)
          & v2_funct_1(X3)
          & v2_funct_2(X3,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t86_funct_2.p',cc2_funct_2)).

fof(redefinition_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => k1_partfun1(X1,X2,X3,X4,X5,X6) = k5_relat_1(X5,X6) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t86_funct_2.p',redefinition_k1_partfun1)).

fof(dt_k6_partfun1,axiom,(
    ! [X1] :
      ( v1_partfun1(k6_partfun1(X1),X1)
      & m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t86_funct_2.p',dt_k6_partfun1)).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_funct_2(X2,X1,X1)
          & v3_funct_2(X2,X1,X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
       => ! [X3] :
            ( ( v1_funct_1(X3)
              & v1_funct_2(X3,X1,X1)
              & v3_funct_2(X3,X1,X1)
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
           => ( r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,X2,X3),X3)
             => r2_relset_1(X1,X1,X2,k6_partfun1(X1)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t86_funct_2])).

fof(c_0_16,plain,(
    ! [X64,X65,X66] :
      ( ~ v1_relat_1(X65)
      | ~ v1_funct_1(X65)
      | ~ v1_relat_1(X66)
      | ~ v1_funct_1(X66)
      | k1_relat_1(X65) != X64
      | k1_relat_1(X66) != X64
      | ~ r1_tarski(k2_relat_1(X66),X64)
      | ~ v2_funct_1(X65)
      | k5_relat_1(X66,X65) != X65
      | X66 = k6_relat_1(X64) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_funct_1])])])).

fof(c_0_17,plain,(
    ! [X42] : k6_partfun1(X42) = k6_relat_1(X42) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).

fof(c_0_18,plain,(
    ! [X21,X22,X23] :
      ( ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))
      | m1_subset_1(k2_relset_1(X21,X22,X23),k1_zfmisc_1(X22)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_relset_1])])).

fof(c_0_19,plain,(
    ! [X39,X40,X41] :
      ( ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))
      | k2_relset_1(X39,X40,X41) = k2_relat_1(X41) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_20,plain,(
    ! [X36,X37,X38] :
      ( ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))
      | k1_relset_1(X36,X37,X38) = k1_relat_1(X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_21,plain,(
    ! [X70,X71] :
      ( ~ v1_funct_1(X71)
      | ~ v1_funct_2(X71,X70,X70)
      | ~ m1_subset_1(X71,k1_zfmisc_1(k2_zfmisc_1(X70,X70)))
      | k1_relset_1(X70,X70,X71) = X70 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t67_funct_2])])).

fof(c_0_22,plain,(
    ! [X43,X44,X45,X46] :
      ( ( ~ r2_relset_1(X43,X44,X45,X46)
        | X45 = X46
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X43,X44))) )
      & ( X45 != X46
        | r2_relset_1(X43,X44,X45,X46)
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X43,X44))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).

fof(c_0_23,negated_conjecture,
    ( v1_funct_1(esk2_0)
    & v1_funct_2(esk2_0,esk1_0,esk1_0)
    & v3_funct_2(esk2_0,esk1_0,esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))
    & v1_funct_1(esk3_0)
    & v1_funct_2(esk3_0,esk1_0,esk1_0)
    & v3_funct_2(esk3_0,esk1_0,esk1_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))
    & r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0),esk3_0)
    & ~ r2_relset_1(esk1_0,esk1_0,esk2_0,k6_partfun1(esk1_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

cnf(c_0_24,plain,
    ( X2 = k6_relat_1(X3)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | k1_relat_1(X1) != X3
    | k1_relat_1(X2) != X3
    | ~ r1_tarski(k2_relat_1(X2),X3)
    | ~ v2_funct_1(X1)
    | k5_relat_1(X2,X1) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( k6_partfun1(X1) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_26,plain,(
    ! [X59,X60] :
      ( ( ~ m1_subset_1(X59,k1_zfmisc_1(X60))
        | r1_tarski(X59,X60) )
      & ( ~ r1_tarski(X59,X60)
        | m1_subset_1(X59,k1_zfmisc_1(X60)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_27,plain,
    ( m1_subset_1(k2_relset_1(X2,X3,X1),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( k1_relset_1(X2,X2,X1) = X2
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_31,plain,(
    ! [X77,X78,X79] :
      ( ~ m1_subset_1(X79,k1_zfmisc_1(k2_zfmisc_1(X77,X78)))
      | v1_relat_1(X79) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_32,plain,
    ( X3 = X4
    | ~ r2_relset_1(X1,X2,X3,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,negated_conjecture,
    ( r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_35,plain,(
    ! [X12,X13,X14,X15,X16,X17] :
      ( ( v1_funct_1(k1_partfun1(X12,X13,X14,X15,X16,X17))
        | ~ v1_funct_1(X16)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X12,X13)))
        | ~ v1_funct_1(X17)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X14,X15))) )
      & ( m1_subset_1(k1_partfun1(X12,X13,X14,X15,X16,X17),k1_zfmisc_1(k2_zfmisc_1(X12,X15)))
        | ~ v1_funct_1(X16)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X12,X13)))
        | ~ v1_funct_1(X17)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X14,X15))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_partfun1])])])).

fof(c_0_36,plain,(
    ! [X51,X52,X53,X54] :
      ( ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))
      | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))
      | ~ r2_relset_1(X51,X52,X53,X54)
      | r2_relset_1(X51,X52,X54,X53) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r2_relset_1])])).

cnf(c_0_37,plain,
    ( X2 = k6_partfun1(X3)
    | k1_relat_1(X2) != X3
    | k1_relat_1(X1) != X3
    | k5_relat_1(X2,X1) != X1
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v2_funct_1(X1)
    | ~ r1_tarski(k2_relat_1(X2),X3) ),
    inference(rw,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_39,plain,
    ( m1_subset_1(k2_relat_1(X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_41,plain,
    ( X1 = k1_relat_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_2(X2,X1,X1)
    | ~ v1_funct_1(X2) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_42,negated_conjecture,
    ( v1_funct_2(esk2_0,esk1_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_43,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_44,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_45,plain,(
    ! [X80,X81,X82] :
      ( ( v1_funct_1(X82)
        | ~ v1_funct_1(X82)
        | ~ v3_funct_2(X82,X80,X81)
        | ~ m1_subset_1(X82,k1_zfmisc_1(k2_zfmisc_1(X80,X81))) )
      & ( v2_funct_1(X82)
        | ~ v1_funct_1(X82)
        | ~ v3_funct_2(X82,X80,X81)
        | ~ m1_subset_1(X82,k1_zfmisc_1(k2_zfmisc_1(X80,X81))) )
      & ( v2_funct_2(X82,X81)
        | ~ v1_funct_1(X82)
        | ~ v3_funct_2(X82,X80,X81)
        | ~ m1_subset_1(X82,k1_zfmisc_1(k2_zfmisc_1(X80,X81))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_funct_2])])])).

fof(c_0_46,plain,(
    ! [X30,X31,X32,X33,X34,X35] :
      ( ~ v1_funct_1(X34)
      | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))
      | ~ v1_funct_1(X35)
      | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))
      | k1_partfun1(X30,X31,X32,X33,X34,X35) = k5_relat_1(X34,X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).

cnf(c_0_47,negated_conjecture,
    ( k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0) = esk3_0
    | ~ m1_subset_1(k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])])).

cnf(c_0_48,plain,
    ( m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X6)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_49,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_50,plain,
    ( r2_relset_1(X2,X3,X4,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_relset_1(X2,X3,X1,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_51,plain,(
    ! [X26] :
      ( v1_partfun1(k6_partfun1(X26),X26)
      & m1_subset_1(k6_partfun1(X26),k1_zfmisc_1(k2_zfmisc_1(X26,X26))) ) ),
    inference(variable_rename,[status(thm)],[dt_k6_partfun1])).

cnf(c_0_52,plain,
    ( X1 = k6_partfun1(X2)
    | k5_relat_1(X1,X3) != X3
    | k1_relat_1(X1) != X2
    | k1_relat_1(X3) != X2
    | ~ v2_funct_1(X3)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X3)
    | ~ m1_subset_1(k2_relat_1(X1),k1_zfmisc_1(X2))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X3) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(k2_relat_1(esk2_0),k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_54,negated_conjecture,
    ( k1_relat_1(esk2_0) = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_40]),c_0_43])])).

cnf(c_0_55,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_40])).

cnf(c_0_56,plain,
    ( v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v3_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_57,negated_conjecture,
    ( v3_funct_2(esk3_0,esk1_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_58,plain,
    ( k1_partfun1(X2,X3,X5,X6,X1,X4) = k5_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_59,negated_conjecture,
    ( k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_34]),c_0_40]),c_0_49]),c_0_43])])).

cnf(c_0_60,negated_conjecture,
    ( v1_funct_2(esk3_0,esk1_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_61,negated_conjecture,
    ( r2_relset_1(esk1_0,esk1_0,esk2_0,X1)
    | ~ r2_relset_1(esk1_0,esk1_0,X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(spm,[status(thm)],[c_0_50,c_0_40])).

cnf(c_0_62,plain,
    ( m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_63,negated_conjecture,
    ( ~ r2_relset_1(esk1_0,esk1_0,esk2_0,k6_partfun1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_64,negated_conjecture,
    ( k6_partfun1(esk1_0) = esk2_0
    | k5_relat_1(esk2_0,X1) != X1
    | k1_relat_1(X1) != esk1_0
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54]),c_0_55]),c_0_43])])).

cnf(c_0_65,negated_conjecture,
    ( v2_funct_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_34]),c_0_57]),c_0_49])])).

cnf(c_0_66,negated_conjecture,
    ( k5_relat_1(esk2_0,esk3_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_34]),c_0_40]),c_0_49]),c_0_43])])).

cnf(c_0_67,negated_conjecture,
    ( k1_relat_1(esk3_0) = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_60]),c_0_34]),c_0_49])])).

cnf(c_0_68,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_34])).

cnf(c_0_69,negated_conjecture,
    ( ~ r2_relset_1(esk1_0,esk1_0,k6_partfun1(esk1_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63])).

cnf(c_0_70,negated_conjecture,
    ( k6_partfun1(esk1_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_66]),c_0_67]),c_0_68]),c_0_49])])).

cnf(c_0_71,plain,
    ( r2_relset_1(X3,X4,X1,X2)
    | X1 != X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_72,negated_conjecture,
    ( ~ r2_relset_1(esk1_0,esk1_0,esk2_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_73,plain,
    ( r2_relset_1(X1,X2,X3,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(er,[status(thm)],[c_0_71])).

cnf(c_0_74,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_40])]),
    [proof]).
%------------------------------------------------------------------------------
