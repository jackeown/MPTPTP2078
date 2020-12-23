%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:03:33 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 108 expanded)
%              Number of clauses        :   27 (  37 expanded)
%              Number of leaves         :   10 (  27 expanded)
%              Depth                    :    8
%              Number of atoms          :  178 ( 625 expanded)
%              Number of equality atoms :   49 (  97 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t37_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ~ ( X2 != k1_xboole_0
          & ? [X4] :
              ( v1_funct_1(X4)
              & v1_funct_2(X4,X2,X1)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
              & r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1)) )
          & ~ v2_funct_1(X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_funct_2)).

fof(redefinition_k6_partfun1,axiom,(
    ! [X1] : k6_partfun1(X1) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(d1_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( ( X2 = k1_xboole_0
           => X1 = k1_xboole_0 )
         => ( v1_funct_2(X3,X1,X2)
          <=> X1 = k1_relset_1(X1,X2,X3) ) )
        & ( X2 = k1_xboole_0
         => ( X1 = k1_xboole_0
            | ( v1_funct_2(X3,X1,X2)
            <=> X3 = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(redefinition_r2_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_relset_1(X1,X2,X3,X4)
      <=> X3 = X4 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(t29_relset_1,axiom,(
    ! [X1] : m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(dt_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => ( v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))
        & m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(t53_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( ? [X2] :
            ( v1_relat_1(X2)
            & v1_funct_1(X2)
            & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X1)) )
       => v2_funct_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_funct_1)).

fof(redefinition_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => k1_partfun1(X1,X2,X3,X4,X5,X6) = k5_relat_1(X5,X6) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ~ ( X2 != k1_xboole_0
            & ? [X4] :
                ( v1_funct_1(X4)
                & v1_funct_2(X4,X2,X1)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                & r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1)) )
            & ~ v2_funct_1(X3) ) ) ),
    inference(assume_negation,[status(cth)],[t37_funct_2])).

fof(c_0_11,negated_conjecture,
    ( v1_funct_1(esk7_0)
    & v1_funct_2(esk7_0,esk5_0,esk6_0)
    & m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))
    & esk6_0 != k1_xboole_0
    & v1_funct_1(esk8_0)
    & v1_funct_2(esk8_0,esk6_0,esk5_0)
    & m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk5_0)))
    & r2_relset_1(esk5_0,esk5_0,k1_partfun1(esk5_0,esk6_0,esk6_0,esk5_0,esk7_0,esk8_0),k6_partfun1(esk5_0))
    & ~ v2_funct_1(esk7_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).

fof(c_0_12,plain,(
    ! [X88] : k6_partfun1(X88) = k6_relat_1(X88) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).

fof(c_0_13,plain,(
    ! [X65,X66,X67] :
      ( ~ m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(X65,X66)))
      | k1_relset_1(X65,X66,X67) = k1_relat_1(X67) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_14,plain,(
    ! [X73,X74,X75] :
      ( ( ~ v1_funct_2(X75,X73,X74)
        | X73 = k1_relset_1(X73,X74,X75)
        | X74 = k1_xboole_0
        | ~ m1_subset_1(X75,k1_zfmisc_1(k2_zfmisc_1(X73,X74))) )
      & ( X73 != k1_relset_1(X73,X74,X75)
        | v1_funct_2(X75,X73,X74)
        | X74 = k1_xboole_0
        | ~ m1_subset_1(X75,k1_zfmisc_1(k2_zfmisc_1(X73,X74))) )
      & ( ~ v1_funct_2(X75,X73,X74)
        | X73 = k1_relset_1(X73,X74,X75)
        | X73 != k1_xboole_0
        | ~ m1_subset_1(X75,k1_zfmisc_1(k2_zfmisc_1(X73,X74))) )
      & ( X73 != k1_relset_1(X73,X74,X75)
        | v1_funct_2(X75,X73,X74)
        | X73 != k1_xboole_0
        | ~ m1_subset_1(X75,k1_zfmisc_1(k2_zfmisc_1(X73,X74))) )
      & ( ~ v1_funct_2(X75,X73,X74)
        | X75 = k1_xboole_0
        | X73 = k1_xboole_0
        | X74 != k1_xboole_0
        | ~ m1_subset_1(X75,k1_zfmisc_1(k2_zfmisc_1(X73,X74))) )
      & ( X75 != k1_xboole_0
        | v1_funct_2(X75,X73,X74)
        | X73 = k1_xboole_0
        | X74 != k1_xboole_0
        | ~ m1_subset_1(X75,k1_zfmisc_1(k2_zfmisc_1(X73,X74))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

fof(c_0_15,plain,(
    ! [X68,X69,X70,X71] :
      ( ( ~ r2_relset_1(X68,X69,X70,X71)
        | X70 = X71
        | ~ m1_subset_1(X70,k1_zfmisc_1(k2_zfmisc_1(X68,X69)))
        | ~ m1_subset_1(X71,k1_zfmisc_1(k2_zfmisc_1(X68,X69))) )
      & ( X70 != X71
        | r2_relset_1(X68,X69,X70,X71)
        | ~ m1_subset_1(X70,k1_zfmisc_1(k2_zfmisc_1(X68,X69)))
        | ~ m1_subset_1(X71,k1_zfmisc_1(k2_zfmisc_1(X68,X69))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).

cnf(c_0_16,negated_conjecture,
    ( r2_relset_1(esk5_0,esk5_0,k1_partfun1(esk5_0,esk6_0,esk6_0,esk5_0,esk7_0,esk8_0),k6_partfun1(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( k6_partfun1(X1) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_18,plain,(
    ! [X72] : m1_subset_1(k6_relat_1(X72),k1_zfmisc_1(k2_zfmisc_1(X72,X72))) ),
    inference(variable_rename,[status(thm)],[t29_relset_1])).

cnf(c_0_19,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_21,plain,(
    ! [X62,X63,X64] :
      ( ~ m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X62,X63)))
      | v1_relat_1(X64) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_22,plain,
    ( X3 = X4
    | ~ r2_relset_1(X1,X2,X3,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,negated_conjecture,
    ( r2_relset_1(esk5_0,esk5_0,k1_partfun1(esk5_0,esk6_0,esk6_0,esk5_0,esk7_0,esk8_0),k6_relat_1(esk5_0)) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_24,plain,
    ( m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_25,plain,(
    ! [X76,X77,X78,X79,X80,X81] :
      ( ( v1_funct_1(k1_partfun1(X76,X77,X78,X79,X80,X81))
        | ~ v1_funct_1(X80)
        | ~ m1_subset_1(X80,k1_zfmisc_1(k2_zfmisc_1(X76,X77)))
        | ~ v1_funct_1(X81)
        | ~ m1_subset_1(X81,k1_zfmisc_1(k2_zfmisc_1(X78,X79))) )
      & ( m1_subset_1(k1_partfun1(X76,X77,X78,X79,X80,X81),k1_zfmisc_1(k2_zfmisc_1(X76,X79)))
        | ~ v1_funct_1(X80)
        | ~ m1_subset_1(X80,k1_zfmisc_1(k2_zfmisc_1(X76,X77)))
        | ~ v1_funct_1(X81)
        | ~ m1_subset_1(X81,k1_zfmisc_1(k2_zfmisc_1(X78,X79))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_partfun1])])])).

fof(c_0_26,plain,(
    ! [X60,X61] :
      ( ~ v1_relat_1(X60)
      | ~ v1_funct_1(X60)
      | ~ v1_relat_1(X61)
      | ~ v1_funct_1(X61)
      | k5_relat_1(X60,X61) != k6_relat_1(k1_relat_1(X60))
      | v2_funct_1(X60) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t53_funct_1])])])).

cnf(c_0_27,plain,
    ( X1 = k1_relat_1(X2)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( v1_funct_2(esk7_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_30,negated_conjecture,
    ( esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_31,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_32,plain,(
    ! [X82,X83,X84,X85,X86,X87] :
      ( ~ v1_funct_1(X86)
      | ~ m1_subset_1(X86,k1_zfmisc_1(k2_zfmisc_1(X82,X83)))
      | ~ v1_funct_1(X87)
      | ~ m1_subset_1(X87,k1_zfmisc_1(k2_zfmisc_1(X84,X85)))
      | k1_partfun1(X82,X83,X84,X85,X86,X87) = k5_relat_1(X86,X87) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).

cnf(c_0_33,negated_conjecture,
    ( k1_partfun1(esk5_0,esk6_0,esk6_0,esk5_0,esk7_0,esk8_0) = k6_relat_1(esk5_0)
    | ~ m1_subset_1(k1_partfun1(esk5_0,esk6_0,esk6_0,esk5_0,esk7_0,esk8_0),k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])])).

cnf(c_0_34,plain,
    ( m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X6)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,negated_conjecture,
    ( v1_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_36,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_38,plain,
    ( v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_39,negated_conjecture,
    ( k1_relat_1(esk7_0) = esk5_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])]),c_0_30])).

cnf(c_0_40,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_29])).

cnf(c_0_41,negated_conjecture,
    ( ~ v2_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_42,plain,
    ( k1_partfun1(X2,X3,X5,X6,X1,X4) = k5_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_43,negated_conjecture,
    ( k1_partfun1(esk5_0,esk6_0,esk6_0,esk5_0,esk7_0,esk8_0) = k6_relat_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35]),c_0_36]),c_0_37]),c_0_29])])).

cnf(c_0_44,negated_conjecture,
    ( k5_relat_1(esk7_0,X1) != k6_relat_1(esk5_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_36]),c_0_40])]),c_0_41])).

cnf(c_0_45,negated_conjecture,
    ( k5_relat_1(esk7_0,esk8_0) = k6_relat_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_35]),c_0_36]),c_0_37]),c_0_29])])).

cnf(c_0_46,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_37])).

cnf(c_0_47,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_35]),c_0_46])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:38:55 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.39  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_URBAN_S0Y
% 0.19/0.39  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.39  #
% 0.19/0.39  # Preprocessing time       : 0.038 s
% 0.19/0.39  
% 0.19/0.39  # Proof found!
% 0.19/0.39  # SZS status Theorem
% 0.19/0.39  # SZS output start CNFRefutation
% 0.19/0.39  fof(t37_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>~(((X2!=k1_xboole_0&?[X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))&r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1))))&~(v2_funct_1(X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_funct_2)).
% 0.19/0.39  fof(redefinition_k6_partfun1, axiom, ![X1]:k6_partfun1(X1)=k6_relat_1(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 0.19/0.39  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.19/0.39  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 0.19/0.39  fof(redefinition_r2_relset_1, axiom, ![X1, X2, X3, X4]:((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_relset_1(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 0.19/0.39  fof(t29_relset_1, axiom, ![X1]:m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 0.19/0.39  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.19/0.39  fof(dt_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>(v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))&m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 0.19/0.39  fof(t53_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(?[X2]:((v1_relat_1(X2)&v1_funct_1(X2))&k5_relat_1(X1,X2)=k6_relat_1(k1_relat_1(X1)))=>v2_funct_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_funct_1)).
% 0.19/0.39  fof(redefinition_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>k1_partfun1(X1,X2,X3,X4,X5,X6)=k5_relat_1(X5,X6)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 0.19/0.39  fof(c_0_10, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>~(((X2!=k1_xboole_0&?[X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))&r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1))))&~(v2_funct_1(X3)))))), inference(assume_negation,[status(cth)],[t37_funct_2])).
% 0.19/0.39  fof(c_0_11, negated_conjecture, (((v1_funct_1(esk7_0)&v1_funct_2(esk7_0,esk5_0,esk6_0))&m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))))&((esk6_0!=k1_xboole_0&(((v1_funct_1(esk8_0)&v1_funct_2(esk8_0,esk6_0,esk5_0))&m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk5_0))))&r2_relset_1(esk5_0,esk5_0,k1_partfun1(esk5_0,esk6_0,esk6_0,esk5_0,esk7_0,esk8_0),k6_partfun1(esk5_0))))&~v2_funct_1(esk7_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).
% 0.19/0.39  fof(c_0_12, plain, ![X88]:k6_partfun1(X88)=k6_relat_1(X88), inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).
% 0.19/0.39  fof(c_0_13, plain, ![X65, X66, X67]:(~m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(X65,X66)))|k1_relset_1(X65,X66,X67)=k1_relat_1(X67)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.19/0.39  fof(c_0_14, plain, ![X73, X74, X75]:((((~v1_funct_2(X75,X73,X74)|X73=k1_relset_1(X73,X74,X75)|X74=k1_xboole_0|~m1_subset_1(X75,k1_zfmisc_1(k2_zfmisc_1(X73,X74))))&(X73!=k1_relset_1(X73,X74,X75)|v1_funct_2(X75,X73,X74)|X74=k1_xboole_0|~m1_subset_1(X75,k1_zfmisc_1(k2_zfmisc_1(X73,X74)))))&((~v1_funct_2(X75,X73,X74)|X73=k1_relset_1(X73,X74,X75)|X73!=k1_xboole_0|~m1_subset_1(X75,k1_zfmisc_1(k2_zfmisc_1(X73,X74))))&(X73!=k1_relset_1(X73,X74,X75)|v1_funct_2(X75,X73,X74)|X73!=k1_xboole_0|~m1_subset_1(X75,k1_zfmisc_1(k2_zfmisc_1(X73,X74))))))&((~v1_funct_2(X75,X73,X74)|X75=k1_xboole_0|X73=k1_xboole_0|X74!=k1_xboole_0|~m1_subset_1(X75,k1_zfmisc_1(k2_zfmisc_1(X73,X74))))&(X75!=k1_xboole_0|v1_funct_2(X75,X73,X74)|X73=k1_xboole_0|X74!=k1_xboole_0|~m1_subset_1(X75,k1_zfmisc_1(k2_zfmisc_1(X73,X74)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.19/0.39  fof(c_0_15, plain, ![X68, X69, X70, X71]:((~r2_relset_1(X68,X69,X70,X71)|X70=X71|(~m1_subset_1(X70,k1_zfmisc_1(k2_zfmisc_1(X68,X69)))|~m1_subset_1(X71,k1_zfmisc_1(k2_zfmisc_1(X68,X69)))))&(X70!=X71|r2_relset_1(X68,X69,X70,X71)|(~m1_subset_1(X70,k1_zfmisc_1(k2_zfmisc_1(X68,X69)))|~m1_subset_1(X71,k1_zfmisc_1(k2_zfmisc_1(X68,X69)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).
% 0.19/0.39  cnf(c_0_16, negated_conjecture, (r2_relset_1(esk5_0,esk5_0,k1_partfun1(esk5_0,esk6_0,esk6_0,esk5_0,esk7_0,esk8_0),k6_partfun1(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.39  cnf(c_0_17, plain, (k6_partfun1(X1)=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.39  fof(c_0_18, plain, ![X72]:m1_subset_1(k6_relat_1(X72),k1_zfmisc_1(k2_zfmisc_1(X72,X72))), inference(variable_rename,[status(thm)],[t29_relset_1])).
% 0.19/0.39  cnf(c_0_19, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.39  cnf(c_0_20, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.39  fof(c_0_21, plain, ![X62, X63, X64]:(~m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X62,X63)))|v1_relat_1(X64)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.19/0.39  cnf(c_0_22, plain, (X3=X4|~r2_relset_1(X1,X2,X3,X4)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.39  cnf(c_0_23, negated_conjecture, (r2_relset_1(esk5_0,esk5_0,k1_partfun1(esk5_0,esk6_0,esk6_0,esk5_0,esk7_0,esk8_0),k6_relat_1(esk5_0))), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 0.19/0.39  cnf(c_0_24, plain, (m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.39  fof(c_0_25, plain, ![X76, X77, X78, X79, X80, X81]:((v1_funct_1(k1_partfun1(X76,X77,X78,X79,X80,X81))|(~v1_funct_1(X80)|~m1_subset_1(X80,k1_zfmisc_1(k2_zfmisc_1(X76,X77)))|~v1_funct_1(X81)|~m1_subset_1(X81,k1_zfmisc_1(k2_zfmisc_1(X78,X79)))))&(m1_subset_1(k1_partfun1(X76,X77,X78,X79,X80,X81),k1_zfmisc_1(k2_zfmisc_1(X76,X79)))|(~v1_funct_1(X80)|~m1_subset_1(X80,k1_zfmisc_1(k2_zfmisc_1(X76,X77)))|~v1_funct_1(X81)|~m1_subset_1(X81,k1_zfmisc_1(k2_zfmisc_1(X78,X79)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_partfun1])])])).
% 0.19/0.39  fof(c_0_26, plain, ![X60, X61]:(~v1_relat_1(X60)|~v1_funct_1(X60)|(~v1_relat_1(X61)|~v1_funct_1(X61)|k5_relat_1(X60,X61)!=k6_relat_1(k1_relat_1(X60))|v2_funct_1(X60))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t53_funct_1])])])).
% 0.19/0.39  cnf(c_0_27, plain, (X1=k1_relat_1(X2)|X3=k1_xboole_0|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.19/0.39  cnf(c_0_28, negated_conjecture, (v1_funct_2(esk7_0,esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.39  cnf(c_0_29, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.39  cnf(c_0_30, negated_conjecture, (esk6_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.39  cnf(c_0_31, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.39  fof(c_0_32, plain, ![X82, X83, X84, X85, X86, X87]:(~v1_funct_1(X86)|~m1_subset_1(X86,k1_zfmisc_1(k2_zfmisc_1(X82,X83)))|~v1_funct_1(X87)|~m1_subset_1(X87,k1_zfmisc_1(k2_zfmisc_1(X84,X85)))|k1_partfun1(X82,X83,X84,X85,X86,X87)=k5_relat_1(X86,X87)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).
% 0.19/0.39  cnf(c_0_33, negated_conjecture, (k1_partfun1(esk5_0,esk6_0,esk6_0,esk5_0,esk7_0,esk8_0)=k6_relat_1(esk5_0)|~m1_subset_1(k1_partfun1(esk5_0,esk6_0,esk6_0,esk5_0,esk7_0,esk8_0),k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24])])).
% 0.19/0.39  cnf(c_0_34, plain, (m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X6)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.39  cnf(c_0_35, negated_conjecture, (v1_funct_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.39  cnf(c_0_36, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.39  cnf(c_0_37, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.39  cnf(c_0_38, plain, (v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|k5_relat_1(X1,X2)!=k6_relat_1(k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.39  cnf(c_0_39, negated_conjecture, (k1_relat_1(esk7_0)=esk5_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29])]), c_0_30])).
% 0.19/0.39  cnf(c_0_40, negated_conjecture, (v1_relat_1(esk7_0)), inference(spm,[status(thm)],[c_0_31, c_0_29])).
% 0.19/0.39  cnf(c_0_41, negated_conjecture, (~v2_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.39  cnf(c_0_42, plain, (k1_partfun1(X2,X3,X5,X6,X1,X4)=k5_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.39  cnf(c_0_43, negated_conjecture, (k1_partfun1(esk5_0,esk6_0,esk6_0,esk5_0,esk7_0,esk8_0)=k6_relat_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35]), c_0_36]), c_0_37]), c_0_29])])).
% 0.19/0.39  cnf(c_0_44, negated_conjecture, (k5_relat_1(esk7_0,X1)!=k6_relat_1(esk5_0)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_36]), c_0_40])]), c_0_41])).
% 0.19/0.39  cnf(c_0_45, negated_conjecture, (k5_relat_1(esk7_0,esk8_0)=k6_relat_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_35]), c_0_36]), c_0_37]), c_0_29])])).
% 0.19/0.39  cnf(c_0_46, negated_conjecture, (v1_relat_1(esk8_0)), inference(spm,[status(thm)],[c_0_31, c_0_37])).
% 0.19/0.39  cnf(c_0_47, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_35]), c_0_46])]), ['proof']).
% 0.19/0.39  # SZS output end CNFRefutation
% 0.19/0.39  # Proof object total steps             : 48
% 0.19/0.39  # Proof object clause steps            : 27
% 0.19/0.39  # Proof object formula steps           : 21
% 0.19/0.39  # Proof object conjectures             : 20
% 0.19/0.39  # Proof object clause conjectures      : 17
% 0.19/0.39  # Proof object formula conjectures     : 3
% 0.19/0.39  # Proof object initial clauses used    : 17
% 0.19/0.39  # Proof object initial formulas used   : 10
% 0.19/0.39  # Proof object generating inferences   : 9
% 0.19/0.39  # Proof object simplifying inferences  : 23
% 0.19/0.39  # Training examples: 0 positive, 0 negative
% 0.19/0.39  # Parsed axioms                        : 32
% 0.19/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.39  # Initial clauses                      : 56
% 0.19/0.39  # Removed in clause preprocessing      : 9
% 0.19/0.39  # Initial clauses in saturation        : 47
% 0.19/0.39  # Processed clauses                    : 88
% 0.19/0.39  # ...of these trivial                  : 1
% 0.19/0.39  # ...subsumed                          : 4
% 0.19/0.39  # ...remaining for further processing  : 83
% 0.19/0.39  # Other redundant clauses eliminated   : 3
% 0.19/0.39  # Clauses deleted for lack of memory   : 0
% 0.19/0.39  # Backward-subsumed                    : 0
% 0.19/0.39  # Backward-rewritten                   : 5
% 0.19/0.39  # Generated clauses                    : 113
% 0.19/0.39  # ...of the previous two non-trivial   : 87
% 0.19/0.39  # Contextual simplify-reflections      : 0
% 0.19/0.39  # Paramodulations                      : 108
% 0.19/0.39  # Factorizations                       : 0
% 0.19/0.39  # Equation resolutions                 : 5
% 0.19/0.39  # Propositional unsat checks           : 0
% 0.19/0.39  #    Propositional check models        : 0
% 0.19/0.39  #    Propositional check unsatisfiable : 0
% 0.19/0.39  #    Propositional clauses             : 0
% 0.19/0.39  #    Propositional clauses after purity: 0
% 0.19/0.39  #    Propositional unsat core size     : 0
% 0.19/0.39  #    Propositional preprocessing time  : 0.000
% 0.19/0.39  #    Propositional encoding time       : 0.000
% 0.19/0.39  #    Propositional solver time         : 0.000
% 0.19/0.39  #    Success case prop preproc time    : 0.000
% 0.19/0.39  #    Success case prop encoding time   : 0.000
% 0.19/0.39  #    Success case prop solver time     : 0.000
% 0.19/0.39  # Current number of processed clauses  : 77
% 0.19/0.39  #    Positive orientable unit clauses  : 28
% 0.19/0.39  #    Positive unorientable unit clauses: 0
% 0.19/0.39  #    Negative unit clauses             : 4
% 0.19/0.39  #    Non-unit-clauses                  : 45
% 0.19/0.39  # Current number of unprocessed clauses: 45
% 0.19/0.39  # ...number of literals in the above   : 149
% 0.19/0.39  # Current number of archived formulas  : 0
% 0.19/0.39  # Current number of archived clauses   : 14
% 0.19/0.39  # Clause-clause subsumption calls (NU) : 398
% 0.19/0.39  # Rec. Clause-clause subsumption calls : 83
% 0.19/0.39  # Non-unit clause-clause subsumptions  : 0
% 0.19/0.39  # Unit Clause-clause subsumption calls : 29
% 0.19/0.39  # Rewrite failures with RHS unbound    : 0
% 0.19/0.39  # BW rewrite match attempts            : 5
% 0.19/0.39  # BW rewrite match successes           : 3
% 0.19/0.39  # Condensation attempts                : 0
% 0.19/0.39  # Condensation successes               : 0
% 0.19/0.39  # Termbank termtop insertions          : 5744
% 0.19/0.39  
% 0.19/0.39  # -------------------------------------------------
% 0.19/0.39  # User time                : 0.042 s
% 0.19/0.39  # System time              : 0.006 s
% 0.19/0.39  # Total time               : 0.048 s
% 0.19/0.39  # Maximum resident set size: 1620 pages
%------------------------------------------------------------------------------
