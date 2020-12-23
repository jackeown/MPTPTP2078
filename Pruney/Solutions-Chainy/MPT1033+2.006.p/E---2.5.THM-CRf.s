%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:06:55 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  122 (1404 expanded)
%              Number of clauses        :   85 ( 532 expanded)
%              Number of leaves         :   18 ( 336 expanded)
%              Depth                    :   20
%              Number of atoms          :  372 (8461 expanded)
%              Number of equality atoms :   89 (1573 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t142_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_funct_2(X4,X1,X2)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
         => ( r1_partfun1(X3,X4)
           => ( ( X2 = k1_xboole_0
                & X1 != k1_xboole_0 )
              | r2_relset_1(X1,X2,X3,X4) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_2)).

fof(t148_partfun1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
         => ( ( v1_partfun1(X3,X1)
              & v1_partfun1(X4,X1)
              & r1_partfun1(X3,X4) )
           => X3 = X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_partfun1)).

fof(cc5_funct_2,axiom,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
         => ( ( v1_funct_1(X3)
              & v1_funct_2(X3,X1,X2) )
           => ( v1_funct_1(X3)
              & v1_partfun1(X3,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(reflexivity_r2_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => r2_relset_1(X1,X2,X3,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(d5_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( X2 = k2_relat_1(X1)
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                  & X3 = k1_funct_1(X1,X4) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(t9_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ( ( k1_relat_1(X1) = k1_relat_1(X2)
              & ! [X3] :
                  ( r2_hidden(X3,k1_relat_1(X1))
                 => k1_funct_1(X1,X3) = k1_funct_1(X2,X3) ) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(fc3_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v1_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ! [X4] :
            ( ( v1_funct_1(X4)
              & v1_funct_2(X4,X1,X2)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
           => ( r1_partfun1(X3,X4)
             => ( ( X2 = k1_xboole_0
                  & X1 != k1_xboole_0 )
                | r2_relset_1(X1,X2,X3,X4) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t142_funct_2])).

fof(c_0_19,plain,(
    ! [X51,X52,X53,X54] :
      ( ~ v1_funct_1(X53)
      | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))
      | ~ v1_funct_1(X54)
      | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))
      | ~ v1_partfun1(X53,X51)
      | ~ v1_partfun1(X54,X51)
      | ~ r1_partfun1(X53,X54)
      | X53 = X54 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_partfun1])])])).

fof(c_0_20,negated_conjecture,
    ( v1_funct_1(esk8_0)
    & v1_funct_2(esk8_0,esk6_0,esk7_0)
    & m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0)))
    & v1_funct_1(esk9_0)
    & v1_funct_2(esk9_0,esk6_0,esk7_0)
    & m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0)))
    & r1_partfun1(esk8_0,esk9_0)
    & ( esk7_0 != k1_xboole_0
      | esk6_0 = k1_xboole_0 )
    & ~ r2_relset_1(esk6_0,esk7_0,esk8_0,esk9_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).

cnf(c_0_21,plain,
    ( X1 = X4
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_partfun1(X1,X2)
    | ~ v1_partfun1(X4,X2)
    | ~ r1_partfun1(X1,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_23,negated_conjecture,
    ( v1_funct_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_24,plain,(
    ! [X48,X49,X50] :
      ( ( v1_funct_1(X50)
        | ~ v1_funct_1(X50)
        | ~ v1_funct_2(X50,X48,X49)
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49)))
        | v1_xboole_0(X49) )
      & ( v1_partfun1(X50,X48)
        | ~ v1_funct_1(X50)
        | ~ v1_funct_2(X50,X48,X49)
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49)))
        | v1_xboole_0(X49) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).

cnf(c_0_25,negated_conjecture,
    ( X1 = esk9_0
    | ~ r1_partfun1(X1,esk9_0)
    | ~ v1_partfun1(esk9_0,esk6_0)
    | ~ v1_partfun1(X1,esk6_0)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])])).

cnf(c_0_26,negated_conjecture,
    ( r1_partfun1(esk8_0,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( v1_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( v1_partfun1(X1,X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( v1_funct_2(esk9_0,esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,negated_conjecture,
    ( v1_funct_2(esk8_0,esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_32,plain,(
    ! [X41,X42,X43] :
      ( ( v4_relat_1(X43,X41)
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42))) )
      & ( v5_relat_1(X43,X42)
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_33,plain,(
    ! [X38,X39,X40] :
      ( ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))
      | v1_relat_1(X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_34,plain,(
    ! [X5] :
      ( ~ v1_xboole_0(X5)
      | X5 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_35,negated_conjecture,
    ( esk9_0 = esk8_0
    | ~ v1_partfun1(esk9_0,esk6_0)
    | ~ v1_partfun1(esk8_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_28])])).

cnf(c_0_36,negated_conjecture,
    ( v1_partfun1(esk9_0,esk6_0)
    | v1_xboole_0(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_22]),c_0_30]),c_0_23])])).

cnf(c_0_37,negated_conjecture,
    ( v1_partfun1(esk8_0,esk6_0)
    | v1_xboole_0(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_28]),c_0_31]),c_0_27])])).

fof(c_0_38,plain,(
    ! [X19,X20] :
      ( ( ~ v5_relat_1(X20,X19)
        | r1_tarski(k2_relat_1(X20),X19)
        | ~ v1_relat_1(X20) )
      & ( ~ r1_tarski(k2_relat_1(X20),X19)
        | v5_relat_1(X20,X19)
        | ~ v1_relat_1(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

cnf(c_0_39,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,negated_conjecture,
    ( esk9_0 = esk8_0
    | v1_xboole_0(esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37])).

fof(c_0_43,plain,(
    ! [X11,X12] :
      ( ( ~ m1_subset_1(X11,k1_zfmisc_1(X12))
        | r1_tarski(X11,X12) )
      & ( ~ r1_tarski(X11,X12)
        | m1_subset_1(X11,k1_zfmisc_1(X12)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_44,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_45,negated_conjecture,
    ( v5_relat_1(esk8_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_28])).

cnf(c_0_46,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_28])).

cnf(c_0_47,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk7_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_48,negated_conjecture,
    ( esk9_0 = esk8_0
    | k1_xboole_0 = esk7_0 ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

fof(c_0_49,plain,(
    ! [X44,X45,X46,X47] :
      ( ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45)))
      | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X44,X45)))
      | r2_relset_1(X44,X45,X46,X46) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[reflexivity_r2_relset_1])])).

fof(c_0_50,plain,(
    ! [X6] : m1_subset_1(esk1_1(X6),X6) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

cnf(c_0_51,negated_conjecture,
    ( v5_relat_1(esk9_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_22])).

cnf(c_0_52,negated_conjecture,
    ( v1_relat_1(esk9_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_22])).

fof(c_0_53,plain,(
    ! [X16,X17,X18] :
      ( ~ r2_hidden(X16,X17)
      | ~ m1_subset_1(X17,k1_zfmisc_1(X18))
      | ~ v1_xboole_0(X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_54,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk8_0),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46])])).

cnf(c_0_56,negated_conjecture,
    ( ~ r2_relset_1(esk6_0,esk7_0,esk8_0,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_57,negated_conjecture,
    ( esk9_0 = esk8_0
    | esk7_0 = esk6_0 ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_58,plain,
    ( r2_relset_1(X2,X3,X1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_59,plain,
    ( m1_subset_1(esk1_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

fof(c_0_60,plain,(
    ! [X36,X37] :
      ( ~ r2_hidden(X36,X37)
      | ~ r1_tarski(X37,X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_61,plain,(
    ! [X22,X23,X24,X26,X27,X28,X30] :
      ( ( r2_hidden(esk2_3(X22,X23,X24),k1_relat_1(X22))
        | ~ r2_hidden(X24,X23)
        | X23 != k2_relat_1(X22)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) )
      & ( X24 = k1_funct_1(X22,esk2_3(X22,X23,X24))
        | ~ r2_hidden(X24,X23)
        | X23 != k2_relat_1(X22)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) )
      & ( ~ r2_hidden(X27,k1_relat_1(X22))
        | X26 != k1_funct_1(X22,X27)
        | r2_hidden(X26,X23)
        | X23 != k2_relat_1(X22)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) )
      & ( ~ r2_hidden(esk3_2(X22,X28),X28)
        | ~ r2_hidden(X30,k1_relat_1(X22))
        | esk3_2(X22,X28) != k1_funct_1(X22,X30)
        | X28 = k2_relat_1(X22)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) )
      & ( r2_hidden(esk4_2(X22,X28),k1_relat_1(X22))
        | r2_hidden(esk3_2(X22,X28),X28)
        | X28 = k2_relat_1(X22)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) )
      & ( esk3_2(X22,X28) = k1_funct_1(X22,esk4_2(X22,X28))
        | r2_hidden(esk3_2(X22,X28),X28)
        | X28 = k2_relat_1(X22)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

fof(c_0_62,plain,(
    ! [X9,X10] :
      ( ~ m1_subset_1(X9,X10)
      | v1_xboole_0(X10)
      | r2_hidden(X9,X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_63,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk9_0),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_51]),c_0_52])])).

cnf(c_0_64,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_65,negated_conjecture,
    ( m1_subset_1(k2_relat_1(esk8_0),k1_zfmisc_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_66,negated_conjecture,
    ( esk7_0 = esk6_0
    | ~ r2_relset_1(esk6_0,esk7_0,esk8_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_67,plain,
    ( r2_relset_1(X1,X2,X3,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_68,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_69,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_70,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),k1_relat_1(X1))
    | ~ r2_hidden(X3,X2)
    | X2 != k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_71,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_72,negated_conjecture,
    ( m1_subset_1(k2_relat_1(esk9_0),k1_zfmisc_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_63])).

cnf(c_0_73,negated_conjecture,
    ( ~ r2_hidden(X1,k2_relat_1(esk8_0))
    | ~ v1_xboole_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_74,negated_conjecture,
    ( esk7_0 = esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_28])])).

cnf(c_0_75,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_76,plain,
    ( r2_hidden(esk2_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_70])).

cnf(c_0_77,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_71,c_0_59])).

cnf(c_0_78,negated_conjecture,
    ( ~ r2_hidden(X1,k2_relat_1(esk9_0))
    | ~ v1_xboole_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_72])).

cnf(c_0_79,plain,
    ( r2_hidden(X3,X4)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | X4 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

fof(c_0_80,plain,(
    ! [X8] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X8)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_81,negated_conjecture,
    ( ~ r2_hidden(X1,k2_relat_1(esk8_0))
    | ~ v1_xboole_0(esk6_0) ),
    inference(rw,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_82,negated_conjecture,
    ( esk9_0 = esk8_0
    | v1_xboole_0(esk6_0) ),
    inference(rw,[status(thm)],[c_0_42,c_0_74])).

fof(c_0_83,plain,(
    ! [X33,X34] :
      ( ( r2_hidden(esk5_2(X33,X34),k1_relat_1(X33))
        | k1_relat_1(X33) != k1_relat_1(X34)
        | X33 = X34
        | ~ v1_relat_1(X34)
        | ~ v1_funct_1(X34)
        | ~ v1_relat_1(X33)
        | ~ v1_funct_1(X33) )
      & ( k1_funct_1(X33,esk5_2(X33,X34)) != k1_funct_1(X34,esk5_2(X33,X34))
        | k1_relat_1(X33) != k1_relat_1(X34)
        | X33 = X34
        | ~ v1_relat_1(X34)
        | ~ v1_funct_1(X34)
        | ~ v1_relat_1(X33)
        | ~ v1_funct_1(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_funct_1])])])])])).

cnf(c_0_84,plain,
    ( ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1))
    | ~ m1_subset_1(k1_relat_1(X1),k1_zfmisc_1(esk2_3(X1,k2_relat_1(X1),X2))) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_85,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_77])).

fof(c_0_86,plain,(
    ! [X21] :
      ( k1_relat_1(k6_relat_1(X21)) = X21
      & k2_relat_1(k6_relat_1(X21)) = X21 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_87,plain,(
    ! [X32] :
      ( v1_relat_1(k6_relat_1(X32))
      & v1_funct_1(k6_relat_1(X32)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

cnf(c_0_88,negated_conjecture,
    ( esk9_0 = esk8_0
    | ~ r2_hidden(X1,k2_relat_1(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_78,c_0_42])).

cnf(c_0_89,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_79])])).

cnf(c_0_90,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_91,negated_conjecture,
    ( esk9_0 = esk8_0
    | ~ r2_hidden(X1,k2_relat_1(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_92,plain,
    ( r2_hidden(esk5_2(X1,X2),k1_relat_1(X1))
    | X1 = X2
    | k1_relat_1(X1) != k1_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_93,plain,
    ( k2_relat_1(X1) = k1_xboole_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(k1_relat_1(X1),k1_zfmisc_1(esk2_3(X1,k2_relat_1(X1),esk1_1(k2_relat_1(X1))))) ),
    inference(spm,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_94,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_86])).

cnf(c_0_95,plain,
    ( v1_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_87])).

cnf(c_0_96,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_87])).

cnf(c_0_97,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_86])).

cnf(c_0_98,negated_conjecture,
    ( esk9_0 = esk8_0
    | ~ r2_hidden(X1,k1_relat_1(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_23]),c_0_52])])).

cnf(c_0_99,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_90,c_0_85])).

cnf(c_0_100,negated_conjecture,
    ( esk9_0 = esk8_0
    | ~ r2_hidden(X1,k1_relat_1(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_89]),c_0_27]),c_0_46])])).

cnf(c_0_101,negated_conjecture,
    ( X1 = esk9_0
    | r2_hidden(esk5_2(X1,esk9_0),k1_relat_1(X1))
    | k1_relat_1(X1) != k1_relat_1(esk9_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_23]),c_0_52])])).

cnf(c_0_102,plain,
    ( X1 = k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk2_3(k6_relat_1(X1),X1,esk1_1(X1)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_95]),c_0_96]),c_0_97])])).

cnf(c_0_103,negated_conjecture,
    ( esk9_0 = esk8_0
    | m1_subset_1(k1_relat_1(esk9_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_98,c_0_99])).

cnf(c_0_104,negated_conjecture,
    ( X1 = esk8_0
    | r2_hidden(esk5_2(X1,esk8_0),k1_relat_1(X1))
    | k1_relat_1(X1) != k1_relat_1(esk8_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_27]),c_0_46])])).

cnf(c_0_105,negated_conjecture,
    ( esk9_0 = esk8_0
    | m1_subset_1(k1_relat_1(esk8_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_100,c_0_99])).

cnf(c_0_106,negated_conjecture,
    ( k6_relat_1(k1_relat_1(esk9_0)) = esk9_0
    | r2_hidden(esk5_2(k6_relat_1(k1_relat_1(esk9_0)),esk9_0),k1_relat_1(esk9_0)) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_97]),c_0_95]),c_0_96])])])).

cnf(c_0_107,negated_conjecture,
    ( k1_xboole_0 = esk6_0
    | esk9_0 = esk8_0 ),
    inference(rw,[status(thm)],[c_0_48,c_0_74])).

cnf(c_0_108,negated_conjecture,
    ( k1_xboole_0 = k1_relat_1(esk9_0)
    | esk9_0 = esk8_0 ),
    inference(spm,[status(thm)],[c_0_102,c_0_103])).

cnf(c_0_109,negated_conjecture,
    ( k6_relat_1(k1_relat_1(esk8_0)) = esk8_0
    | r2_hidden(esk5_2(k6_relat_1(k1_relat_1(esk8_0)),esk8_0),k1_relat_1(esk8_0)) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_97]),c_0_95]),c_0_96])])])).

cnf(c_0_110,negated_conjecture,
    ( k1_xboole_0 = k1_relat_1(esk8_0)
    | esk9_0 = esk8_0 ),
    inference(spm,[status(thm)],[c_0_102,c_0_105])).

cnf(c_0_111,negated_conjecture,
    ( k6_relat_1(k1_relat_1(esk9_0)) = esk9_0
    | esk9_0 = esk8_0 ),
    inference(spm,[status(thm)],[c_0_98,c_0_106])).

cnf(c_0_112,negated_conjecture,
    ( k1_relat_1(esk9_0) = esk6_0
    | esk9_0 = esk8_0 ),
    inference(spm,[status(thm)],[c_0_107,c_0_108])).

cnf(c_0_113,negated_conjecture,
    ( k6_relat_1(k1_relat_1(esk8_0)) = esk8_0
    | esk9_0 = esk8_0 ),
    inference(spm,[status(thm)],[c_0_100,c_0_109])).

cnf(c_0_114,negated_conjecture,
    ( k1_relat_1(esk8_0) = esk6_0
    | esk9_0 = esk8_0 ),
    inference(spm,[status(thm)],[c_0_107,c_0_110])).

cnf(c_0_115,negated_conjecture,
    ( k6_relat_1(esk6_0) = esk9_0
    | esk9_0 = esk8_0 ),
    inference(spm,[status(thm)],[c_0_111,c_0_112])).

cnf(c_0_116,negated_conjecture,
    ( k6_relat_1(esk6_0) = esk8_0
    | esk9_0 = esk8_0 ),
    inference(spm,[status(thm)],[c_0_113,c_0_114])).

cnf(c_0_117,negated_conjecture,
    ( ~ r2_relset_1(esk6_0,esk6_0,esk8_0,esk9_0) ),
    inference(rw,[status(thm)],[c_0_56,c_0_74])).

cnf(c_0_118,negated_conjecture,
    ( esk9_0 = esk8_0 ),
    inference(spm,[status(thm)],[c_0_115,c_0_116])).

cnf(c_0_119,negated_conjecture,
    ( ~ r2_relset_1(esk6_0,esk6_0,esk8_0,esk8_0) ),
    inference(rw,[status(thm)],[c_0_117,c_0_118])).

cnf(c_0_120,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk6_0))) ),
    inference(rw,[status(thm)],[c_0_28,c_0_74])).

cnf(c_0_121,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_67]),c_0_120])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:34:14 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.48  # AutoSched0-Mode selected heuristic G_E___208_B07____S_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.48  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.48  #
% 0.19/0.48  # Preprocessing time       : 0.029 s
% 0.19/0.48  # Presaturation interreduction done
% 0.19/0.48  
% 0.19/0.48  # Proof found!
% 0.19/0.48  # SZS status Theorem
% 0.19/0.48  # SZS output start CNFRefutation
% 0.19/0.48  fof(t142_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_partfun1(X3,X4)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|r2_relset_1(X1,X2,X3,X4))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_funct_2)).
% 0.19/0.48  fof(t148_partfun1, axiom, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:((v1_funct_1(X4)&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(((v1_partfun1(X3,X1)&v1_partfun1(X4,X1))&r1_partfun1(X3,X4))=>X3=X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_partfun1)).
% 0.19/0.48  fof(cc5_funct_2, axiom, ![X1, X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))=>(v1_funct_1(X3)&v1_partfun1(X3,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 0.19/0.48  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.19/0.48  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.19/0.48  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.19/0.48  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 0.19/0.48  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.48  fof(reflexivity_r2_relset_1, axiom, ![X1, X2, X3, X4]:((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>r2_relset_1(X1,X2,X3,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 0.19/0.48  fof(existence_m1_subset_1, axiom, ![X1]:?[X2]:m1_subset_1(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 0.19/0.48  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 0.19/0.48  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.19/0.48  fof(d5_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 0.19/0.48  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 0.19/0.48  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 0.19/0.48  fof(t9_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((k1_relat_1(X1)=k1_relat_1(X2)&![X3]:(r2_hidden(X3,k1_relat_1(X1))=>k1_funct_1(X1,X3)=k1_funct_1(X2,X3)))=>X1=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_funct_1)).
% 0.19/0.48  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 0.19/0.48  fof(fc3_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v1_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 0.19/0.48  fof(c_0_18, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_partfun1(X3,X4)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|r2_relset_1(X1,X2,X3,X4)))))), inference(assume_negation,[status(cth)],[t142_funct_2])).
% 0.19/0.48  fof(c_0_19, plain, ![X51, X52, X53, X54]:(~v1_funct_1(X53)|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))|(~v1_funct_1(X54)|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))|(~v1_partfun1(X53,X51)|~v1_partfun1(X54,X51)|~r1_partfun1(X53,X54)|X53=X54))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_partfun1])])])).
% 0.19/0.48  fof(c_0_20, negated_conjecture, (((v1_funct_1(esk8_0)&v1_funct_2(esk8_0,esk6_0,esk7_0))&m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0))))&(((v1_funct_1(esk9_0)&v1_funct_2(esk9_0,esk6_0,esk7_0))&m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0))))&(r1_partfun1(esk8_0,esk9_0)&((esk7_0!=k1_xboole_0|esk6_0=k1_xboole_0)&~r2_relset_1(esk6_0,esk7_0,esk8_0,esk9_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).
% 0.19/0.48  cnf(c_0_21, plain, (X1=X4|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_partfun1(X1,X2)|~v1_partfun1(X4,X2)|~r1_partfun1(X1,X4)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.48  cnf(c_0_22, negated_conjecture, (m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.48  cnf(c_0_23, negated_conjecture, (v1_funct_1(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.48  fof(c_0_24, plain, ![X48, X49, X50]:((v1_funct_1(X50)|(~v1_funct_1(X50)|~v1_funct_2(X50,X48,X49))|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49)))|v1_xboole_0(X49))&(v1_partfun1(X50,X48)|(~v1_funct_1(X50)|~v1_funct_2(X50,X48,X49))|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49)))|v1_xboole_0(X49))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).
% 0.19/0.48  cnf(c_0_25, negated_conjecture, (X1=esk9_0|~r1_partfun1(X1,esk9_0)|~v1_partfun1(esk9_0,esk6_0)|~v1_partfun1(X1,esk6_0)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23])])).
% 0.19/0.48  cnf(c_0_26, negated_conjecture, (r1_partfun1(esk8_0,esk9_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.48  cnf(c_0_27, negated_conjecture, (v1_funct_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.48  cnf(c_0_28, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.48  cnf(c_0_29, plain, (v1_partfun1(X1,X2)|v1_xboole_0(X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.48  cnf(c_0_30, negated_conjecture, (v1_funct_2(esk9_0,esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.48  cnf(c_0_31, negated_conjecture, (v1_funct_2(esk8_0,esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.48  fof(c_0_32, plain, ![X41, X42, X43]:((v4_relat_1(X43,X41)|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42))))&(v5_relat_1(X43,X42)|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.19/0.48  fof(c_0_33, plain, ![X38, X39, X40]:(~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))|v1_relat_1(X40)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.19/0.48  fof(c_0_34, plain, ![X5]:(~v1_xboole_0(X5)|X5=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.19/0.48  cnf(c_0_35, negated_conjecture, (esk9_0=esk8_0|~v1_partfun1(esk9_0,esk6_0)|~v1_partfun1(esk8_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27]), c_0_28])])).
% 0.19/0.48  cnf(c_0_36, negated_conjecture, (v1_partfun1(esk9_0,esk6_0)|v1_xboole_0(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_22]), c_0_30]), c_0_23])])).
% 0.19/0.48  cnf(c_0_37, negated_conjecture, (v1_partfun1(esk8_0,esk6_0)|v1_xboole_0(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_28]), c_0_31]), c_0_27])])).
% 0.19/0.48  fof(c_0_38, plain, ![X19, X20]:((~v5_relat_1(X20,X19)|r1_tarski(k2_relat_1(X20),X19)|~v1_relat_1(X20))&(~r1_tarski(k2_relat_1(X20),X19)|v5_relat_1(X20,X19)|~v1_relat_1(X20))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 0.19/0.48  cnf(c_0_39, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.48  cnf(c_0_40, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.48  cnf(c_0_41, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.48  cnf(c_0_42, negated_conjecture, (esk9_0=esk8_0|v1_xboole_0(esk7_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37])).
% 0.19/0.48  fof(c_0_43, plain, ![X11, X12]:((~m1_subset_1(X11,k1_zfmisc_1(X12))|r1_tarski(X11,X12))&(~r1_tarski(X11,X12)|m1_subset_1(X11,k1_zfmisc_1(X12)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.48  cnf(c_0_44, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.48  cnf(c_0_45, negated_conjecture, (v5_relat_1(esk8_0,esk7_0)), inference(spm,[status(thm)],[c_0_39, c_0_28])).
% 0.19/0.48  cnf(c_0_46, negated_conjecture, (v1_relat_1(esk8_0)), inference(spm,[status(thm)],[c_0_40, c_0_28])).
% 0.19/0.48  cnf(c_0_47, negated_conjecture, (esk6_0=k1_xboole_0|esk7_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.48  cnf(c_0_48, negated_conjecture, (esk9_0=esk8_0|k1_xboole_0=esk7_0), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.19/0.48  fof(c_0_49, plain, ![X44, X45, X46, X47]:(~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45)))|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X44,X45)))|r2_relset_1(X44,X45,X46,X46)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[reflexivity_r2_relset_1])])).
% 0.19/0.48  fof(c_0_50, plain, ![X6]:m1_subset_1(esk1_1(X6),X6), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).
% 0.19/0.48  cnf(c_0_51, negated_conjecture, (v5_relat_1(esk9_0,esk7_0)), inference(spm,[status(thm)],[c_0_39, c_0_22])).
% 0.19/0.48  cnf(c_0_52, negated_conjecture, (v1_relat_1(esk9_0)), inference(spm,[status(thm)],[c_0_40, c_0_22])).
% 0.19/0.48  fof(c_0_53, plain, ![X16, X17, X18]:(~r2_hidden(X16,X17)|~m1_subset_1(X17,k1_zfmisc_1(X18))|~v1_xboole_0(X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.19/0.48  cnf(c_0_54, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.48  cnf(c_0_55, negated_conjecture, (r1_tarski(k2_relat_1(esk8_0),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46])])).
% 0.19/0.48  cnf(c_0_56, negated_conjecture, (~r2_relset_1(esk6_0,esk7_0,esk8_0,esk9_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.48  cnf(c_0_57, negated_conjecture, (esk9_0=esk8_0|esk7_0=esk6_0), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.19/0.48  cnf(c_0_58, plain, (r2_relset_1(X2,X3,X1,X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.19/0.48  cnf(c_0_59, plain, (m1_subset_1(esk1_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.19/0.48  fof(c_0_60, plain, ![X36, X37]:(~r2_hidden(X36,X37)|~r1_tarski(X37,X36)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.19/0.48  fof(c_0_61, plain, ![X22, X23, X24, X26, X27, X28, X30]:((((r2_hidden(esk2_3(X22,X23,X24),k1_relat_1(X22))|~r2_hidden(X24,X23)|X23!=k2_relat_1(X22)|(~v1_relat_1(X22)|~v1_funct_1(X22)))&(X24=k1_funct_1(X22,esk2_3(X22,X23,X24))|~r2_hidden(X24,X23)|X23!=k2_relat_1(X22)|(~v1_relat_1(X22)|~v1_funct_1(X22))))&(~r2_hidden(X27,k1_relat_1(X22))|X26!=k1_funct_1(X22,X27)|r2_hidden(X26,X23)|X23!=k2_relat_1(X22)|(~v1_relat_1(X22)|~v1_funct_1(X22))))&((~r2_hidden(esk3_2(X22,X28),X28)|(~r2_hidden(X30,k1_relat_1(X22))|esk3_2(X22,X28)!=k1_funct_1(X22,X30))|X28=k2_relat_1(X22)|(~v1_relat_1(X22)|~v1_funct_1(X22)))&((r2_hidden(esk4_2(X22,X28),k1_relat_1(X22))|r2_hidden(esk3_2(X22,X28),X28)|X28=k2_relat_1(X22)|(~v1_relat_1(X22)|~v1_funct_1(X22)))&(esk3_2(X22,X28)=k1_funct_1(X22,esk4_2(X22,X28))|r2_hidden(esk3_2(X22,X28),X28)|X28=k2_relat_1(X22)|(~v1_relat_1(X22)|~v1_funct_1(X22)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).
% 0.19/0.48  fof(c_0_62, plain, ![X9, X10]:(~m1_subset_1(X9,X10)|(v1_xboole_0(X10)|r2_hidden(X9,X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.19/0.48  cnf(c_0_63, negated_conjecture, (r1_tarski(k2_relat_1(esk9_0),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_51]), c_0_52])])).
% 0.19/0.48  cnf(c_0_64, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.19/0.48  cnf(c_0_65, negated_conjecture, (m1_subset_1(k2_relat_1(esk8_0),k1_zfmisc_1(esk7_0))), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.19/0.48  cnf(c_0_66, negated_conjecture, (esk7_0=esk6_0|~r2_relset_1(esk6_0,esk7_0,esk8_0,esk8_0)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.19/0.48  cnf(c_0_67, plain, (r2_relset_1(X1,X2,X3,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.19/0.48  cnf(c_0_68, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.19/0.48  cnf(c_0_69, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.48  cnf(c_0_70, plain, (r2_hidden(esk2_3(X1,X2,X3),k1_relat_1(X1))|~r2_hidden(X3,X2)|X2!=k2_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.19/0.48  cnf(c_0_71, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.19/0.48  cnf(c_0_72, negated_conjecture, (m1_subset_1(k2_relat_1(esk9_0),k1_zfmisc_1(esk7_0))), inference(spm,[status(thm)],[c_0_54, c_0_63])).
% 0.19/0.48  cnf(c_0_73, negated_conjecture, (~r2_hidden(X1,k2_relat_1(esk8_0))|~v1_xboole_0(esk7_0)), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.19/0.48  cnf(c_0_74, negated_conjecture, (esk7_0=esk6_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_28])])).
% 0.19/0.48  cnf(c_0_75, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.19/0.48  cnf(c_0_76, plain, (r2_hidden(esk2_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_70])).
% 0.19/0.48  cnf(c_0_77, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_71, c_0_59])).
% 0.19/0.48  cnf(c_0_78, negated_conjecture, (~r2_hidden(X1,k2_relat_1(esk9_0))|~v1_xboole_0(esk7_0)), inference(spm,[status(thm)],[c_0_64, c_0_72])).
% 0.19/0.48  cnf(c_0_79, plain, (r2_hidden(X3,X4)|~r2_hidden(X1,k1_relat_1(X2))|X3!=k1_funct_1(X2,X1)|X4!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.19/0.48  fof(c_0_80, plain, ![X8]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X8)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.19/0.48  cnf(c_0_81, negated_conjecture, (~r2_hidden(X1,k2_relat_1(esk8_0))|~v1_xboole_0(esk6_0)), inference(rw,[status(thm)],[c_0_73, c_0_74])).
% 0.19/0.48  cnf(c_0_82, negated_conjecture, (esk9_0=esk8_0|v1_xboole_0(esk6_0)), inference(rw,[status(thm)],[c_0_42, c_0_74])).
% 0.19/0.48  fof(c_0_83, plain, ![X33, X34]:((r2_hidden(esk5_2(X33,X34),k1_relat_1(X33))|k1_relat_1(X33)!=k1_relat_1(X34)|X33=X34|(~v1_relat_1(X34)|~v1_funct_1(X34))|(~v1_relat_1(X33)|~v1_funct_1(X33)))&(k1_funct_1(X33,esk5_2(X33,X34))!=k1_funct_1(X34,esk5_2(X33,X34))|k1_relat_1(X33)!=k1_relat_1(X34)|X33=X34|(~v1_relat_1(X34)|~v1_funct_1(X34))|(~v1_relat_1(X33)|~v1_funct_1(X33)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_funct_1])])])])])).
% 0.19/0.48  cnf(c_0_84, plain, (~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))|~m1_subset_1(k1_relat_1(X1),k1_zfmisc_1(esk2_3(X1,k2_relat_1(X1),X2)))), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 0.19/0.48  cnf(c_0_85, plain, (X1=k1_xboole_0|r2_hidden(esk1_1(X1),X1)), inference(spm,[status(thm)],[c_0_41, c_0_77])).
% 0.19/0.48  fof(c_0_86, plain, ![X21]:(k1_relat_1(k6_relat_1(X21))=X21&k2_relat_1(k6_relat_1(X21))=X21), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.19/0.48  fof(c_0_87, plain, ![X32]:(v1_relat_1(k6_relat_1(X32))&v1_funct_1(k6_relat_1(X32))), inference(variable_rename,[status(thm)],[fc3_funct_1])).
% 0.19/0.48  cnf(c_0_88, negated_conjecture, (esk9_0=esk8_0|~r2_hidden(X1,k2_relat_1(esk9_0))), inference(spm,[status(thm)],[c_0_78, c_0_42])).
% 0.19/0.48  cnf(c_0_89, plain, (r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k1_relat_1(X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_79])])).
% 0.19/0.48  cnf(c_0_90, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_80])).
% 0.19/0.48  cnf(c_0_91, negated_conjecture, (esk9_0=esk8_0|~r2_hidden(X1,k2_relat_1(esk8_0))), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 0.19/0.48  cnf(c_0_92, plain, (r2_hidden(esk5_2(X1,X2),k1_relat_1(X1))|X1=X2|k1_relat_1(X1)!=k1_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_83])).
% 0.19/0.48  cnf(c_0_93, plain, (k2_relat_1(X1)=k1_xboole_0|~v1_funct_1(X1)|~v1_relat_1(X1)|~m1_subset_1(k1_relat_1(X1),k1_zfmisc_1(esk2_3(X1,k2_relat_1(X1),esk1_1(k2_relat_1(X1)))))), inference(spm,[status(thm)],[c_0_84, c_0_85])).
% 0.19/0.48  cnf(c_0_94, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_86])).
% 0.19/0.48  cnf(c_0_95, plain, (v1_funct_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_87])).
% 0.19/0.48  cnf(c_0_96, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_87])).
% 0.19/0.48  cnf(c_0_97, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_86])).
% 0.19/0.48  cnf(c_0_98, negated_conjecture, (esk9_0=esk8_0|~r2_hidden(X1,k1_relat_1(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_89]), c_0_23]), c_0_52])])).
% 0.19/0.48  cnf(c_0_99, plain, (r2_hidden(esk1_1(X1),X1)|m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_90, c_0_85])).
% 0.19/0.48  cnf(c_0_100, negated_conjecture, (esk9_0=esk8_0|~r2_hidden(X1,k1_relat_1(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_89]), c_0_27]), c_0_46])])).
% 0.19/0.48  cnf(c_0_101, negated_conjecture, (X1=esk9_0|r2_hidden(esk5_2(X1,esk9_0),k1_relat_1(X1))|k1_relat_1(X1)!=k1_relat_1(esk9_0)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_23]), c_0_52])])).
% 0.19/0.48  cnf(c_0_102, plain, (X1=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(esk2_3(k6_relat_1(X1),X1,esk1_1(X1))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_94]), c_0_95]), c_0_96]), c_0_97])])).
% 0.19/0.48  cnf(c_0_103, negated_conjecture, (esk9_0=esk8_0|m1_subset_1(k1_relat_1(esk9_0),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_98, c_0_99])).
% 0.19/0.48  cnf(c_0_104, negated_conjecture, (X1=esk8_0|r2_hidden(esk5_2(X1,esk8_0),k1_relat_1(X1))|k1_relat_1(X1)!=k1_relat_1(esk8_0)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_27]), c_0_46])])).
% 0.19/0.48  cnf(c_0_105, negated_conjecture, (esk9_0=esk8_0|m1_subset_1(k1_relat_1(esk8_0),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_100, c_0_99])).
% 0.19/0.48  cnf(c_0_106, negated_conjecture, (k6_relat_1(k1_relat_1(esk9_0))=esk9_0|r2_hidden(esk5_2(k6_relat_1(k1_relat_1(esk9_0)),esk9_0),k1_relat_1(esk9_0))), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_97]), c_0_95]), c_0_96])])])).
% 0.19/0.48  cnf(c_0_107, negated_conjecture, (k1_xboole_0=esk6_0|esk9_0=esk8_0), inference(rw,[status(thm)],[c_0_48, c_0_74])).
% 0.19/0.48  cnf(c_0_108, negated_conjecture, (k1_xboole_0=k1_relat_1(esk9_0)|esk9_0=esk8_0), inference(spm,[status(thm)],[c_0_102, c_0_103])).
% 0.19/0.48  cnf(c_0_109, negated_conjecture, (k6_relat_1(k1_relat_1(esk8_0))=esk8_0|r2_hidden(esk5_2(k6_relat_1(k1_relat_1(esk8_0)),esk8_0),k1_relat_1(esk8_0))), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_97]), c_0_95]), c_0_96])])])).
% 0.19/0.48  cnf(c_0_110, negated_conjecture, (k1_xboole_0=k1_relat_1(esk8_0)|esk9_0=esk8_0), inference(spm,[status(thm)],[c_0_102, c_0_105])).
% 0.19/0.48  cnf(c_0_111, negated_conjecture, (k6_relat_1(k1_relat_1(esk9_0))=esk9_0|esk9_0=esk8_0), inference(spm,[status(thm)],[c_0_98, c_0_106])).
% 0.19/0.48  cnf(c_0_112, negated_conjecture, (k1_relat_1(esk9_0)=esk6_0|esk9_0=esk8_0), inference(spm,[status(thm)],[c_0_107, c_0_108])).
% 0.19/0.48  cnf(c_0_113, negated_conjecture, (k6_relat_1(k1_relat_1(esk8_0))=esk8_0|esk9_0=esk8_0), inference(spm,[status(thm)],[c_0_100, c_0_109])).
% 0.19/0.48  cnf(c_0_114, negated_conjecture, (k1_relat_1(esk8_0)=esk6_0|esk9_0=esk8_0), inference(spm,[status(thm)],[c_0_107, c_0_110])).
% 0.19/0.48  cnf(c_0_115, negated_conjecture, (k6_relat_1(esk6_0)=esk9_0|esk9_0=esk8_0), inference(spm,[status(thm)],[c_0_111, c_0_112])).
% 0.19/0.48  cnf(c_0_116, negated_conjecture, (k6_relat_1(esk6_0)=esk8_0|esk9_0=esk8_0), inference(spm,[status(thm)],[c_0_113, c_0_114])).
% 0.19/0.48  cnf(c_0_117, negated_conjecture, (~r2_relset_1(esk6_0,esk6_0,esk8_0,esk9_0)), inference(rw,[status(thm)],[c_0_56, c_0_74])).
% 0.19/0.48  cnf(c_0_118, negated_conjecture, (esk9_0=esk8_0), inference(spm,[status(thm)],[c_0_115, c_0_116])).
% 0.19/0.48  cnf(c_0_119, negated_conjecture, (~r2_relset_1(esk6_0,esk6_0,esk8_0,esk8_0)), inference(rw,[status(thm)],[c_0_117, c_0_118])).
% 0.19/0.48  cnf(c_0_120, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk6_0)))), inference(rw,[status(thm)],[c_0_28, c_0_74])).
% 0.19/0.48  cnf(c_0_121, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119, c_0_67]), c_0_120])]), ['proof']).
% 0.19/0.48  # SZS output end CNFRefutation
% 0.19/0.48  # Proof object total steps             : 122
% 0.19/0.48  # Proof object clause steps            : 85
% 0.19/0.48  # Proof object formula steps           : 37
% 0.19/0.48  # Proof object conjectures             : 57
% 0.19/0.48  # Proof object clause conjectures      : 54
% 0.19/0.48  # Proof object formula conjectures     : 3
% 0.19/0.48  # Proof object initial clauses used    : 30
% 0.19/0.48  # Proof object initial formulas used   : 18
% 0.19/0.48  # Proof object generating inferences   : 47
% 0.19/0.48  # Proof object simplifying inferences  : 51
% 0.19/0.48  # Training examples: 0 positive, 0 negative
% 0.19/0.48  # Parsed axioms                        : 19
% 0.19/0.48  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.48  # Initial clauses                      : 39
% 0.19/0.48  # Removed in clause preprocessing      : 1
% 0.19/0.48  # Initial clauses in saturation        : 38
% 0.19/0.48  # Processed clauses                    : 1181
% 0.19/0.48  # ...of these trivial                  : 3
% 0.19/0.48  # ...subsumed                          : 629
% 0.19/0.48  # ...remaining for further processing  : 549
% 0.19/0.48  # Other redundant clauses eliminated   : 55
% 0.19/0.48  # Clauses deleted for lack of memory   : 0
% 0.19/0.48  # Backward-subsumed                    : 20
% 0.19/0.48  # Backward-rewritten                   : 314
% 0.19/0.48  # Generated clauses                    : 4779
% 0.19/0.48  # ...of the previous two non-trivial   : 4805
% 0.19/0.48  # Contextual simplify-reflections      : 8
% 0.19/0.48  # Paramodulations                      : 4720
% 0.19/0.48  # Factorizations                       : 2
% 0.19/0.48  # Equation resolutions                 : 58
% 0.19/0.48  # Propositional unsat checks           : 0
% 0.19/0.48  #    Propositional check models        : 0
% 0.19/0.48  #    Propositional check unsatisfiable : 0
% 0.19/0.48  #    Propositional clauses             : 0
% 0.19/0.48  #    Propositional clauses after purity: 0
% 0.19/0.48  #    Propositional unsat core size     : 0
% 0.19/0.48  #    Propositional preprocessing time  : 0.000
% 0.19/0.48  #    Propositional encoding time       : 0.000
% 0.19/0.48  #    Propositional solver time         : 0.000
% 0.19/0.48  #    Success case prop preproc time    : 0.000
% 0.19/0.48  #    Success case prop encoding time   : 0.000
% 0.19/0.48  #    Success case prop solver time     : 0.000
% 0.19/0.48  # Current number of processed clauses  : 174
% 0.19/0.48  #    Positive orientable unit clauses  : 26
% 0.19/0.48  #    Positive unorientable unit clauses: 0
% 0.19/0.48  #    Negative unit clauses             : 4
% 0.19/0.48  #    Non-unit-clauses                  : 144
% 0.19/0.48  # Current number of unprocessed clauses: 3507
% 0.19/0.48  # ...number of literals in the above   : 13664
% 0.19/0.48  # Current number of archived formulas  : 0
% 0.19/0.48  # Current number of archived clauses   : 372
% 0.19/0.48  # Clause-clause subsumption calls (NU) : 27187
% 0.19/0.48  # Rec. Clause-clause subsumption calls : 14605
% 0.19/0.48  # Non-unit clause-clause subsumptions  : 622
% 0.19/0.48  # Unit Clause-clause subsumption calls : 785
% 0.19/0.48  # Rewrite failures with RHS unbound    : 0
% 0.19/0.48  # BW rewrite match attempts            : 3
% 0.19/0.48  # BW rewrite match successes           : 3
% 0.19/0.48  # Condensation attempts                : 0
% 0.19/0.48  # Condensation successes               : 0
% 0.19/0.48  # Termbank termtop insertions          : 64830
% 0.19/0.48  
% 0.19/0.48  # -------------------------------------------------
% 0.19/0.48  # User time                : 0.130 s
% 0.19/0.48  # System time              : 0.011 s
% 0.19/0.48  # Total time               : 0.141 s
% 0.19/0.48  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
