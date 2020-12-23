%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:02:34 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 902 expanded)
%              Number of clauses        :   74 ( 363 expanded)
%              Number of leaves         :   20 ( 229 expanded)
%              Depth                    :   23
%              Number of atoms          :  353 (3812 expanded)
%              Number of equality atoms :   97 ( 749 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t31_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( v2_funct_1(X3)
          & k2_relset_1(X1,X2,X3) = X2 )
       => ( v1_funct_1(k2_funct_1(X3))
          & v1_funct_2(k2_funct_1(X3),X2,X1)
          & m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(d9_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => k2_funct_1(X1) = k4_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(fc14_relat_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => ( v1_xboole_0(k4_relat_1(X1))
        & v1_relat_1(k4_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc14_relat_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(t152_zfmisc_1,axiom,(
    ! [X1,X2] : ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

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

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(dt_k2_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t4_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r1_tarski(k2_relat_1(X2),X1)
       => ( v1_funct_1(X2)
          & v1_funct_2(X2,k1_relat_1(X2),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

fof(t45_ordinal1,axiom,(
    ! [X1] :
      ( v1_relat_1(k1_xboole_0)
      & v5_relat_1(k1_xboole_0,X1)
      & v1_funct_1(k1_xboole_0)
      & v5_ordinal1(k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_ordinal1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(t3_funct_2,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_funct_1(X1)
        & v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(t55_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
          & k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(c_0_20,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ( ( v2_funct_1(X3)
            & k2_relset_1(X1,X2,X3) = X2 )
         => ( v1_funct_1(k2_funct_1(X3))
            & v1_funct_2(k2_funct_1(X3),X2,X1)
            & m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t31_funct_2])).

fof(c_0_21,plain,(
    ! [X41,X42,X43] :
      ( ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))
      | v1_relat_1(X43) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_22,negated_conjecture,
    ( v1_funct_1(esk7_0)
    & v1_funct_2(esk7_0,esk5_0,esk6_0)
    & m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))
    & v2_funct_1(esk7_0)
    & k2_relset_1(esk5_0,esk6_0,esk7_0) = esk6_0
    & ( ~ v1_funct_1(k2_funct_1(esk7_0))
      | ~ v1_funct_2(k2_funct_1(esk7_0),esk6_0,esk5_0)
      | ~ m1_subset_1(k2_funct_1(esk7_0),k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk5_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).

fof(c_0_23,plain,(
    ! [X37] :
      ( ~ v1_relat_1(X37)
      | ~ v1_funct_1(X37)
      | ~ v2_funct_1(X37)
      | k2_funct_1(X37) = k4_relat_1(X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_funct_1])])).

cnf(c_0_24,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_26,plain,(
    ! [X9] :
      ( ~ v1_xboole_0(X9)
      | X9 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

fof(c_0_27,plain,(
    ! [X34] :
      ( ( v1_xboole_0(k4_relat_1(X34))
        | ~ v1_xboole_0(X34) )
      & ( v1_relat_1(k4_relat_1(X34))
        | ~ v1_xboole_0(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc14_relat_1])])])).

cnf(c_0_28,negated_conjecture,
    ( ~ v1_funct_1(k2_funct_1(esk7_0))
    | ~ v1_funct_2(k2_funct_1(esk7_0),esk6_0,esk5_0)
    | ~ m1_subset_1(k2_funct_1(esk7_0),k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( k2_funct_1(X1) = k4_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( v2_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(pm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_33,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( v1_xboole_0(k4_relat_1(X1))
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_35,plain,(
    ! [X18] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X18)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_36,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(esk7_0),esk6_0,esk5_0)
    | ~ v1_funct_1(k2_funct_1(esk7_0))
    | ~ m1_subset_1(k4_relat_1(esk7_0),k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_28,c_0_29]),c_0_30]),c_0_31]),c_0_32])])).

cnf(c_0_37,plain,
    ( k4_relat_1(X1) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(pm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_38,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_39,plain,(
    ! [X13,X14] : ~ r2_hidden(X13,k2_zfmisc_1(X13,X14)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).

fof(c_0_40,plain,(
    ! [X11,X12] :
      ( ( k2_zfmisc_1(X11,X12) != k1_xboole_0
        | X11 = k1_xboole_0
        | X12 = k1_xboole_0 )
      & ( X11 != k1_xboole_0
        | k2_zfmisc_1(X11,X12) = k1_xboole_0 )
      & ( X12 != k1_xboole_0
        | k2_zfmisc_1(X11,X12) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_41,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(esk7_0),esk6_0,esk5_0)
    | ~ v1_funct_1(k2_funct_1(esk7_0))
    | ~ v1_xboole_0(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_36,c_0_37]),c_0_38])])).

fof(c_0_42,plain,(
    ! [X50,X51,X52] :
      ( ( ~ v1_funct_2(X52,X50,X51)
        | X50 = k1_relset_1(X50,X51,X52)
        | X51 = k1_xboole_0
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51))) )
      & ( X50 != k1_relset_1(X50,X51,X52)
        | v1_funct_2(X52,X50,X51)
        | X51 = k1_xboole_0
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51))) )
      & ( ~ v1_funct_2(X52,X50,X51)
        | X50 = k1_relset_1(X50,X51,X52)
        | X50 != k1_xboole_0
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51))) )
      & ( X50 != k1_relset_1(X50,X51,X52)
        | v1_funct_2(X52,X50,X51)
        | X50 != k1_xboole_0
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51))) )
      & ( ~ v1_funct_2(X52,X50,X51)
        | X52 = k1_xboole_0
        | X50 = k1_xboole_0
        | X51 != k1_xboole_0
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51))) )
      & ( X52 != k1_xboole_0
        | v1_funct_2(X52,X50,X51)
        | X50 = k1_xboole_0
        | X51 != k1_xboole_0
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_43,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_44,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_45,negated_conjecture,
    ( ~ v1_funct_2(k4_relat_1(esk7_0),esk6_0,esk5_0)
    | ~ v1_funct_1(k2_funct_1(esk7_0))
    | ~ v1_xboole_0(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_41,c_0_29]),c_0_30]),c_0_31]),c_0_32])])).

cnf(c_0_46,plain,
    ( v1_funct_2(X1,X2,X3)
    | X2 = k1_xboole_0
    | X1 != k1_xboole_0
    | X3 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

fof(c_0_47,plain,(
    ! [X15,X16,X17] :
      ( ~ m1_subset_1(X16,k1_zfmisc_1(X15))
      | ~ r2_hidden(X17,X16)
      | r2_hidden(X17,X15) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

cnf(c_0_48,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_49,plain,
    ( X1 != k1_xboole_0
    | ~ r2_hidden(X2,k1_xboole_0) ),
    inference(pm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_50,negated_conjecture,
    ( ~ v1_funct_2(k1_xboole_0,esk6_0,esk5_0)
    | ~ v1_funct_1(k2_funct_1(esk7_0))
    | ~ v1_xboole_0(esk7_0) ),
    inference(pm,[status(thm)],[c_0_45,c_0_37])).

cnf(c_0_51,plain,
    ( X1 = k1_xboole_0
    | v1_funct_2(k1_xboole_0,X1,X2)
    | X2 != k1_xboole_0 ),
    inference(pm,[status(thm)],[c_0_46,c_0_38])).

fof(c_0_52,plain,(
    ! [X38] :
      ( ( v1_relat_1(k2_funct_1(X38))
        | ~ v1_relat_1(X38)
        | ~ v1_funct_1(X38) )
      & ( v1_funct_1(k2_funct_1(X38))
        | ~ v1_relat_1(X38)
        | ~ v1_funct_1(X38) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

cnf(c_0_53,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_54,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k1_xboole_0))
    | esk5_0 != k1_xboole_0 ),
    inference(pm,[status(thm)],[c_0_25,c_0_48])).

cnf(c_0_55,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(er,[status(thm)],[c_0_49])).

fof(c_0_56,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_57,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk5_0 != k1_xboole_0
    | ~ v1_funct_1(k2_funct_1(esk7_0))
    | ~ v1_xboole_0(esk7_0) ),
    inference(pm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_58,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_59,negated_conjecture,
    ( esk5_0 != k1_xboole_0
    | ~ r2_hidden(X1,esk7_0) ),
    inference(sr,[status(thm)],[inference(pm,[status(thm)],[c_0_53,c_0_54]),c_0_55])).

cnf(c_0_60,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

fof(c_0_61,plain,(
    ! [X54,X55] :
      ( ( v1_funct_1(X55)
        | ~ r1_tarski(k2_relat_1(X55),X54)
        | ~ v1_relat_1(X55)
        | ~ v1_funct_1(X55) )
      & ( v1_funct_2(X55,k1_relat_1(X55),X54)
        | ~ r1_tarski(k2_relat_1(X55),X54)
        | ~ v1_relat_1(X55)
        | ~ v1_funct_1(X55) )
      & ( m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X55),X54)))
        | ~ r1_tarski(k2_relat_1(X55),X54)
        | ~ v1_relat_1(X55)
        | ~ v1_funct_1(X55) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_funct_2])])])).

fof(c_0_62,plain,(
    ! [X40] :
      ( v1_relat_1(k1_xboole_0)
      & v5_relat_1(k1_xboole_0,X40)
      & v1_funct_1(k1_xboole_0)
      & v5_ordinal1(k1_xboole_0) ) ),
    inference(variable_rename,[status(thm)],[t45_ordinal1])).

fof(c_0_63,plain,(
    ! [X10] : r1_tarski(k1_xboole_0,X10) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_64,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk5_0 != k1_xboole_0
    | ~ v1_xboole_0(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_57,c_0_58]),c_0_31]),c_0_32])])).

cnf(c_0_65,negated_conjecture,
    ( v1_xboole_0(esk7_0)
    | esk5_0 != k1_xboole_0 ),
    inference(pm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_66,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_67,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_68,plain,
    ( v1_funct_1(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_69,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_70,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_71,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

fof(c_0_72,plain,(
    ! [X44,X45,X46] :
      ( ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45)))
      | k1_relset_1(X44,X45,X46) = k1_relat_1(X46) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_73,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk5_0 != k1_xboole_0 ),
    inference(pm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_74,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_66,c_0_67]),c_0_68]),c_0_69]),c_0_70]),c_0_71])])).

cnf(c_0_75,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_76,negated_conjecture,
    ( esk5_0 != k1_xboole_0
    | ~ v1_funct_1(k2_funct_1(esk7_0))
    | ~ v1_xboole_0(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_50,c_0_73]),c_0_74])])).

cnf(c_0_77,plain,
    ( v1_funct_2(X3,X1,X2)
    | X2 = k1_xboole_0
    | X1 != k1_relset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_78,plain,
    ( k1_relset_1(X1,X2,k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_75,c_0_38]),c_0_67])).

cnf(c_0_79,negated_conjecture,
    ( esk5_0 != k1_xboole_0
    | ~ v1_xboole_0(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_76,c_0_58]),c_0_31]),c_0_32])])).

cnf(c_0_80,plain,
    ( X1 = k1_xboole_0
    | v1_funct_2(k1_xboole_0,X2,X1)
    | k1_xboole_0 != X2 ),
    inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_77,c_0_38]),c_0_78])).

cnf(c_0_81,negated_conjecture,
    ( esk5_0 != k1_xboole_0 ),
    inference(pm,[status(thm)],[c_0_79,c_0_65])).

cnf(c_0_82,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k1_xboole_0))
    | esk6_0 != k1_xboole_0 ),
    inference(pm,[status(thm)],[c_0_25,c_0_44])).

fof(c_0_83,plain,(
    ! [X53] :
      ( ( v1_funct_1(X53)
        | ~ v1_relat_1(X53)
        | ~ v1_funct_1(X53) )
      & ( v1_funct_2(X53,k1_relat_1(X53),k2_relat_1(X53))
        | ~ v1_relat_1(X53)
        | ~ v1_funct_1(X53) )
      & ( m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X53),k2_relat_1(X53))))
        | ~ v1_relat_1(X53)
        | ~ v1_funct_1(X53) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).

fof(c_0_84,plain,(
    ! [X39] :
      ( ( k2_relat_1(X39) = k1_relat_1(k2_funct_1(X39))
        | ~ v2_funct_1(X39)
        | ~ v1_relat_1(X39)
        | ~ v1_funct_1(X39) )
      & ( k1_relat_1(X39) = k2_relat_1(k2_funct_1(X39))
        | ~ v2_funct_1(X39)
        | ~ v1_relat_1(X39)
        | ~ v1_funct_1(X39) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).

fof(c_0_85,plain,(
    ! [X47,X48,X49] :
      ( ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))
      | k2_relset_1(X47,X48,X49) = k2_relat_1(X49) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_86,negated_conjecture,
    ( esk6_0 != k1_xboole_0
    | ~ v1_funct_1(k2_funct_1(esk7_0))
    | ~ v1_xboole_0(esk7_0) ),
    inference(sr,[status(thm)],[inference(pm,[status(thm)],[c_0_50,c_0_80]),c_0_81])).

cnf(c_0_87,negated_conjecture,
    ( esk6_0 != k1_xboole_0
    | ~ r2_hidden(X1,esk7_0) ),
    inference(sr,[status(thm)],[inference(pm,[status(thm)],[c_0_53,c_0_82]),c_0_55])).

cnf(c_0_88,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_89,plain,
    ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_90,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

cnf(c_0_91,negated_conjecture,
    ( k2_relset_1(esk5_0,esk6_0,esk7_0) = esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_92,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_93,negated_conjecture,
    ( k1_relset_1(esk5_0,esk6_0,esk7_0) = k1_relat_1(esk7_0) ),
    inference(pm,[status(thm)],[c_0_75,c_0_25])).

cnf(c_0_94,negated_conjecture,
    ( v1_funct_2(esk7_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_95,negated_conjecture,
    ( esk6_0 != k1_xboole_0
    | ~ v1_xboole_0(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_86,c_0_58]),c_0_31]),c_0_32])])).

cnf(c_0_96,negated_conjecture,
    ( v1_xboole_0(esk7_0)
    | esk6_0 != k1_xboole_0 ),
    inference(pm,[status(thm)],[c_0_87,c_0_60])).

cnf(c_0_97,plain,
    ( m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(pm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_98,negated_conjecture,
    ( k2_relat_1(esk7_0) = esk6_0 ),
    inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_90,c_0_25]),c_0_91])).

cnf(c_0_99,negated_conjecture,
    ( k1_relat_1(esk7_0) = esk5_0
    | esk6_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_92,c_0_25]),c_0_93]),c_0_94])])).

cnf(c_0_100,negated_conjecture,
    ( esk6_0 != k1_xboole_0 ),
    inference(pm,[status(thm)],[c_0_95,c_0_96])).

cnf(c_0_101,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_102,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk7_0),k1_zfmisc_1(k2_zfmisc_1(esk6_0,k2_relat_1(k2_funct_1(esk7_0)))))
    | ~ v1_funct_1(k2_funct_1(esk7_0))
    | ~ v1_relat_1(k2_funct_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_97,c_0_98]),c_0_30]),c_0_31]),c_0_32])])).

cnf(c_0_103,plain,
    ( k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_104,negated_conjecture,
    ( k1_relat_1(esk7_0) = esk5_0 ),
    inference(sr,[status(thm)],[c_0_99,c_0_100])).

cnf(c_0_105,plain,
    ( v1_funct_2(k2_funct_1(X1),k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(pm,[status(thm)],[c_0_101,c_0_89])).

cnf(c_0_106,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk7_0),k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk5_0)))
    | ~ v1_funct_1(k2_funct_1(esk7_0))
    | ~ v1_relat_1(k2_funct_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_102,c_0_103]),c_0_104]),c_0_30]),c_0_31]),c_0_32])])).

cnf(c_0_107,negated_conjecture,
    ( v1_funct_2(k2_funct_1(esk7_0),esk6_0,k2_relat_1(k2_funct_1(esk7_0)))
    | ~ v1_funct_1(k2_funct_1(esk7_0))
    | ~ v1_relat_1(k2_funct_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_105,c_0_98]),c_0_30]),c_0_31]),c_0_32])])).

cnf(c_0_108,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(esk7_0),esk6_0,esk5_0)
    | ~ v1_funct_1(k2_funct_1(esk7_0))
    | ~ v1_relat_1(k2_funct_1(esk7_0)) ),
    inference(pm,[status(thm)],[c_0_28,c_0_106])).

cnf(c_0_109,negated_conjecture,
    ( v1_funct_2(k2_funct_1(esk7_0),esk6_0,esk5_0)
    | ~ v1_funct_1(k2_funct_1(esk7_0))
    | ~ v1_relat_1(k2_funct_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_107,c_0_103]),c_0_104]),c_0_30]),c_0_31]),c_0_32])])).

cnf(c_0_110,negated_conjecture,
    ( ~ v1_funct_1(k2_funct_1(esk7_0))
    | ~ v1_relat_1(k2_funct_1(esk7_0)) ),
    inference(pm,[status(thm)],[c_0_108,c_0_109])).

cnf(c_0_111,negated_conjecture,
    ( ~ v1_relat_1(k2_funct_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_110,c_0_58]),c_0_31]),c_0_32])])).

cnf(c_0_112,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_113,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_111,c_0_112]),c_0_31]),c_0_32])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:15:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.40  # AutoSched0-Mode selected heuristic G_E___300_C01_S00
% 0.21/0.40  # and selection function NoSelection.
% 0.21/0.40  #
% 0.21/0.40  # Preprocessing time       : 0.029 s
% 0.21/0.40  
% 0.21/0.40  # Proof found!
% 0.21/0.40  # SZS status Theorem
% 0.21/0.40  # SZS output start CNFRefutation
% 0.21/0.40  fof(t31_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v2_funct_1(X3)&k2_relset_1(X1,X2,X3)=X2)=>((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),X2,X1))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 0.21/0.40  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.21/0.40  fof(d9_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>k2_funct_1(X1)=k4_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 0.21/0.40  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.21/0.40  fof(fc14_relat_1, axiom, ![X1]:(v1_xboole_0(X1)=>(v1_xboole_0(k4_relat_1(X1))&v1_relat_1(k4_relat_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc14_relat_1)).
% 0.21/0.40  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 0.21/0.40  fof(t152_zfmisc_1, axiom, ![X1, X2]:~(r2_hidden(X1,k2_zfmisc_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 0.21/0.40  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.21/0.40  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 0.21/0.40  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 0.21/0.40  fof(dt_k2_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k2_funct_1(X1))&v1_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 0.21/0.40  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.21/0.40  fof(t4_funct_2, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r1_tarski(k2_relat_1(X2),X1)=>((v1_funct_1(X2)&v1_funct_2(X2,k1_relat_1(X2),X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 0.21/0.40  fof(t45_ordinal1, axiom, ![X1]:(((v1_relat_1(k1_xboole_0)&v5_relat_1(k1_xboole_0,X1))&v1_funct_1(k1_xboole_0))&v5_ordinal1(k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_ordinal1)).
% 0.21/0.40  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.21/0.40  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 0.21/0.40  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.21/0.40  fof(t3_funct_2, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>((v1_funct_1(X1)&v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1)))&m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 0.21/0.40  fof(t55_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))&k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 0.21/0.40  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.21/0.40  fof(c_0_20, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v2_funct_1(X3)&k2_relset_1(X1,X2,X3)=X2)=>((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),X2,X1))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))))))), inference(assume_negation,[status(cth)],[t31_funct_2])).
% 0.21/0.40  fof(c_0_21, plain, ![X41, X42, X43]:(~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))|v1_relat_1(X43)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.21/0.40  fof(c_0_22, negated_conjecture, (((v1_funct_1(esk7_0)&v1_funct_2(esk7_0,esk5_0,esk6_0))&m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))))&((v2_funct_1(esk7_0)&k2_relset_1(esk5_0,esk6_0,esk7_0)=esk6_0)&(~v1_funct_1(k2_funct_1(esk7_0))|~v1_funct_2(k2_funct_1(esk7_0),esk6_0,esk5_0)|~m1_subset_1(k2_funct_1(esk7_0),k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk5_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).
% 0.21/0.40  fof(c_0_23, plain, ![X37]:(~v1_relat_1(X37)|~v1_funct_1(X37)|(~v2_funct_1(X37)|k2_funct_1(X37)=k4_relat_1(X37))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_funct_1])])).
% 0.21/0.40  cnf(c_0_24, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.40  cnf(c_0_25, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.40  fof(c_0_26, plain, ![X9]:(~v1_xboole_0(X9)|X9=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.21/0.40  fof(c_0_27, plain, ![X34]:((v1_xboole_0(k4_relat_1(X34))|~v1_xboole_0(X34))&(v1_relat_1(k4_relat_1(X34))|~v1_xboole_0(X34))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc14_relat_1])])])).
% 0.21/0.40  cnf(c_0_28, negated_conjecture, (~v1_funct_1(k2_funct_1(esk7_0))|~v1_funct_2(k2_funct_1(esk7_0),esk6_0,esk5_0)|~m1_subset_1(k2_funct_1(esk7_0),k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.40  cnf(c_0_29, plain, (k2_funct_1(X1)=k4_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.40  cnf(c_0_30, negated_conjecture, (v2_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.40  cnf(c_0_31, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.40  cnf(c_0_32, negated_conjecture, (v1_relat_1(esk7_0)), inference(pm,[status(thm)],[c_0_24, c_0_25])).
% 0.21/0.40  cnf(c_0_33, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.21/0.40  cnf(c_0_34, plain, (v1_xboole_0(k4_relat_1(X1))|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.21/0.40  fof(c_0_35, plain, ![X18]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X18)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.21/0.40  cnf(c_0_36, negated_conjecture, (~v1_funct_2(k2_funct_1(esk7_0),esk6_0,esk5_0)|~v1_funct_1(k2_funct_1(esk7_0))|~m1_subset_1(k4_relat_1(esk7_0),k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_28, c_0_29]), c_0_30]), c_0_31]), c_0_32])])).
% 0.21/0.40  cnf(c_0_37, plain, (k4_relat_1(X1)=k1_xboole_0|~v1_xboole_0(X1)), inference(pm,[status(thm)],[c_0_33, c_0_34])).
% 0.21/0.40  cnf(c_0_38, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.21/0.40  fof(c_0_39, plain, ![X13, X14]:~r2_hidden(X13,k2_zfmisc_1(X13,X14)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).
% 0.21/0.40  fof(c_0_40, plain, ![X11, X12]:((k2_zfmisc_1(X11,X12)!=k1_xboole_0|(X11=k1_xboole_0|X12=k1_xboole_0))&((X11!=k1_xboole_0|k2_zfmisc_1(X11,X12)=k1_xboole_0)&(X12!=k1_xboole_0|k2_zfmisc_1(X11,X12)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.21/0.40  cnf(c_0_41, negated_conjecture, (~v1_funct_2(k2_funct_1(esk7_0),esk6_0,esk5_0)|~v1_funct_1(k2_funct_1(esk7_0))|~v1_xboole_0(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_36, c_0_37]), c_0_38])])).
% 0.21/0.40  fof(c_0_42, plain, ![X50, X51, X52]:((((~v1_funct_2(X52,X50,X51)|X50=k1_relset_1(X50,X51,X52)|X51=k1_xboole_0|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51))))&(X50!=k1_relset_1(X50,X51,X52)|v1_funct_2(X52,X50,X51)|X51=k1_xboole_0|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51)))))&((~v1_funct_2(X52,X50,X51)|X50=k1_relset_1(X50,X51,X52)|X50!=k1_xboole_0|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51))))&(X50!=k1_relset_1(X50,X51,X52)|v1_funct_2(X52,X50,X51)|X50!=k1_xboole_0|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51))))))&((~v1_funct_2(X52,X50,X51)|X52=k1_xboole_0|X50=k1_xboole_0|X51!=k1_xboole_0|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51))))&(X52!=k1_xboole_0|v1_funct_2(X52,X50,X51)|X50=k1_xboole_0|X51!=k1_xboole_0|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.21/0.40  cnf(c_0_43, plain, (~r2_hidden(X1,k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.21/0.40  cnf(c_0_44, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.21/0.40  cnf(c_0_45, negated_conjecture, (~v1_funct_2(k4_relat_1(esk7_0),esk6_0,esk5_0)|~v1_funct_1(k2_funct_1(esk7_0))|~v1_xboole_0(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_41, c_0_29]), c_0_30]), c_0_31]), c_0_32])])).
% 0.21/0.40  cnf(c_0_46, plain, (v1_funct_2(X1,X2,X3)|X2=k1_xboole_0|X1!=k1_xboole_0|X3!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.21/0.40  fof(c_0_47, plain, ![X15, X16, X17]:(~m1_subset_1(X16,k1_zfmisc_1(X15))|(~r2_hidden(X17,X16)|r2_hidden(X17,X15))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.21/0.40  cnf(c_0_48, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.21/0.40  cnf(c_0_49, plain, (X1!=k1_xboole_0|~r2_hidden(X2,k1_xboole_0)), inference(pm,[status(thm)],[c_0_43, c_0_44])).
% 0.21/0.40  cnf(c_0_50, negated_conjecture, (~v1_funct_2(k1_xboole_0,esk6_0,esk5_0)|~v1_funct_1(k2_funct_1(esk7_0))|~v1_xboole_0(esk7_0)), inference(pm,[status(thm)],[c_0_45, c_0_37])).
% 0.21/0.40  cnf(c_0_51, plain, (X1=k1_xboole_0|v1_funct_2(k1_xboole_0,X1,X2)|X2!=k1_xboole_0), inference(pm,[status(thm)],[c_0_46, c_0_38])).
% 0.21/0.40  fof(c_0_52, plain, ![X38]:((v1_relat_1(k2_funct_1(X38))|(~v1_relat_1(X38)|~v1_funct_1(X38)))&(v1_funct_1(k2_funct_1(X38))|(~v1_relat_1(X38)|~v1_funct_1(X38)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).
% 0.21/0.40  cnf(c_0_53, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.21/0.40  cnf(c_0_54, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k1_xboole_0))|esk5_0!=k1_xboole_0), inference(pm,[status(thm)],[c_0_25, c_0_48])).
% 0.21/0.40  cnf(c_0_55, plain, (~r2_hidden(X1,k1_xboole_0)), inference(er,[status(thm)],[c_0_49])).
% 0.21/0.40  fof(c_0_56, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.21/0.40  cnf(c_0_57, negated_conjecture, (esk6_0=k1_xboole_0|esk5_0!=k1_xboole_0|~v1_funct_1(k2_funct_1(esk7_0))|~v1_xboole_0(esk7_0)), inference(pm,[status(thm)],[c_0_50, c_0_51])).
% 0.21/0.40  cnf(c_0_58, plain, (v1_funct_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.21/0.40  cnf(c_0_59, negated_conjecture, (esk5_0!=k1_xboole_0|~r2_hidden(X1,esk7_0)), inference(sr,[status(thm)],[inference(pm,[status(thm)],[c_0_53, c_0_54]), c_0_55])).
% 0.21/0.40  cnf(c_0_60, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.21/0.40  fof(c_0_61, plain, ![X54, X55]:(((v1_funct_1(X55)|~r1_tarski(k2_relat_1(X55),X54)|(~v1_relat_1(X55)|~v1_funct_1(X55)))&(v1_funct_2(X55,k1_relat_1(X55),X54)|~r1_tarski(k2_relat_1(X55),X54)|(~v1_relat_1(X55)|~v1_funct_1(X55))))&(m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X55),X54)))|~r1_tarski(k2_relat_1(X55),X54)|(~v1_relat_1(X55)|~v1_funct_1(X55)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_funct_2])])])).
% 0.21/0.40  fof(c_0_62, plain, ![X40]:(((v1_relat_1(k1_xboole_0)&v5_relat_1(k1_xboole_0,X40))&v1_funct_1(k1_xboole_0))&v5_ordinal1(k1_xboole_0)), inference(variable_rename,[status(thm)],[t45_ordinal1])).
% 0.21/0.40  fof(c_0_63, plain, ![X10]:r1_tarski(k1_xboole_0,X10), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.21/0.40  cnf(c_0_64, negated_conjecture, (esk6_0=k1_xboole_0|esk5_0!=k1_xboole_0|~v1_xboole_0(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_57, c_0_58]), c_0_31]), c_0_32])])).
% 0.21/0.40  cnf(c_0_65, negated_conjecture, (v1_xboole_0(esk7_0)|esk5_0!=k1_xboole_0), inference(pm,[status(thm)],[c_0_59, c_0_60])).
% 0.21/0.40  cnf(c_0_66, plain, (v1_funct_2(X1,k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.21/0.40  cnf(c_0_67, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.21/0.40  cnf(c_0_68, plain, (v1_funct_1(k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.21/0.40  cnf(c_0_69, plain, (v1_relat_1(k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.21/0.40  cnf(c_0_70, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.21/0.40  cnf(c_0_71, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.21/0.40  fof(c_0_72, plain, ![X44, X45, X46]:(~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45)))|k1_relset_1(X44,X45,X46)=k1_relat_1(X46)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.21/0.40  cnf(c_0_73, negated_conjecture, (esk6_0=k1_xboole_0|esk5_0!=k1_xboole_0), inference(pm,[status(thm)],[c_0_64, c_0_65])).
% 0.21/0.40  cnf(c_0_74, plain, (v1_funct_2(k1_xboole_0,k1_xboole_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_66, c_0_67]), c_0_68]), c_0_69]), c_0_70]), c_0_71])])).
% 0.21/0.40  cnf(c_0_75, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.21/0.40  cnf(c_0_76, negated_conjecture, (esk5_0!=k1_xboole_0|~v1_funct_1(k2_funct_1(esk7_0))|~v1_xboole_0(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_50, c_0_73]), c_0_74])])).
% 0.21/0.40  cnf(c_0_77, plain, (v1_funct_2(X3,X1,X2)|X2=k1_xboole_0|X1!=k1_relset_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.21/0.40  cnf(c_0_78, plain, (k1_relset_1(X1,X2,k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_75, c_0_38]), c_0_67])).
% 0.21/0.40  cnf(c_0_79, negated_conjecture, (esk5_0!=k1_xboole_0|~v1_xboole_0(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_76, c_0_58]), c_0_31]), c_0_32])])).
% 0.21/0.40  cnf(c_0_80, plain, (X1=k1_xboole_0|v1_funct_2(k1_xboole_0,X2,X1)|k1_xboole_0!=X2), inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_77, c_0_38]), c_0_78])).
% 0.21/0.40  cnf(c_0_81, negated_conjecture, (esk5_0!=k1_xboole_0), inference(pm,[status(thm)],[c_0_79, c_0_65])).
% 0.21/0.40  cnf(c_0_82, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k1_xboole_0))|esk6_0!=k1_xboole_0), inference(pm,[status(thm)],[c_0_25, c_0_44])).
% 0.21/0.40  fof(c_0_83, plain, ![X53]:(((v1_funct_1(X53)|(~v1_relat_1(X53)|~v1_funct_1(X53)))&(v1_funct_2(X53,k1_relat_1(X53),k2_relat_1(X53))|(~v1_relat_1(X53)|~v1_funct_1(X53))))&(m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X53),k2_relat_1(X53))))|(~v1_relat_1(X53)|~v1_funct_1(X53)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).
% 0.21/0.40  fof(c_0_84, plain, ![X39]:((k2_relat_1(X39)=k1_relat_1(k2_funct_1(X39))|~v2_funct_1(X39)|(~v1_relat_1(X39)|~v1_funct_1(X39)))&(k1_relat_1(X39)=k2_relat_1(k2_funct_1(X39))|~v2_funct_1(X39)|(~v1_relat_1(X39)|~v1_funct_1(X39)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).
% 0.21/0.40  fof(c_0_85, plain, ![X47, X48, X49]:(~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))|k2_relset_1(X47,X48,X49)=k2_relat_1(X49)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.21/0.40  cnf(c_0_86, negated_conjecture, (esk6_0!=k1_xboole_0|~v1_funct_1(k2_funct_1(esk7_0))|~v1_xboole_0(esk7_0)), inference(sr,[status(thm)],[inference(pm,[status(thm)],[c_0_50, c_0_80]), c_0_81])).
% 0.21/0.40  cnf(c_0_87, negated_conjecture, (esk6_0!=k1_xboole_0|~r2_hidden(X1,esk7_0)), inference(sr,[status(thm)],[inference(pm,[status(thm)],[c_0_53, c_0_82]), c_0_55])).
% 0.21/0.40  cnf(c_0_88, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_83])).
% 0.21/0.40  cnf(c_0_89, plain, (k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_84])).
% 0.21/0.40  cnf(c_0_90, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_85])).
% 0.21/0.40  cnf(c_0_91, negated_conjecture, (k2_relset_1(esk5_0,esk6_0,esk7_0)=esk6_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.40  cnf(c_0_92, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.21/0.40  cnf(c_0_93, negated_conjecture, (k1_relset_1(esk5_0,esk6_0,esk7_0)=k1_relat_1(esk7_0)), inference(pm,[status(thm)],[c_0_75, c_0_25])).
% 0.21/0.40  cnf(c_0_94, negated_conjecture, (v1_funct_2(esk7_0,esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.40  cnf(c_0_95, negated_conjecture, (esk6_0!=k1_xboole_0|~v1_xboole_0(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_86, c_0_58]), c_0_31]), c_0_32])])).
% 0.21/0.40  cnf(c_0_96, negated_conjecture, (v1_xboole_0(esk7_0)|esk6_0!=k1_xboole_0), inference(pm,[status(thm)],[c_0_87, c_0_60])).
% 0.21/0.40  cnf(c_0_97, plain, (m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(X1))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)), inference(pm,[status(thm)],[c_0_88, c_0_89])).
% 0.21/0.40  cnf(c_0_98, negated_conjecture, (k2_relat_1(esk7_0)=esk6_0), inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_90, c_0_25]), c_0_91])).
% 0.21/0.40  cnf(c_0_99, negated_conjecture, (k1_relat_1(esk7_0)=esk5_0|esk6_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_92, c_0_25]), c_0_93]), c_0_94])])).
% 0.21/0.40  cnf(c_0_100, negated_conjecture, (esk6_0!=k1_xboole_0), inference(pm,[status(thm)],[c_0_95, c_0_96])).
% 0.21/0.40  cnf(c_0_101, plain, (v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_83])).
% 0.21/0.40  cnf(c_0_102, negated_conjecture, (m1_subset_1(k2_funct_1(esk7_0),k1_zfmisc_1(k2_zfmisc_1(esk6_0,k2_relat_1(k2_funct_1(esk7_0)))))|~v1_funct_1(k2_funct_1(esk7_0))|~v1_relat_1(k2_funct_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_97, c_0_98]), c_0_30]), c_0_31]), c_0_32])])).
% 0.21/0.40  cnf(c_0_103, plain, (k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_84])).
% 0.21/0.40  cnf(c_0_104, negated_conjecture, (k1_relat_1(esk7_0)=esk5_0), inference(sr,[status(thm)],[c_0_99, c_0_100])).
% 0.21/0.40  cnf(c_0_105, plain, (v1_funct_2(k2_funct_1(X1),k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(X1))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)), inference(pm,[status(thm)],[c_0_101, c_0_89])).
% 0.21/0.40  cnf(c_0_106, negated_conjecture, (m1_subset_1(k2_funct_1(esk7_0),k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk5_0)))|~v1_funct_1(k2_funct_1(esk7_0))|~v1_relat_1(k2_funct_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_102, c_0_103]), c_0_104]), c_0_30]), c_0_31]), c_0_32])])).
% 0.21/0.40  cnf(c_0_107, negated_conjecture, (v1_funct_2(k2_funct_1(esk7_0),esk6_0,k2_relat_1(k2_funct_1(esk7_0)))|~v1_funct_1(k2_funct_1(esk7_0))|~v1_relat_1(k2_funct_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_105, c_0_98]), c_0_30]), c_0_31]), c_0_32])])).
% 0.21/0.40  cnf(c_0_108, negated_conjecture, (~v1_funct_2(k2_funct_1(esk7_0),esk6_0,esk5_0)|~v1_funct_1(k2_funct_1(esk7_0))|~v1_relat_1(k2_funct_1(esk7_0))), inference(pm,[status(thm)],[c_0_28, c_0_106])).
% 0.21/0.40  cnf(c_0_109, negated_conjecture, (v1_funct_2(k2_funct_1(esk7_0),esk6_0,esk5_0)|~v1_funct_1(k2_funct_1(esk7_0))|~v1_relat_1(k2_funct_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_107, c_0_103]), c_0_104]), c_0_30]), c_0_31]), c_0_32])])).
% 0.21/0.40  cnf(c_0_110, negated_conjecture, (~v1_funct_1(k2_funct_1(esk7_0))|~v1_relat_1(k2_funct_1(esk7_0))), inference(pm,[status(thm)],[c_0_108, c_0_109])).
% 0.21/0.40  cnf(c_0_111, negated_conjecture, (~v1_relat_1(k2_funct_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_110, c_0_58]), c_0_31]), c_0_32])])).
% 0.21/0.40  cnf(c_0_112, plain, (v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.21/0.40  cnf(c_0_113, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_111, c_0_112]), c_0_31]), c_0_32])]), ['proof']).
% 0.21/0.40  # SZS output end CNFRefutation
% 0.21/0.40  # Proof object total steps             : 114
% 0.21/0.40  # Proof object clause steps            : 74
% 0.21/0.40  # Proof object formula steps           : 40
% 0.21/0.40  # Proof object conjectures             : 41
% 0.21/0.40  # Proof object clause conjectures      : 38
% 0.21/0.40  # Proof object formula conjectures     : 3
% 0.21/0.40  # Proof object initial clauses used    : 33
% 0.21/0.40  # Proof object initial formulas used   : 20
% 0.21/0.40  # Proof object generating inferences   : 40
% 0.21/0.40  # Proof object simplifying inferences  : 60
% 0.21/0.40  # Training examples: 0 positive, 0 negative
% 0.21/0.40  # Parsed axioms                        : 25
% 0.21/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.40  # Initial clauses                      : 54
% 0.21/0.40  # Removed in clause preprocessing      : 4
% 0.21/0.40  # Initial clauses in saturation        : 50
% 0.21/0.40  # Processed clauses                    : 436
% 0.21/0.40  # ...of these trivial                  : 2
% 0.21/0.40  # ...subsumed                          : 231
% 0.21/0.40  # ...remaining for further processing  : 203
% 0.21/0.40  # Other redundant clauses eliminated   : 0
% 0.21/0.40  # Clauses deleted for lack of memory   : 0
% 0.21/0.40  # Backward-subsumed                    : 23
% 0.21/0.40  # Backward-rewritten                   : 20
% 0.21/0.40  # Generated clauses                    : 1442
% 0.21/0.40  # ...of the previous two non-trivial   : 1318
% 0.21/0.40  # Contextual simplify-reflections      : 0
% 0.21/0.40  # Paramodulations                      : 1434
% 0.21/0.40  # Factorizations                       : 0
% 0.21/0.40  # Equation resolutions                 : 5
% 0.21/0.40  # Propositional unsat checks           : 0
% 0.21/0.40  #    Propositional check models        : 0
% 0.21/0.40  #    Propositional check unsatisfiable : 0
% 0.21/0.40  #    Propositional clauses             : 0
% 0.21/0.40  #    Propositional clauses after purity: 0
% 0.21/0.40  #    Propositional unsat core size     : 0
% 0.21/0.40  #    Propositional preprocessing time  : 0.000
% 0.21/0.40  #    Propositional encoding time       : 0.000
% 0.21/0.40  #    Propositional solver time         : 0.000
% 0.21/0.40  #    Success case prop preproc time    : 0.000
% 0.21/0.40  #    Success case prop encoding time   : 0.000
% 0.21/0.40  #    Success case prop solver time     : 0.000
% 0.21/0.40  # Current number of processed clauses  : 157
% 0.21/0.40  #    Positive orientable unit clauses  : 24
% 0.21/0.40  #    Positive unorientable unit clauses: 0
% 0.21/0.40  #    Negative unit clauses             : 10
% 0.21/0.40  #    Non-unit-clauses                  : 123
% 0.21/0.40  # Current number of unprocessed clauses: 900
% 0.21/0.40  # ...number of literals in the above   : 4324
% 0.21/0.40  # Current number of archived formulas  : 0
% 0.21/0.40  # Current number of archived clauses   : 46
% 0.21/0.40  # Clause-clause subsumption calls (NU) : 1154
% 0.21/0.40  # Rec. Clause-clause subsumption calls : 686
% 0.21/0.40  # Non-unit clause-clause subsumptions  : 128
% 0.21/0.40  # Unit Clause-clause subsumption calls : 246
% 0.21/0.40  # Rewrite failures with RHS unbound    : 0
% 0.21/0.40  # BW rewrite match attempts            : 9
% 0.21/0.40  # BW rewrite match successes           : 4
% 0.21/0.40  # Condensation attempts                : 0
% 0.21/0.40  # Condensation successes               : 0
% 0.21/0.40  # Termbank termtop insertions          : 13385
% 0.21/0.40  
% 0.21/0.40  # -------------------------------------------------
% 0.21/0.40  # User time                : 0.054 s
% 0.21/0.40  # System time              : 0.006 s
% 0.21/0.40  # Total time               : 0.060 s
% 0.21/0.40  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
