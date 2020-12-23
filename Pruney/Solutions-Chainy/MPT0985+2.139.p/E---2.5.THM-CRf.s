%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:02:53 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  121 (11915 expanded)
%              Number of clauses        :   86 (4458 expanded)
%              Number of leaves         :   18 (3019 expanded)
%              Depth                    :   19
%              Number of atoms          :  357 (57598 expanded)
%              Number of equality atoms :   84 (9990 expanded)
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

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(fc4_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => v1_xboole_0(k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_zfmisc_1)).

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

fof(cc1_subset_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(dt_k2_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(fc3_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X2)
     => v1_xboole_0(k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_zfmisc_1)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(t45_ordinal1,axiom,(
    ! [X1] :
      ( v1_relat_1(k1_xboole_0)
      & v5_relat_1(k1_xboole_0,X1)
      & v1_funct_1(k1_xboole_0)
      & v5_ordinal1(k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_ordinal1)).

fof(t4_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r1_tarski(k2_relat_1(X2),X1)
       => ( v1_funct_1(X2)
          & v1_funct_2(X2,k1_relat_1(X2),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(c_0_18,negated_conjecture,(
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

fof(c_0_19,plain,(
    ! [X28] :
      ( ( v1_funct_1(X28)
        | ~ v1_relat_1(X28)
        | ~ v1_funct_1(X28) )
      & ( v1_funct_2(X28,k1_relat_1(X28),k2_relat_1(X28))
        | ~ v1_relat_1(X28)
        | ~ v1_funct_1(X28) )
      & ( m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X28),k2_relat_1(X28))))
        | ~ v1_relat_1(X28)
        | ~ v1_funct_1(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).

fof(c_0_20,plain,(
    ! [X17] :
      ( ( k2_relat_1(X17) = k1_relat_1(k2_funct_1(X17))
        | ~ v2_funct_1(X17)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) )
      & ( k1_relat_1(X17) = k2_relat_1(k2_funct_1(X17))
        | ~ v2_funct_1(X17)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).

fof(c_0_21,plain,(
    ! [X22,X23,X24] :
      ( ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))
      | k2_relset_1(X22,X23,X24) = k2_relat_1(X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_22,negated_conjecture,
    ( v1_funct_1(esk3_0)
    & v1_funct_2(esk3_0,esk1_0,esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    & v2_funct_1(esk3_0)
    & k2_relset_1(esk1_0,esk2_0,esk3_0) = esk2_0
    & ( ~ v1_funct_1(k2_funct_1(esk3_0))
      | ~ v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)
      | ~ m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).

fof(c_0_23,plain,(
    ! [X12,X13] :
      ( ~ v1_relat_1(X12)
      | ~ m1_subset_1(X13,k1_zfmisc_1(X12))
      | v1_relat_1(X13) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_24,plain,(
    ! [X14,X15] : v1_relat_1(k2_zfmisc_1(X14,X15)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_25,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( k2_relset_1(esk1_0,esk2_0,esk3_0) = esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_32,plain,(
    ! [X19,X20,X21] :
      ( ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))
      | k1_relset_1(X19,X20,X21) = k1_relat_1(X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_33,plain,(
    ! [X4] :
      ( ~ v1_xboole_0(X4)
      | X4 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

fof(c_0_34,plain,(
    ! [X8,X9] :
      ( ~ v1_xboole_0(X8)
      | v1_xboole_0(k2_zfmisc_1(X8,X9)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc4_zfmisc_1])])).

cnf(c_0_35,plain,
    ( m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(pm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_36,negated_conjecture,
    ( k2_relat_1(esk3_0) = esk2_0 ),
    inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_27,c_0_28]),c_0_29])).

cnf(c_0_37,negated_conjecture,
    ( v2_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_38,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_39,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_30,c_0_28]),c_0_31])])).

fof(c_0_40,plain,(
    ! [X25,X26,X27] :
      ( ( ~ v1_funct_2(X27,X25,X26)
        | X25 = k1_relset_1(X25,X26,X27)
        | X26 = k1_xboole_0
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) )
      & ( X25 != k1_relset_1(X25,X26,X27)
        | v1_funct_2(X27,X25,X26)
        | X26 = k1_xboole_0
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) )
      & ( ~ v1_funct_2(X27,X25,X26)
        | X25 = k1_relset_1(X25,X26,X27)
        | X25 != k1_xboole_0
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) )
      & ( X25 != k1_relset_1(X25,X26,X27)
        | v1_funct_2(X27,X25,X26)
        | X25 != k1_xboole_0
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) )
      & ( ~ v1_funct_2(X27,X25,X26)
        | X27 = k1_xboole_0
        | X25 = k1_xboole_0
        | X26 != k1_xboole_0
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) )
      & ( X27 != k1_xboole_0
        | v1_funct_2(X27,X25,X26)
        | X25 = k1_xboole_0
        | X26 != k1_xboole_0
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_41,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_42,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_43,plain,(
    ! [X10,X11] :
      ( ~ v1_xboole_0(X10)
      | ~ m1_subset_1(X11,k1_zfmisc_1(X10))
      | v1_xboole_0(X11) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).

cnf(c_0_44,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_45,plain,
    ( v1_xboole_0(k2_zfmisc_1(X1,X2))
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,k2_relat_1(k2_funct_1(esk3_0)))))
    | ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_35,c_0_36]),c_0_37]),c_0_38]),c_0_39])])).

cnf(c_0_47,plain,
    ( k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_48,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_49,negated_conjecture,
    ( k1_relset_1(esk1_0,esk2_0,esk3_0) = k1_relat_1(esk3_0) ),
    inference(pm,[status(thm)],[c_0_41,c_0_28])).

cnf(c_0_50,negated_conjecture,
    ( v1_funct_2(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_51,plain,
    ( v1_funct_2(k2_funct_1(X1),k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(pm,[status(thm)],[c_0_42,c_0_26])).

cnf(c_0_52,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_53,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | X3 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_54,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(pm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_55,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_56,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,k1_relat_1(esk3_0))))
    | ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_46,c_0_47]),c_0_37]),c_0_38]),c_0_39])])).

cnf(c_0_57,negated_conjecture,
    ( k1_relat_1(esk3_0) = esk1_0
    | k1_xboole_0 = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_48,c_0_28]),c_0_49]),c_0_50])])).

cnf(c_0_58,negated_conjecture,
    ( v1_funct_2(k2_funct_1(esk3_0),esk2_0,k2_relat_1(k2_funct_1(esk3_0)))
    | ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_51,c_0_36]),c_0_37]),c_0_38]),c_0_39])])).

cnf(c_0_59,negated_conjecture,
    ( v1_xboole_0(esk3_0)
    | ~ v1_xboole_0(k2_zfmisc_1(esk1_0,esk2_0)) ),
    inference(pm,[status(thm)],[c_0_52,c_0_28])).

cnf(c_0_60,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | k1_xboole_0 != esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_53,c_0_28]),c_0_50])])).

cnf(c_0_61,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(pm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_62,negated_conjecture,
    ( ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)
    | ~ m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_63,negated_conjecture,
    ( k1_xboole_0 = esk2_0
    | m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))
    | ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(pm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_64,negated_conjecture,
    ( v1_funct_2(k2_funct_1(esk3_0),esk2_0,k1_relat_1(esk3_0))
    | ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_58,c_0_47]),c_0_37]),c_0_38]),c_0_39])])).

cnf(c_0_65,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | v1_xboole_0(esk3_0)
    | k1_xboole_0 != esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_59,c_0_60]),c_0_61]),c_0_55])])).

cnf(c_0_66,negated_conjecture,
    ( k1_xboole_0 = esk2_0
    | ~ v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)
    | ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(pm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_67,negated_conjecture,
    ( k1_xboole_0 = esk2_0
    | v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)
    | ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(pm,[status(thm)],[c_0_64,c_0_57])).

fof(c_0_68,plain,(
    ! [X16] :
      ( ( v1_relat_1(k2_funct_1(X16))
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) )
      & ( v1_funct_1(k2_funct_1(X16))
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

fof(c_0_69,plain,(
    ! [X6,X7] :
      ( ~ v1_xboole_0(X7)
      | v1_xboole_0(k2_zfmisc_1(X6,X7)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc3_zfmisc_1])])).

cnf(c_0_70,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | k1_xboole_0 != esk2_0 ),
    inference(pm,[status(thm)],[c_0_44,c_0_65])).

cnf(c_0_71,negated_conjecture,
    ( k1_xboole_0 = esk2_0
    | ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(pm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_72,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_73,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk3_0),esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_25,c_0_36]),c_0_38]),c_0_39])])).

cnf(c_0_74,plain,
    ( v1_xboole_0(k2_zfmisc_1(X2,X1))
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_75,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    | k1_xboole_0 != esk2_0 ),
    inference(pm,[status(thm)],[c_0_28,c_0_70])).

cnf(c_0_76,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_77,negated_conjecture,
    ( k1_xboole_0 = esk2_0
    | ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_71,c_0_72]),c_0_38]),c_0_39])])).

cnf(c_0_78,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_79,negated_conjecture,
    ( v1_xboole_0(esk3_0)
    | ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1(esk3_0),esk2_0)) ),
    inference(pm,[status(thm)],[c_0_52,c_0_73])).

cnf(c_0_80,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | ~ v1_xboole_0(X2) ),
    inference(pm,[status(thm)],[c_0_44,c_0_74])).

cnf(c_0_81,negated_conjecture,
    ( k1_relset_1(esk1_0,esk2_0,k1_xboole_0) = k1_xboole_0
    | k1_xboole_0 != esk2_0 ),
    inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_41,c_0_75]),c_0_76])).

cnf(c_0_82,negated_conjecture,
    ( k1_relset_1(esk1_0,esk2_0,k1_xboole_0) = k1_relat_1(esk3_0)
    | k1_xboole_0 != esk2_0 ),
    inference(pm,[status(thm)],[c_0_49,c_0_70])).

cnf(c_0_83,negated_conjecture,
    ( k1_xboole_0 = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_77,c_0_78]),c_0_38]),c_0_39])])).

cnf(c_0_84,negated_conjecture,
    ( v1_xboole_0(esk3_0)
    | k1_xboole_0 != esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_79,c_0_70]),c_0_76]),c_0_61]),c_0_55])])).

cnf(c_0_85,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)
    | ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k1_xboole_0))
    | ~ v1_xboole_0(esk2_0) ),
    inference(pm,[status(thm)],[c_0_62,c_0_54])).

cnf(c_0_86,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_xboole_0(k1_relat_1(X1)) ),
    inference(pm,[status(thm)],[c_0_25,c_0_54])).

cnf(c_0_87,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_xboole_0(esk2_0) ),
    inference(pm,[status(thm)],[c_0_28,c_0_80])).

cnf(c_0_88,negated_conjecture,
    ( k1_relat_1(esk3_0) = k1_xboole_0
    | k1_xboole_0 != esk2_0 ),
    inference(pm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_89,negated_conjecture,
    ( esk3_0 = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_83]),c_0_83])])).

cnf(c_0_90,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,X1) = k1_xboole_0
    | k1_xboole_0 != esk2_0 ),
    inference(pm,[status(thm)],[c_0_54,c_0_84])).

cnf(c_0_91,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)
    | ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ v1_relat_1(k2_funct_1(esk3_0))
    | ~ v1_xboole_0(k1_relat_1(k2_funct_1(esk3_0)))
    | ~ v1_xboole_0(esk2_0) ),
    inference(pm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_92,negated_conjecture,
    ( v1_xboole_0(esk3_0)
    | ~ v1_xboole_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_52,c_0_87]),c_0_55])])).

cnf(c_0_93,negated_conjecture,
    ( k1_relat_1(esk2_0) = esk2_0 ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_88,c_0_83]),c_0_83])]),c_0_89])).

cnf(c_0_94,negated_conjecture,
    ( k2_zfmisc_1(esk2_0,X1) = esk2_0 ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_90,c_0_83]),c_0_83])]),c_0_89])).

fof(c_0_95,plain,(
    ! [X18] :
      ( v1_relat_1(k1_xboole_0)
      & v5_relat_1(k1_xboole_0,X18)
      & v1_funct_1(k1_xboole_0)
      & v5_ordinal1(k1_xboole_0) ) ),
    inference(variable_rename,[status(thm)],[t45_ordinal1])).

cnf(c_0_96,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)
    | ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ v1_relat_1(k2_funct_1(esk3_0))
    | ~ v1_xboole_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_91,c_0_26]),c_0_36]),c_0_37]),c_0_38]),c_0_39])])).

cnf(c_0_97,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | ~ v1_xboole_0(esk2_0) ),
    inference(pm,[status(thm)],[c_0_44,c_0_92])).

cnf(c_0_98,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk2_0),k1_zfmisc_1(esk2_0))
    | ~ v1_funct_1(k2_funct_1(esk2_0))
    | ~ v1_relat_1(k2_funct_1(esk2_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_89]),c_0_89]),c_0_89]),c_0_89]),c_0_93]),c_0_94])).

cnf(c_0_99,plain,
    ( v1_xboole_0(esk2_0) ),
    inference(rw,[status(thm)],[c_0_55,c_0_83])).

cnf(c_0_100,plain,
    ( v1_funct_1(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_95])).

cnf(c_0_101,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_95])).

cnf(c_0_102,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(k1_xboole_0),esk2_0,esk1_0)
    | ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ v1_relat_1(k2_funct_1(esk3_0))
    | ~ v1_xboole_0(esk2_0) ),
    inference(pm,[status(thm)],[c_0_96,c_0_97])).

cnf(c_0_103,negated_conjecture,
    ( v1_xboole_0(k2_funct_1(esk2_0))
    | ~ v1_funct_1(k2_funct_1(esk2_0))
    | ~ v1_relat_1(k2_funct_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_52,c_0_98]),c_0_99])])).

cnf(c_0_104,plain,
    ( v1_funct_1(esk2_0) ),
    inference(rw,[status(thm)],[c_0_100,c_0_83])).

cnf(c_0_105,plain,
    ( v1_relat_1(esk2_0) ),
    inference(rw,[status(thm)],[c_0_101,c_0_83])).

fof(c_0_106,plain,(
    ! [X29,X30] :
      ( ( v1_funct_1(X30)
        | ~ r1_tarski(k2_relat_1(X30),X29)
        | ~ v1_relat_1(X30)
        | ~ v1_funct_1(X30) )
      & ( v1_funct_2(X30,k1_relat_1(X30),X29)
        | ~ r1_tarski(k2_relat_1(X30),X29)
        | ~ v1_relat_1(X30)
        | ~ v1_funct_1(X30) )
      & ( m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X30),X29)))
        | ~ r1_tarski(k2_relat_1(X30),X29)
        | ~ v1_relat_1(X30)
        | ~ v1_funct_1(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_funct_2])])])).

fof(c_0_107,plain,(
    ! [X5] : r1_tarski(k1_xboole_0,X5) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_108,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(esk2_0),esk2_0,esk1_0)
    | ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_102,c_0_83]),c_0_99])])).

cnf(c_0_109,negated_conjecture,
    ( v1_xboole_0(k2_funct_1(esk2_0))
    | ~ v1_relat_1(k2_funct_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_103,c_0_72]),c_0_104]),c_0_105])])).

cnf(c_0_110,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_106])).

cnf(c_0_111,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_112,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_107])).

cnf(c_0_113,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(esk2_0),esk2_0,esk1_0)
    | ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_108,c_0_72]),c_0_38]),c_0_39])])).

cnf(c_0_114,plain,
    ( X1 = esk2_0
    | ~ v1_xboole_0(X1) ),
    inference(rw,[status(thm)],[c_0_44,c_0_83])).

cnf(c_0_115,negated_conjecture,
    ( v1_xboole_0(k2_funct_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_109,c_0_78]),c_0_104]),c_0_105])])).

cnf(c_0_116,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_110,c_0_76]),c_0_100]),c_0_101]),c_0_111]),c_0_112])])).

cnf(c_0_117,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(esk2_0),esk2_0,esk1_0)
    | ~ v1_relat_1(k2_funct_1(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_113,c_0_89])).

cnf(c_0_118,negated_conjecture,
    ( k2_funct_1(esk2_0) = esk2_0 ),
    inference(pm,[status(thm)],[c_0_114,c_0_115])).

cnf(c_0_119,plain,
    ( v1_funct_2(esk2_0,esk2_0,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_116,c_0_83]),c_0_83])).

cnf(c_0_120,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_117,c_0_118]),c_0_119]),c_0_118]),c_0_105])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:55:24 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.42  # AutoSched0-Mode selected heuristic G_E___300_C01_S00
% 0.20/0.42  # and selection function NoSelection.
% 0.20/0.42  #
% 0.20/0.42  # Preprocessing time       : 0.028 s
% 0.20/0.42  
% 0.20/0.42  # Proof found!
% 0.20/0.42  # SZS status Theorem
% 0.20/0.42  # SZS output start CNFRefutation
% 0.20/0.42  fof(t31_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v2_funct_1(X3)&k2_relset_1(X1,X2,X3)=X2)=>((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),X2,X1))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 0.20/0.42  fof(t3_funct_2, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>((v1_funct_1(X1)&v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1)))&m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 0.20/0.42  fof(t55_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))&k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 0.20/0.42  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.20/0.42  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.20/0.42  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.20/0.42  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.20/0.42  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.20/0.42  fof(fc4_zfmisc_1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>v1_xboole_0(k2_zfmisc_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_zfmisc_1)).
% 0.20/0.42  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 0.20/0.42  fof(cc1_subset_1, axiom, ![X1]:(v1_xboole_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_xboole_0(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 0.20/0.42  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.20/0.42  fof(dt_k2_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k2_funct_1(X1))&v1_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 0.20/0.42  fof(fc3_zfmisc_1, axiom, ![X1, X2]:(v1_xboole_0(X2)=>v1_xboole_0(k2_zfmisc_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_zfmisc_1)).
% 0.20/0.42  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 0.20/0.42  fof(t45_ordinal1, axiom, ![X1]:(((v1_relat_1(k1_xboole_0)&v5_relat_1(k1_xboole_0,X1))&v1_funct_1(k1_xboole_0))&v5_ordinal1(k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_ordinal1)).
% 0.20/0.42  fof(t4_funct_2, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r1_tarski(k2_relat_1(X2),X1)=>((v1_funct_1(X2)&v1_funct_2(X2,k1_relat_1(X2),X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 0.20/0.42  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.20/0.42  fof(c_0_18, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v2_funct_1(X3)&k2_relset_1(X1,X2,X3)=X2)=>((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),X2,X1))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))))))), inference(assume_negation,[status(cth)],[t31_funct_2])).
% 0.20/0.42  fof(c_0_19, plain, ![X28]:(((v1_funct_1(X28)|(~v1_relat_1(X28)|~v1_funct_1(X28)))&(v1_funct_2(X28,k1_relat_1(X28),k2_relat_1(X28))|(~v1_relat_1(X28)|~v1_funct_1(X28))))&(m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X28),k2_relat_1(X28))))|(~v1_relat_1(X28)|~v1_funct_1(X28)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).
% 0.20/0.42  fof(c_0_20, plain, ![X17]:((k2_relat_1(X17)=k1_relat_1(k2_funct_1(X17))|~v2_funct_1(X17)|(~v1_relat_1(X17)|~v1_funct_1(X17)))&(k1_relat_1(X17)=k2_relat_1(k2_funct_1(X17))|~v2_funct_1(X17)|(~v1_relat_1(X17)|~v1_funct_1(X17)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).
% 0.20/0.42  fof(c_0_21, plain, ![X22, X23, X24]:(~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))|k2_relset_1(X22,X23,X24)=k2_relat_1(X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.20/0.42  fof(c_0_22, negated_conjecture, (((v1_funct_1(esk3_0)&v1_funct_2(esk3_0,esk1_0,esk2_0))&m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))))&((v2_funct_1(esk3_0)&k2_relset_1(esk1_0,esk2_0,esk3_0)=esk2_0)&(~v1_funct_1(k2_funct_1(esk3_0))|~v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)|~m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).
% 0.20/0.42  fof(c_0_23, plain, ![X12, X13]:(~v1_relat_1(X12)|(~m1_subset_1(X13,k1_zfmisc_1(X12))|v1_relat_1(X13))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.20/0.42  fof(c_0_24, plain, ![X14, X15]:v1_relat_1(k2_zfmisc_1(X14,X15)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.20/0.42  cnf(c_0_25, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.42  cnf(c_0_26, plain, (k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.42  cnf(c_0_27, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.42  cnf(c_0_28, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.42  cnf(c_0_29, negated_conjecture, (k2_relset_1(esk1_0,esk2_0,esk3_0)=esk2_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.42  cnf(c_0_30, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.42  cnf(c_0_31, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.42  fof(c_0_32, plain, ![X19, X20, X21]:(~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))|k1_relset_1(X19,X20,X21)=k1_relat_1(X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.20/0.42  fof(c_0_33, plain, ![X4]:(~v1_xboole_0(X4)|X4=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.20/0.42  fof(c_0_34, plain, ![X8, X9]:(~v1_xboole_0(X8)|v1_xboole_0(k2_zfmisc_1(X8,X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc4_zfmisc_1])])).
% 0.20/0.42  cnf(c_0_35, plain, (m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(X1))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)), inference(pm,[status(thm)],[c_0_25, c_0_26])).
% 0.20/0.42  cnf(c_0_36, negated_conjecture, (k2_relat_1(esk3_0)=esk2_0), inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_27, c_0_28]), c_0_29])).
% 0.20/0.42  cnf(c_0_37, negated_conjecture, (v2_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.42  cnf(c_0_38, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.42  cnf(c_0_39, negated_conjecture, (v1_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_30, c_0_28]), c_0_31])])).
% 0.20/0.42  fof(c_0_40, plain, ![X25, X26, X27]:((((~v1_funct_2(X27,X25,X26)|X25=k1_relset_1(X25,X26,X27)|X26=k1_xboole_0|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))))&(X25!=k1_relset_1(X25,X26,X27)|v1_funct_2(X27,X25,X26)|X26=k1_xboole_0|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))))&((~v1_funct_2(X27,X25,X26)|X25=k1_relset_1(X25,X26,X27)|X25!=k1_xboole_0|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))))&(X25!=k1_relset_1(X25,X26,X27)|v1_funct_2(X27,X25,X26)|X25!=k1_xboole_0|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))))))&((~v1_funct_2(X27,X25,X26)|X27=k1_xboole_0|X25=k1_xboole_0|X26!=k1_xboole_0|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))))&(X27!=k1_xboole_0|v1_funct_2(X27,X25,X26)|X25=k1_xboole_0|X26!=k1_xboole_0|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.20/0.42  cnf(c_0_41, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.42  cnf(c_0_42, plain, (v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.42  fof(c_0_43, plain, ![X10, X11]:(~v1_xboole_0(X10)|(~m1_subset_1(X11,k1_zfmisc_1(X10))|v1_xboole_0(X11))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).
% 0.20/0.42  cnf(c_0_44, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.42  cnf(c_0_45, plain, (v1_xboole_0(k2_zfmisc_1(X1,X2))|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.42  cnf(c_0_46, negated_conjecture, (m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,k2_relat_1(k2_funct_1(esk3_0)))))|~v1_funct_1(k2_funct_1(esk3_0))|~v1_relat_1(k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_35, c_0_36]), c_0_37]), c_0_38]), c_0_39])])).
% 0.20/0.42  cnf(c_0_47, plain, (k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.42  cnf(c_0_48, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.42  cnf(c_0_49, negated_conjecture, (k1_relset_1(esk1_0,esk2_0,esk3_0)=k1_relat_1(esk3_0)), inference(pm,[status(thm)],[c_0_41, c_0_28])).
% 0.20/0.42  cnf(c_0_50, negated_conjecture, (v1_funct_2(esk3_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.42  cnf(c_0_51, plain, (v1_funct_2(k2_funct_1(X1),k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(X1))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)), inference(pm,[status(thm)],[c_0_42, c_0_26])).
% 0.20/0.42  cnf(c_0_52, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.42  cnf(c_0_53, plain, (X1=k1_xboole_0|X2=k1_xboole_0|~v1_funct_2(X1,X2,X3)|X3!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.42  cnf(c_0_54, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|~v1_xboole_0(X1)), inference(pm,[status(thm)],[c_0_44, c_0_45])).
% 0.20/0.42  cnf(c_0_55, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.20/0.42  cnf(c_0_56, negated_conjecture, (m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,k1_relat_1(esk3_0))))|~v1_funct_1(k2_funct_1(esk3_0))|~v1_relat_1(k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_46, c_0_47]), c_0_37]), c_0_38]), c_0_39])])).
% 0.20/0.42  cnf(c_0_57, negated_conjecture, (k1_relat_1(esk3_0)=esk1_0|k1_xboole_0=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_48, c_0_28]), c_0_49]), c_0_50])])).
% 0.20/0.42  cnf(c_0_58, negated_conjecture, (v1_funct_2(k2_funct_1(esk3_0),esk2_0,k2_relat_1(k2_funct_1(esk3_0)))|~v1_funct_1(k2_funct_1(esk3_0))|~v1_relat_1(k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_51, c_0_36]), c_0_37]), c_0_38]), c_0_39])])).
% 0.20/0.42  cnf(c_0_59, negated_conjecture, (v1_xboole_0(esk3_0)|~v1_xboole_0(k2_zfmisc_1(esk1_0,esk2_0))), inference(pm,[status(thm)],[c_0_52, c_0_28])).
% 0.20/0.42  cnf(c_0_60, negated_conjecture, (esk1_0=k1_xboole_0|esk3_0=k1_xboole_0|k1_xboole_0!=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_53, c_0_28]), c_0_50])])).
% 0.20/0.42  cnf(c_0_61, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(pm,[status(thm)],[c_0_54, c_0_55])).
% 0.20/0.42  cnf(c_0_62, negated_conjecture, (~v1_funct_1(k2_funct_1(esk3_0))|~v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)|~m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.42  cnf(c_0_63, negated_conjecture, (k1_xboole_0=esk2_0|m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))|~v1_funct_1(k2_funct_1(esk3_0))|~v1_relat_1(k2_funct_1(esk3_0))), inference(pm,[status(thm)],[c_0_56, c_0_57])).
% 0.20/0.42  cnf(c_0_64, negated_conjecture, (v1_funct_2(k2_funct_1(esk3_0),esk2_0,k1_relat_1(esk3_0))|~v1_funct_1(k2_funct_1(esk3_0))|~v1_relat_1(k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_58, c_0_47]), c_0_37]), c_0_38]), c_0_39])])).
% 0.20/0.42  cnf(c_0_65, negated_conjecture, (esk3_0=k1_xboole_0|v1_xboole_0(esk3_0)|k1_xboole_0!=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_59, c_0_60]), c_0_61]), c_0_55])])).
% 0.20/0.42  cnf(c_0_66, negated_conjecture, (k1_xboole_0=esk2_0|~v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)|~v1_funct_1(k2_funct_1(esk3_0))|~v1_relat_1(k2_funct_1(esk3_0))), inference(pm,[status(thm)],[c_0_62, c_0_63])).
% 0.20/0.42  cnf(c_0_67, negated_conjecture, (k1_xboole_0=esk2_0|v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)|~v1_funct_1(k2_funct_1(esk3_0))|~v1_relat_1(k2_funct_1(esk3_0))), inference(pm,[status(thm)],[c_0_64, c_0_57])).
% 0.20/0.42  fof(c_0_68, plain, ![X16]:((v1_relat_1(k2_funct_1(X16))|(~v1_relat_1(X16)|~v1_funct_1(X16)))&(v1_funct_1(k2_funct_1(X16))|(~v1_relat_1(X16)|~v1_funct_1(X16)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).
% 0.20/0.42  fof(c_0_69, plain, ![X6, X7]:(~v1_xboole_0(X7)|v1_xboole_0(k2_zfmisc_1(X6,X7))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc3_zfmisc_1])])).
% 0.20/0.42  cnf(c_0_70, negated_conjecture, (esk3_0=k1_xboole_0|k1_xboole_0!=esk2_0), inference(pm,[status(thm)],[c_0_44, c_0_65])).
% 0.20/0.42  cnf(c_0_71, negated_conjecture, (k1_xboole_0=esk2_0|~v1_funct_1(k2_funct_1(esk3_0))|~v1_relat_1(k2_funct_1(esk3_0))), inference(pm,[status(thm)],[c_0_66, c_0_67])).
% 0.20/0.42  cnf(c_0_72, plain, (v1_funct_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.20/0.42  cnf(c_0_73, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk3_0),esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_25, c_0_36]), c_0_38]), c_0_39])])).
% 0.20/0.42  cnf(c_0_74, plain, (v1_xboole_0(k2_zfmisc_1(X2,X1))|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.20/0.42  cnf(c_0_75, negated_conjecture, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))|k1_xboole_0!=esk2_0), inference(pm,[status(thm)],[c_0_28, c_0_70])).
% 0.20/0.42  cnf(c_0_76, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.20/0.42  cnf(c_0_77, negated_conjecture, (k1_xboole_0=esk2_0|~v1_relat_1(k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_71, c_0_72]), c_0_38]), c_0_39])])).
% 0.20/0.42  cnf(c_0_78, plain, (v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.20/0.42  cnf(c_0_79, negated_conjecture, (v1_xboole_0(esk3_0)|~v1_xboole_0(k2_zfmisc_1(k1_relat_1(esk3_0),esk2_0))), inference(pm,[status(thm)],[c_0_52, c_0_73])).
% 0.20/0.42  cnf(c_0_80, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|~v1_xboole_0(X2)), inference(pm,[status(thm)],[c_0_44, c_0_74])).
% 0.20/0.42  cnf(c_0_81, negated_conjecture, (k1_relset_1(esk1_0,esk2_0,k1_xboole_0)=k1_xboole_0|k1_xboole_0!=esk2_0), inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_41, c_0_75]), c_0_76])).
% 0.20/0.42  cnf(c_0_82, negated_conjecture, (k1_relset_1(esk1_0,esk2_0,k1_xboole_0)=k1_relat_1(esk3_0)|k1_xboole_0!=esk2_0), inference(pm,[status(thm)],[c_0_49, c_0_70])).
% 0.20/0.42  cnf(c_0_83, negated_conjecture, (k1_xboole_0=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_77, c_0_78]), c_0_38]), c_0_39])])).
% 0.20/0.42  cnf(c_0_84, negated_conjecture, (v1_xboole_0(esk3_0)|k1_xboole_0!=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_79, c_0_70]), c_0_76]), c_0_61]), c_0_55])])).
% 0.20/0.42  cnf(c_0_85, negated_conjecture, (~v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)|~v1_funct_1(k2_funct_1(esk3_0))|~m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k1_xboole_0))|~v1_xboole_0(esk2_0)), inference(pm,[status(thm)],[c_0_62, c_0_54])).
% 0.20/0.42  cnf(c_0_86, plain, (m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))|~v1_funct_1(X1)|~v1_relat_1(X1)|~v1_xboole_0(k1_relat_1(X1))), inference(pm,[status(thm)],[c_0_25, c_0_54])).
% 0.20/0.42  cnf(c_0_87, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0))|~v1_xboole_0(esk2_0)), inference(pm,[status(thm)],[c_0_28, c_0_80])).
% 0.20/0.42  cnf(c_0_88, negated_conjecture, (k1_relat_1(esk3_0)=k1_xboole_0|k1_xboole_0!=esk2_0), inference(pm,[status(thm)],[c_0_81, c_0_82])).
% 0.20/0.42  cnf(c_0_89, negated_conjecture, (esk3_0=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_83]), c_0_83])])).
% 0.20/0.42  cnf(c_0_90, negated_conjecture, (k2_zfmisc_1(esk3_0,X1)=k1_xboole_0|k1_xboole_0!=esk2_0), inference(pm,[status(thm)],[c_0_54, c_0_84])).
% 0.20/0.42  cnf(c_0_91, negated_conjecture, (~v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)|~v1_funct_1(k2_funct_1(esk3_0))|~v1_relat_1(k2_funct_1(esk3_0))|~v1_xboole_0(k1_relat_1(k2_funct_1(esk3_0)))|~v1_xboole_0(esk2_0)), inference(pm,[status(thm)],[c_0_85, c_0_86])).
% 0.20/0.42  cnf(c_0_92, negated_conjecture, (v1_xboole_0(esk3_0)|~v1_xboole_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_52, c_0_87]), c_0_55])])).
% 0.20/0.42  cnf(c_0_93, negated_conjecture, (k1_relat_1(esk2_0)=esk2_0), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_88, c_0_83]), c_0_83])]), c_0_89])).
% 0.20/0.42  cnf(c_0_94, negated_conjecture, (k2_zfmisc_1(esk2_0,X1)=esk2_0), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_90, c_0_83]), c_0_83])]), c_0_89])).
% 0.20/0.42  fof(c_0_95, plain, ![X18]:(((v1_relat_1(k1_xboole_0)&v5_relat_1(k1_xboole_0,X18))&v1_funct_1(k1_xboole_0))&v5_ordinal1(k1_xboole_0)), inference(variable_rename,[status(thm)],[t45_ordinal1])).
% 0.20/0.42  cnf(c_0_96, negated_conjecture, (~v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)|~v1_funct_1(k2_funct_1(esk3_0))|~v1_relat_1(k2_funct_1(esk3_0))|~v1_xboole_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_91, c_0_26]), c_0_36]), c_0_37]), c_0_38]), c_0_39])])).
% 0.20/0.42  cnf(c_0_97, negated_conjecture, (esk3_0=k1_xboole_0|~v1_xboole_0(esk2_0)), inference(pm,[status(thm)],[c_0_44, c_0_92])).
% 0.20/0.42  cnf(c_0_98, negated_conjecture, (m1_subset_1(k2_funct_1(esk2_0),k1_zfmisc_1(esk2_0))|~v1_funct_1(k2_funct_1(esk2_0))|~v1_relat_1(k2_funct_1(esk2_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_89]), c_0_89]), c_0_89]), c_0_89]), c_0_93]), c_0_94])).
% 0.20/0.42  cnf(c_0_99, plain, (v1_xboole_0(esk2_0)), inference(rw,[status(thm)],[c_0_55, c_0_83])).
% 0.20/0.42  cnf(c_0_100, plain, (v1_funct_1(k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_95])).
% 0.20/0.42  cnf(c_0_101, plain, (v1_relat_1(k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_95])).
% 0.20/0.42  cnf(c_0_102, negated_conjecture, (~v1_funct_2(k2_funct_1(k1_xboole_0),esk2_0,esk1_0)|~v1_funct_1(k2_funct_1(esk3_0))|~v1_relat_1(k2_funct_1(esk3_0))|~v1_xboole_0(esk2_0)), inference(pm,[status(thm)],[c_0_96, c_0_97])).
% 0.20/0.42  cnf(c_0_103, negated_conjecture, (v1_xboole_0(k2_funct_1(esk2_0))|~v1_funct_1(k2_funct_1(esk2_0))|~v1_relat_1(k2_funct_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_52, c_0_98]), c_0_99])])).
% 0.20/0.42  cnf(c_0_104, plain, (v1_funct_1(esk2_0)), inference(rw,[status(thm)],[c_0_100, c_0_83])).
% 0.20/0.42  cnf(c_0_105, plain, (v1_relat_1(esk2_0)), inference(rw,[status(thm)],[c_0_101, c_0_83])).
% 0.20/0.42  fof(c_0_106, plain, ![X29, X30]:(((v1_funct_1(X30)|~r1_tarski(k2_relat_1(X30),X29)|(~v1_relat_1(X30)|~v1_funct_1(X30)))&(v1_funct_2(X30,k1_relat_1(X30),X29)|~r1_tarski(k2_relat_1(X30),X29)|(~v1_relat_1(X30)|~v1_funct_1(X30))))&(m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X30),X29)))|~r1_tarski(k2_relat_1(X30),X29)|(~v1_relat_1(X30)|~v1_funct_1(X30)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_funct_2])])])).
% 0.20/0.42  fof(c_0_107, plain, ![X5]:r1_tarski(k1_xboole_0,X5), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.20/0.42  cnf(c_0_108, negated_conjecture, (~v1_funct_2(k2_funct_1(esk2_0),esk2_0,esk1_0)|~v1_funct_1(k2_funct_1(esk3_0))|~v1_relat_1(k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_102, c_0_83]), c_0_99])])).
% 0.20/0.42  cnf(c_0_109, negated_conjecture, (v1_xboole_0(k2_funct_1(esk2_0))|~v1_relat_1(k2_funct_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_103, c_0_72]), c_0_104]), c_0_105])])).
% 0.20/0.42  cnf(c_0_110, plain, (v1_funct_2(X1,k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_106])).
% 0.20/0.42  cnf(c_0_111, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.20/0.42  cnf(c_0_112, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_107])).
% 0.20/0.42  cnf(c_0_113, negated_conjecture, (~v1_funct_2(k2_funct_1(esk2_0),esk2_0,esk1_0)|~v1_relat_1(k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_108, c_0_72]), c_0_38]), c_0_39])])).
% 0.20/0.42  cnf(c_0_114, plain, (X1=esk2_0|~v1_xboole_0(X1)), inference(rw,[status(thm)],[c_0_44, c_0_83])).
% 0.20/0.42  cnf(c_0_115, negated_conjecture, (v1_xboole_0(k2_funct_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_109, c_0_78]), c_0_104]), c_0_105])])).
% 0.20/0.42  cnf(c_0_116, plain, (v1_funct_2(k1_xboole_0,k1_xboole_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_110, c_0_76]), c_0_100]), c_0_101]), c_0_111]), c_0_112])])).
% 0.20/0.42  cnf(c_0_117, negated_conjecture, (~v1_funct_2(k2_funct_1(esk2_0),esk2_0,esk1_0)|~v1_relat_1(k2_funct_1(esk2_0))), inference(rw,[status(thm)],[c_0_113, c_0_89])).
% 0.20/0.42  cnf(c_0_118, negated_conjecture, (k2_funct_1(esk2_0)=esk2_0), inference(pm,[status(thm)],[c_0_114, c_0_115])).
% 0.20/0.42  cnf(c_0_119, plain, (v1_funct_2(esk2_0,esk2_0,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_116, c_0_83]), c_0_83])).
% 0.20/0.42  cnf(c_0_120, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_117, c_0_118]), c_0_119]), c_0_118]), c_0_105])]), ['proof']).
% 0.20/0.42  # SZS output end CNFRefutation
% 0.20/0.42  # Proof object total steps             : 121
% 0.20/0.42  # Proof object clause steps            : 86
% 0.20/0.42  # Proof object formula steps           : 35
% 0.20/0.42  # Proof object conjectures             : 54
% 0.20/0.42  # Proof object clause conjectures      : 51
% 0.20/0.42  # Proof object formula conjectures     : 3
% 0.20/0.42  # Proof object initial clauses used    : 29
% 0.20/0.42  # Proof object initial formulas used   : 18
% 0.20/0.42  # Proof object generating inferences   : 45
% 0.20/0.42  # Proof object simplifying inferences  : 96
% 0.20/0.42  # Training examples: 0 positive, 0 negative
% 0.20/0.42  # Parsed axioms                        : 18
% 0.20/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.42  # Initial clauses                      : 38
% 0.20/0.42  # Removed in clause preprocessing      : 2
% 0.20/0.42  # Initial clauses in saturation        : 36
% 0.20/0.42  # Processed clauses                    : 833
% 0.20/0.42  # ...of these trivial                  : 85
% 0.20/0.42  # ...subsumed                          : 405
% 0.20/0.42  # ...remaining for further processing  : 343
% 0.20/0.42  # Other redundant clauses eliminated   : 0
% 0.20/0.42  # Clauses deleted for lack of memory   : 0
% 0.20/0.42  # Backward-subsumed                    : 39
% 0.20/0.42  # Backward-rewritten                   : 210
% 0.20/0.42  # Generated clauses                    : 2676
% 0.20/0.42  # ...of the previous two non-trivial   : 1939
% 0.20/0.42  # Contextual simplify-reflections      : 0
% 0.20/0.42  # Paramodulations                      : 2676
% 0.20/0.42  # Factorizations                       : 0
% 0.20/0.42  # Equation resolutions                 : 0
% 0.20/0.42  # Propositional unsat checks           : 0
% 0.20/0.42  #    Propositional check models        : 0
% 0.20/0.42  #    Propositional check unsatisfiable : 0
% 0.20/0.42  #    Propositional clauses             : 0
% 0.20/0.42  #    Propositional clauses after purity: 0
% 0.20/0.42  #    Propositional unsat core size     : 0
% 0.20/0.42  #    Propositional preprocessing time  : 0.000
% 0.20/0.42  #    Propositional encoding time       : 0.000
% 0.20/0.42  #    Propositional solver time         : 0.000
% 0.20/0.42  #    Success case prop preproc time    : 0.000
% 0.20/0.42  #    Success case prop encoding time   : 0.000
% 0.20/0.42  #    Success case prop solver time     : 0.000
% 0.20/0.42  # Current number of processed clauses  : 94
% 0.20/0.42  #    Positive orientable unit clauses  : 22
% 0.20/0.42  #    Positive unorientable unit clauses: 0
% 0.20/0.42  #    Negative unit clauses             : 1
% 0.20/0.42  #    Non-unit-clauses                  : 71
% 0.20/0.42  # Current number of unprocessed clauses: 954
% 0.20/0.42  # ...number of literals in the above   : 4531
% 0.20/0.42  # Current number of archived formulas  : 0
% 0.20/0.42  # Current number of archived clauses   : 249
% 0.20/0.42  # Clause-clause subsumption calls (NU) : 3776
% 0.20/0.42  # Rec. Clause-clause subsumption calls : 2603
% 0.20/0.42  # Non-unit clause-clause subsumptions  : 427
% 0.20/0.42  # Unit Clause-clause subsumption calls : 170
% 0.20/0.42  # Rewrite failures with RHS unbound    : 0
% 0.20/0.42  # BW rewrite match attempts            : 28
% 0.20/0.42  # BW rewrite match successes           : 18
% 0.20/0.42  # Condensation attempts                : 0
% 0.20/0.42  # Condensation successes               : 0
% 0.20/0.42  # Termbank termtop insertions          : 20548
% 0.20/0.42  
% 0.20/0.42  # -------------------------------------------------
% 0.20/0.42  # User time                : 0.075 s
% 0.20/0.42  # System time              : 0.005 s
% 0.20/0.42  # Total time               : 0.081 s
% 0.20/0.42  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
