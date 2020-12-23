%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:02:45 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  124 (2186 expanded)
%              Number of clauses        :   90 ( 899 expanded)
%              Number of leaves         :   17 ( 570 expanded)
%              Depth                    :   26
%              Number of atoms          :  441 (8867 expanded)
%              Number of equality atoms :   90 (1477 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   36 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(t65_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k1_relat_1(X1) = k1_xboole_0
      <=> k2_relat_1(X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(l222_relat_1,axiom,(
    ! [X1,X2] :
      ( v4_relat_1(k1_xboole_0,X1)
      & v5_relat_1(k1_xboole_0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l222_relat_1)).

fof(t45_ordinal1,axiom,(
    ! [X1] :
      ( v1_relat_1(k1_xboole_0)
      & v5_relat_1(k1_xboole_0,X1)
      & v1_funct_1(k1_xboole_0)
      & v5_ordinal1(k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_ordinal1)).

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

fof(t64_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( ( k1_relat_1(X1) = k1_xboole_0
          | k2_relat_1(X1) = k1_xboole_0 )
       => X1 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(t55_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
          & k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(dt_k2_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(fc11_relat_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => v1_xboole_0(k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc11_relat_1)).

fof(t3_funct_2,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_funct_1(X1)
        & v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(t9_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r1_tarski(X2,X3)
       => ( ( X2 = k1_xboole_0
            & X1 != k1_xboole_0 )
          | ( v1_funct_1(X4)
            & v1_funct_2(X4,X1,X3)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_2)).

fof(c_0_17,plain,(
    ! [X21,X22,X23] :
      ( ( v4_relat_1(X23,X21)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22))) )
      & ( v5_relat_1(X23,X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_18,plain,(
    ! [X6,X7] :
      ( ( ~ m1_subset_1(X6,k1_zfmisc_1(X7))
        | r1_tarski(X6,X7) )
      & ( ~ r1_tarski(X6,X7)
        | m1_subset_1(X6,k1_zfmisc_1(X7)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_19,plain,(
    ! [X18,X19,X20] :
      ( ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))
      | v1_relat_1(X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_20,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_22,plain,(
    ! [X8,X9] :
      ( ( ~ v4_relat_1(X9,X8)
        | r1_tarski(k1_relat_1(X9),X8)
        | ~ v1_relat_1(X9) )
      & ( ~ r1_tarski(k1_relat_1(X9),X8)
        | v4_relat_1(X9,X8)
        | ~ v1_relat_1(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

cnf(c_0_23,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_24,plain,(
    ! [X14] :
      ( ( k1_relat_1(X14) != k1_xboole_0
        | k2_relat_1(X14) = k1_xboole_0
        | ~ v1_relat_1(X14) )
      & ( k2_relat_1(X14) != k1_xboole_0
        | k1_relat_1(X14) = k1_xboole_0
        | ~ v1_relat_1(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_relat_1])])])).

cnf(c_0_25,plain,
    ( v4_relat_1(X1,X2)
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X3)) ),
    inference(pm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_26,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_27,plain,(
    ! [X11,X12] :
      ( v4_relat_1(k1_xboole_0,X11)
      & v5_relat_1(k1_xboole_0,X12) ) ),
    inference(variable_rename,[status(thm)],[l222_relat_1])).

fof(c_0_28,plain,(
    ! [X17] :
      ( v1_relat_1(k1_xboole_0)
      & v5_relat_1(k1_xboole_0,X17)
      & v1_funct_1(k1_xboole_0)
      & v5_ordinal1(k1_xboole_0) ) ),
    inference(variable_rename,[status(thm)],[t45_ordinal1])).

cnf(c_0_29,plain,
    ( v1_relat_1(X1)
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X3)) ),
    inference(pm,[status(thm)],[c_0_23,c_0_21])).

fof(c_0_30,negated_conjecture,(
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

fof(c_0_31,plain,(
    ! [X13] :
      ( ( k1_relat_1(X13) != k1_xboole_0
        | X13 = k1_xboole_0
        | ~ v1_relat_1(X13) )
      & ( k2_relat_1(X13) != k1_xboole_0
        | X13 = k1_xboole_0
        | ~ v1_relat_1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).

fof(c_0_32,plain,(
    ! [X16] :
      ( ( k2_relat_1(X16) = k1_relat_1(k2_funct_1(X16))
        | ~ v2_funct_1(X16)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) )
      & ( k1_relat_1(X16) = k2_relat_1(k2_funct_1(X16))
        | ~ v2_funct_1(X16)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).

cnf(c_0_33,plain,
    ( k1_relat_1(X1) = k1_xboole_0
    | k2_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,plain,
    ( v4_relat_1(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,k2_zfmisc_1(X2,X3))
    | ~ v1_relat_1(X1) ),
    inference(pm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_35,plain,
    ( v4_relat_1(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,plain,
    ( v1_relat_1(k1_relat_1(X1))
    | ~ v4_relat_1(X1,k2_zfmisc_1(X2,X3))
    | ~ v1_relat_1(X1) ),
    inference(pm,[status(thm)],[c_0_29,c_0_26])).

fof(c_0_38,negated_conjecture,
    ( v1_funct_1(esk3_0)
    & v1_funct_2(esk3_0,esk1_0,esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    & v2_funct_1(esk3_0)
    & k2_relset_1(esk1_0,esk2_0,esk3_0) = esk2_0
    & ( ~ v1_funct_1(k2_funct_1(esk3_0))
      | ~ v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)
      | ~ m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_30])])])).

cnf(c_0_39,plain,
    ( X1 = k1_xboole_0
    | k1_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_40,plain,
    ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_41,plain,(
    ! [X15] :
      ( ( v1_relat_1(k2_funct_1(X15))
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) )
      & ( v1_funct_1(k2_funct_1(X15))
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

fof(c_0_42,plain,(
    ! [X24,X25,X26] :
      ( ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))
      | k2_relset_1(X24,X25,X26) = k2_relat_1(X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_43,plain,
    ( r1_tarski(k1_xboole_0,X1)
    | k2_relat_1(X2) != k1_xboole_0
    | ~ v4_relat_1(X2,X1)
    | ~ v1_relat_1(X2) ),
    inference(pm,[status(thm)],[c_0_26,c_0_33])).

cnf(c_0_44,plain,
    ( v4_relat_1(k1_relat_1(k1_xboole_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_34,c_0_35]),c_0_36])])).

cnf(c_0_45,plain,
    ( v1_relat_1(k1_relat_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_37,c_0_35]),c_0_36])])).

fof(c_0_46,plain,(
    ! [X5] :
      ( ~ v1_xboole_0(X5)
      | X5 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

fof(c_0_47,plain,(
    ! [X10] :
      ( ~ v1_xboole_0(X10)
      | v1_xboole_0(k2_relat_1(X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc11_relat_1])])).

cnf(c_0_48,negated_conjecture,
    ( ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)
    | ~ m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_49,plain,
    ( k2_funct_1(X1) = k1_xboole_0
    | k2_relat_1(X1) != k1_xboole_0
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(pm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_50,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_51,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_53,negated_conjecture,
    ( k2_relset_1(esk1_0,esk2_0,esk3_0) = esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_54,plain,
    ( r1_tarski(k1_xboole_0,X1)
    | k2_relat_1(k1_relat_1(k1_xboole_0)) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_43,c_0_44]),c_0_45])])).

cnf(c_0_55,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_56,plain,
    ( v1_xboole_0(k2_relat_1(X1))
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

fof(c_0_57,plain,(
    ! [X27] :
      ( ( v1_funct_1(X27)
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27) )
      & ( v1_funct_2(X27,k1_relat_1(X27),k2_relat_1(X27))
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27) )
      & ( m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X27),k2_relat_1(X27))))
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).

cnf(c_0_58,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)
    | ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ r1_tarski(k2_funct_1(esk3_0),k2_zfmisc_1(esk2_0,esk1_0)) ),
    inference(pm,[status(thm)],[c_0_48,c_0_21])).

cnf(c_0_59,plain,
    ( k2_funct_1(X1) = k1_xboole_0
    | k2_relat_1(X1) != k1_xboole_0
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(pm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_60,negated_conjecture,
    ( k2_relat_1(esk3_0) = esk2_0 ),
    inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_51,c_0_52]),c_0_53])).

cnf(c_0_61,negated_conjecture,
    ( v2_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_62,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_63,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(pm,[status(thm)],[c_0_23,c_0_52])).

cnf(c_0_64,plain,
    ( r1_tarski(k1_xboole_0,X1)
    | k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_54,c_0_33]),c_0_36])])).

cnf(c_0_65,plain,
    ( k2_relat_1(X1) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(pm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_66,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

fof(c_0_67,plain,(
    ! [X28,X29,X30,X31] :
      ( ( v1_funct_1(X31)
        | X29 = k1_xboole_0
        | ~ r1_tarski(X29,X30)
        | ~ v1_funct_1(X31)
        | ~ v1_funct_2(X31,X28,X29)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X28,X29))) )
      & ( v1_funct_2(X31,X28,X30)
        | X29 = k1_xboole_0
        | ~ r1_tarski(X29,X30)
        | ~ v1_funct_1(X31)
        | ~ v1_funct_2(X31,X28,X29)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X28,X29))) )
      & ( m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X28,X30)))
        | X29 = k1_xboole_0
        | ~ r1_tarski(X29,X30)
        | ~ v1_funct_1(X31)
        | ~ v1_funct_2(X31,X28,X29)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X28,X29))) )
      & ( v1_funct_1(X31)
        | X28 != k1_xboole_0
        | ~ r1_tarski(X29,X30)
        | ~ v1_funct_1(X31)
        | ~ v1_funct_2(X31,X28,X29)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X28,X29))) )
      & ( v1_funct_2(X31,X28,X30)
        | X28 != k1_xboole_0
        | ~ r1_tarski(X29,X30)
        | ~ v1_funct_1(X31)
        | ~ v1_funct_2(X31,X28,X29)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X28,X29))) )
      & ( m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X28,X30)))
        | X28 != k1_xboole_0
        | ~ r1_tarski(X29,X30)
        | ~ v1_funct_1(X31)
        | ~ v1_funct_2(X31,X28,X29)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X28,X29))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_funct_2])])])).

cnf(c_0_68,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_69,negated_conjecture,
    ( k1_xboole_0 != esk2_0
    | ~ v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)
    | ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(esk2_0,esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_58,c_0_59]),c_0_60]),c_0_61]),c_0_62]),c_0_63])])).

cnf(c_0_70,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_64,c_0_65]),c_0_66])])).

cnf(c_0_71,plain,
    ( v1_funct_2(X1,X2,X3)
    | X2 != k1_xboole_0
    | ~ r1_tarski(X4,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_72,plain,
    ( m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(pm,[status(thm)],[c_0_68,c_0_40])).

cnf(c_0_73,plain,
    ( k2_relset_1(X1,X2,X3) = k2_relat_1(X3)
    | ~ r1_tarski(X3,k2_zfmisc_1(X1,X2)) ),
    inference(pm,[status(thm)],[c_0_51,c_0_21])).

cnf(c_0_74,negated_conjecture,
    ( k1_xboole_0 != esk2_0
    | ~ v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)
    | ~ v1_funct_1(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_70])])).

cnf(c_0_75,plain,
    ( v1_funct_2(X1,X2,X3)
    | X2 != k1_xboole_0
    | ~ v1_funct_2(X1,X2,X4)
    | ~ v1_funct_1(X1)
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X4))
    | ~ r1_tarski(X4,X3) ),
    inference(pm,[status(thm)],[c_0_71,c_0_21])).

cnf(c_0_76,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_77,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,k2_relat_1(k2_funct_1(esk3_0)))))
    | ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_72,c_0_60]),c_0_61]),c_0_62]),c_0_63])])).

cnf(c_0_78,plain,
    ( k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_79,plain,
    ( X1 = k1_xboole_0
    | k2_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_80,plain,
    ( k2_relset_1(X1,X2,k1_xboole_0) = k2_relat_1(k1_xboole_0) ),
    inference(pm,[status(thm)],[c_0_73,c_0_70])).

cnf(c_0_81,negated_conjecture,
    ( k1_xboole_0 != esk2_0
    | ~ v1_funct_2(k2_funct_1(esk3_0),esk2_0,X1)
    | ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ r1_tarski(k2_funct_1(esk3_0),k2_zfmisc_1(esk2_0,X1))
    | ~ r1_tarski(X1,esk1_0) ),
    inference(pm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_82,plain,
    ( v1_funct_2(k2_funct_1(X1),k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(pm,[status(thm)],[c_0_76,c_0_40])).

cnf(c_0_83,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,k1_relat_1(esk3_0))))
    | ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_77,c_0_78]),c_0_61]),c_0_62]),c_0_63])])).

cnf(c_0_84,plain,
    ( k2_funct_1(X1) = k1_xboole_0
    | k1_relat_1(X1) != k1_xboole_0
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(pm,[status(thm)],[c_0_79,c_0_78])).

cnf(c_0_85,plain,
    ( v1_xboole_0(k2_relset_1(X1,X2,k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_56,c_0_80]),c_0_66])])).

cnf(c_0_86,negated_conjecture,
    ( k1_xboole_0 != esk2_0
    | ~ v1_funct_2(k2_funct_1(esk3_0),esk2_0,X1)
    | ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ r1_tarski(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_81,c_0_59]),c_0_70]),c_0_60]),c_0_61]),c_0_62]),c_0_63])])).

cnf(c_0_87,plain,
    ( v1_funct_1(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_88,negated_conjecture,
    ( v1_funct_2(k2_funct_1(esk3_0),esk2_0,k2_relat_1(k2_funct_1(esk3_0)))
    | ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_82,c_0_60]),c_0_61]),c_0_62]),c_0_63])])).

cnf(c_0_89,negated_conjecture,
    ( k2_relset_1(esk2_0,k1_relat_1(esk3_0),k2_funct_1(esk3_0)) = k2_relat_1(k2_funct_1(esk3_0))
    | ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(pm,[status(thm)],[c_0_51,c_0_83])).

cnf(c_0_90,plain,
    ( k2_funct_1(X1) = k1_xboole_0
    | k1_relat_1(X1) != k1_xboole_0
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(pm,[status(thm)],[c_0_84,c_0_50])).

cnf(c_0_91,plain,
    ( k2_relset_1(X1,X2,k1_xboole_0) = k1_xboole_0 ),
    inference(pm,[status(thm)],[c_0_55,c_0_85])).

cnf(c_0_92,negated_conjecture,
    ( k1_xboole_0 != esk2_0
    | ~ v1_funct_2(k2_funct_1(esk3_0),esk2_0,X1)
    | ~ r1_tarski(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_86,c_0_59]),c_0_87]),c_0_60]),c_0_61]),c_0_62]),c_0_63])])).

cnf(c_0_93,negated_conjecture,
    ( v1_funct_2(k2_funct_1(esk3_0),esk2_0,k1_relat_1(esk3_0))
    | ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_88,c_0_78]),c_0_61]),c_0_62]),c_0_63])])).

cnf(c_0_94,negated_conjecture,
    ( k2_relat_1(k2_funct_1(esk3_0)) = k1_xboole_0
    | k1_relat_1(esk3_0) != k1_xboole_0
    | ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_89,c_0_90]),c_0_91]),c_0_61]),c_0_62]),c_0_63])])).

cnf(c_0_95,negated_conjecture,
    ( k1_xboole_0 != esk2_0
    | ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ v1_relat_1(k2_funct_1(esk3_0))
    | ~ r1_tarski(k1_relat_1(esk3_0),esk1_0) ),
    inference(pm,[status(thm)],[c_0_92,c_0_93])).

cnf(c_0_96,negated_conjecture,
    ( k2_funct_1(esk3_0) = k1_xboole_0
    | k1_relat_1(esk3_0) != k1_xboole_0
    | ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(pm,[status(thm)],[c_0_79,c_0_94])).

cnf(c_0_97,negated_conjecture,
    ( k1_xboole_0 != esk2_0
    | ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_95,c_0_33]),c_0_70]),c_0_60]),c_0_63])])).

cnf(c_0_98,negated_conjecture,
    ( k2_funct_1(esk3_0) = k1_xboole_0
    | k1_relat_1(esk3_0) != k1_xboole_0
    | ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_96,c_0_90]),c_0_87]),c_0_61]),c_0_62]),c_0_63])])).

cnf(c_0_99,plain,
    ( v1_xboole_0(k2_relat_1(k1_xboole_0)) ),
    inference(pm,[status(thm)],[c_0_85,c_0_80])).

cnf(c_0_100,negated_conjecture,
    ( k1_xboole_0 != esk2_0
    | ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_97,c_0_59]),c_0_87]),c_0_60]),c_0_61]),c_0_62]),c_0_63])])).

cnf(c_0_101,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | X4 = k1_xboole_0
    | ~ r1_tarski(X4,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_102,plain,
    ( k2_relat_1(X1) = k1_xboole_0
    | k2_relat_1(k2_funct_1(X1)) != k1_xboole_0
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(pm,[status(thm)],[c_0_33,c_0_40])).

cnf(c_0_103,negated_conjecture,
    ( k2_funct_1(esk3_0) = k1_xboole_0
    | k1_relat_1(esk3_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_98,c_0_90]),c_0_36]),c_0_61]),c_0_62]),c_0_63])])).

cnf(c_0_104,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(pm,[status(thm)],[c_0_55,c_0_99])).

cnf(c_0_105,negated_conjecture,
    ( k1_xboole_0 != esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_100,c_0_59]),c_0_36]),c_0_60]),c_0_61]),c_0_62]),c_0_63])])).

cnf(c_0_106,negated_conjecture,
    ( X1 = k1_xboole_0
    | ~ v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)
    | ~ v1_funct_2(k2_funct_1(esk3_0),esk2_0,X1)
    | ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ r1_tarski(X1,esk1_0)
    | ~ m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,X1))) ),
    inference(pm,[status(thm)],[c_0_48,c_0_101])).

cnf(c_0_107,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_108,negated_conjecture,
    ( k1_relat_1(esk3_0) != k1_xboole_0
    | ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_102,c_0_103]),c_0_60]),c_0_104]),c_0_61]),c_0_62]),c_0_63])]),c_0_105])).

cnf(c_0_109,negated_conjecture,
    ( X1 = k1_xboole_0
    | ~ v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)
    | ~ v1_funct_2(k2_funct_1(esk3_0),esk2_0,X1)
    | ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ r1_tarski(k2_funct_1(esk3_0),k2_zfmisc_1(esk2_0,X1))
    | ~ r1_tarski(X1,esk1_0) ),
    inference(pm,[status(thm)],[c_0_106,c_0_21])).

cnf(c_0_110,negated_conjecture,
    ( r1_tarski(k2_funct_1(esk3_0),k2_zfmisc_1(esk2_0,k1_relat_1(esk3_0)))
    | ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(pm,[status(thm)],[c_0_107,c_0_83])).

cnf(c_0_111,negated_conjecture,
    ( k1_relat_1(esk3_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_108,c_0_90]),c_0_36]),c_0_61]),c_0_62]),c_0_63])])).

cnf(c_0_112,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(esk3_0),esk2_0,k1_relat_1(esk3_0))
    | ~ v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)
    | ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ v1_relat_1(k2_funct_1(esk3_0))
    | ~ r1_tarski(k1_relat_1(esk3_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(pm,[status(thm)],[c_0_109,c_0_110]),c_0_111])).

cnf(c_0_113,plain,
    ( v1_funct_2(X1,X2,X3)
    | X4 = k1_xboole_0
    | ~ r1_tarski(X4,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_114,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)
    | ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ v1_relat_1(k2_funct_1(esk3_0))
    | ~ r1_tarski(k1_relat_1(esk3_0),esk1_0) ),
    inference(pm,[status(thm)],[c_0_112,c_0_93])).

cnf(c_0_115,plain,
    ( X1 = k1_xboole_0
    | v1_funct_2(X2,X3,X4)
    | ~ v1_funct_2(X2,X3,X1)
    | ~ v1_funct_1(X2)
    | ~ r1_tarski(X2,k2_zfmisc_1(X3,X1))
    | ~ r1_tarski(X1,X4) ),
    inference(pm,[status(thm)],[c_0_113,c_0_21])).

cnf(c_0_116,negated_conjecture,
    ( X1 = k1_xboole_0
    | ~ v1_funct_2(k2_funct_1(esk3_0),esk2_0,X1)
    | ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ v1_relat_1(k2_funct_1(esk3_0))
    | ~ r1_tarski(k2_funct_1(esk3_0),k2_zfmisc_1(esk2_0,X1))
    | ~ r1_tarski(k1_relat_1(esk3_0),esk1_0)
    | ~ r1_tarski(X1,esk1_0) ),
    inference(pm,[status(thm)],[c_0_114,c_0_115])).

cnf(c_0_117,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(esk3_0),esk2_0,k1_relat_1(esk3_0))
    | ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ v1_relat_1(k2_funct_1(esk3_0))
    | ~ r1_tarski(k1_relat_1(esk3_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(pm,[status(thm)],[c_0_116,c_0_110]),c_0_111])).

cnf(c_0_118,negated_conjecture,
    ( ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ v1_relat_1(k2_funct_1(esk3_0))
    | ~ r1_tarski(k1_relat_1(esk3_0),esk1_0) ),
    inference(pm,[status(thm)],[c_0_117,c_0_93])).

cnf(c_0_119,negated_conjecture,
    ( v4_relat_1(esk3_0,esk1_0) ),
    inference(pm,[status(thm)],[c_0_20,c_0_52])).

cnf(c_0_120,negated_conjecture,
    ( ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_118,c_0_26]),c_0_119]),c_0_63])])).

cnf(c_0_121,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_122,negated_conjecture,
    ( ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_120,c_0_121]),c_0_62]),c_0_63])])).

cnf(c_0_123,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_122,c_0_50]),c_0_62]),c_0_63])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:27:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.51  # AutoSched0-Mode selected heuristic G_E___300_C01_S00
% 0.20/0.51  # and selection function NoSelection.
% 0.20/0.51  #
% 0.20/0.51  # Preprocessing time       : 0.029 s
% 0.20/0.51  
% 0.20/0.51  # Proof found!
% 0.20/0.51  # SZS status Theorem
% 0.20/0.51  # SZS output start CNFRefutation
% 0.20/0.51  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.20/0.51  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.51  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.20/0.51  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 0.20/0.51  fof(t65_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>(k1_relat_1(X1)=k1_xboole_0<=>k2_relat_1(X1)=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 0.20/0.51  fof(l222_relat_1, axiom, ![X1, X2]:(v4_relat_1(k1_xboole_0,X1)&v5_relat_1(k1_xboole_0,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l222_relat_1)).
% 0.20/0.51  fof(t45_ordinal1, axiom, ![X1]:(((v1_relat_1(k1_xboole_0)&v5_relat_1(k1_xboole_0,X1))&v1_funct_1(k1_xboole_0))&v5_ordinal1(k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_ordinal1)).
% 0.20/0.51  fof(t31_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v2_funct_1(X3)&k2_relset_1(X1,X2,X3)=X2)=>((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),X2,X1))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 0.20/0.51  fof(t64_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>((k1_relat_1(X1)=k1_xboole_0|k2_relat_1(X1)=k1_xboole_0)=>X1=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 0.20/0.51  fof(t55_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))&k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 0.20/0.51  fof(dt_k2_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k2_funct_1(X1))&v1_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 0.20/0.51  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.20/0.51  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.20/0.51  fof(fc11_relat_1, axiom, ![X1]:(v1_xboole_0(X1)=>v1_xboole_0(k2_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc11_relat_1)).
% 0.20/0.51  fof(t3_funct_2, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>((v1_funct_1(X1)&v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1)))&m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 0.20/0.51  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.20/0.51  fof(t9_funct_2, axiom, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_tarski(X2,X3)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|((v1_funct_1(X4)&v1_funct_2(X4,X1,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_funct_2)).
% 0.20/0.51  fof(c_0_17, plain, ![X21, X22, X23]:((v4_relat_1(X23,X21)|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22))))&(v5_relat_1(X23,X22)|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.20/0.51  fof(c_0_18, plain, ![X6, X7]:((~m1_subset_1(X6,k1_zfmisc_1(X7))|r1_tarski(X6,X7))&(~r1_tarski(X6,X7)|m1_subset_1(X6,k1_zfmisc_1(X7)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.51  fof(c_0_19, plain, ![X18, X19, X20]:(~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))|v1_relat_1(X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.20/0.51  cnf(c_0_20, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.51  cnf(c_0_21, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.51  fof(c_0_22, plain, ![X8, X9]:((~v4_relat_1(X9,X8)|r1_tarski(k1_relat_1(X9),X8)|~v1_relat_1(X9))&(~r1_tarski(k1_relat_1(X9),X8)|v4_relat_1(X9,X8)|~v1_relat_1(X9))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 0.20/0.51  cnf(c_0_23, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.51  fof(c_0_24, plain, ![X14]:((k1_relat_1(X14)!=k1_xboole_0|k2_relat_1(X14)=k1_xboole_0|~v1_relat_1(X14))&(k2_relat_1(X14)!=k1_xboole_0|k1_relat_1(X14)=k1_xboole_0|~v1_relat_1(X14))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_relat_1])])])).
% 0.20/0.51  cnf(c_0_25, plain, (v4_relat_1(X1,X2)|~r1_tarski(X1,k2_zfmisc_1(X2,X3))), inference(pm,[status(thm)],[c_0_20, c_0_21])).
% 0.20/0.51  cnf(c_0_26, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.51  fof(c_0_27, plain, ![X11, X12]:(v4_relat_1(k1_xboole_0,X11)&v5_relat_1(k1_xboole_0,X12)), inference(variable_rename,[status(thm)],[l222_relat_1])).
% 0.20/0.51  fof(c_0_28, plain, ![X17]:(((v1_relat_1(k1_xboole_0)&v5_relat_1(k1_xboole_0,X17))&v1_funct_1(k1_xboole_0))&v5_ordinal1(k1_xboole_0)), inference(variable_rename,[status(thm)],[t45_ordinal1])).
% 0.20/0.51  cnf(c_0_29, plain, (v1_relat_1(X1)|~r1_tarski(X1,k2_zfmisc_1(X2,X3))), inference(pm,[status(thm)],[c_0_23, c_0_21])).
% 0.20/0.51  fof(c_0_30, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v2_funct_1(X3)&k2_relset_1(X1,X2,X3)=X2)=>((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),X2,X1))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))))))), inference(assume_negation,[status(cth)],[t31_funct_2])).
% 0.20/0.51  fof(c_0_31, plain, ![X13]:((k1_relat_1(X13)!=k1_xboole_0|X13=k1_xboole_0|~v1_relat_1(X13))&(k2_relat_1(X13)!=k1_xboole_0|X13=k1_xboole_0|~v1_relat_1(X13))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).
% 0.20/0.51  fof(c_0_32, plain, ![X16]:((k2_relat_1(X16)=k1_relat_1(k2_funct_1(X16))|~v2_funct_1(X16)|(~v1_relat_1(X16)|~v1_funct_1(X16)))&(k1_relat_1(X16)=k2_relat_1(k2_funct_1(X16))|~v2_funct_1(X16)|(~v1_relat_1(X16)|~v1_funct_1(X16)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).
% 0.20/0.51  cnf(c_0_33, plain, (k1_relat_1(X1)=k1_xboole_0|k2_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.51  cnf(c_0_34, plain, (v4_relat_1(k1_relat_1(X1),X2)|~v4_relat_1(X1,k2_zfmisc_1(X2,X3))|~v1_relat_1(X1)), inference(pm,[status(thm)],[c_0_25, c_0_26])).
% 0.20/0.51  cnf(c_0_35, plain, (v4_relat_1(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.51  cnf(c_0_36, plain, (v1_relat_1(k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.51  cnf(c_0_37, plain, (v1_relat_1(k1_relat_1(X1))|~v4_relat_1(X1,k2_zfmisc_1(X2,X3))|~v1_relat_1(X1)), inference(pm,[status(thm)],[c_0_29, c_0_26])).
% 0.20/0.51  fof(c_0_38, negated_conjecture, (((v1_funct_1(esk3_0)&v1_funct_2(esk3_0,esk1_0,esk2_0))&m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))))&((v2_funct_1(esk3_0)&k2_relset_1(esk1_0,esk2_0,esk3_0)=esk2_0)&(~v1_funct_1(k2_funct_1(esk3_0))|~v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)|~m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_30])])])).
% 0.20/0.51  cnf(c_0_39, plain, (X1=k1_xboole_0|k1_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.51  cnf(c_0_40, plain, (k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.51  fof(c_0_41, plain, ![X15]:((v1_relat_1(k2_funct_1(X15))|(~v1_relat_1(X15)|~v1_funct_1(X15)))&(v1_funct_1(k2_funct_1(X15))|(~v1_relat_1(X15)|~v1_funct_1(X15)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).
% 0.20/0.51  fof(c_0_42, plain, ![X24, X25, X26]:(~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))|k2_relset_1(X24,X25,X26)=k2_relat_1(X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.20/0.51  cnf(c_0_43, plain, (r1_tarski(k1_xboole_0,X1)|k2_relat_1(X2)!=k1_xboole_0|~v4_relat_1(X2,X1)|~v1_relat_1(X2)), inference(pm,[status(thm)],[c_0_26, c_0_33])).
% 0.20/0.51  cnf(c_0_44, plain, (v4_relat_1(k1_relat_1(k1_xboole_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_34, c_0_35]), c_0_36])])).
% 0.20/0.51  cnf(c_0_45, plain, (v1_relat_1(k1_relat_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_37, c_0_35]), c_0_36])])).
% 0.20/0.51  fof(c_0_46, plain, ![X5]:(~v1_xboole_0(X5)|X5=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.20/0.51  fof(c_0_47, plain, ![X10]:(~v1_xboole_0(X10)|v1_xboole_0(k2_relat_1(X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc11_relat_1])])).
% 0.20/0.51  cnf(c_0_48, negated_conjecture, (~v1_funct_1(k2_funct_1(esk3_0))|~v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)|~m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.51  cnf(c_0_49, plain, (k2_funct_1(X1)=k1_xboole_0|k2_relat_1(X1)!=k1_xboole_0|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)), inference(pm,[status(thm)],[c_0_39, c_0_40])).
% 0.20/0.51  cnf(c_0_50, plain, (v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.20/0.51  cnf(c_0_51, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.51  cnf(c_0_52, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.51  cnf(c_0_53, negated_conjecture, (k2_relset_1(esk1_0,esk2_0,esk3_0)=esk2_0), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.51  cnf(c_0_54, plain, (r1_tarski(k1_xboole_0,X1)|k2_relat_1(k1_relat_1(k1_xboole_0))!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_43, c_0_44]), c_0_45])])).
% 0.20/0.51  cnf(c_0_55, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.20/0.51  cnf(c_0_56, plain, (v1_xboole_0(k2_relat_1(X1))|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.20/0.51  fof(c_0_57, plain, ![X27]:(((v1_funct_1(X27)|(~v1_relat_1(X27)|~v1_funct_1(X27)))&(v1_funct_2(X27,k1_relat_1(X27),k2_relat_1(X27))|(~v1_relat_1(X27)|~v1_funct_1(X27))))&(m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X27),k2_relat_1(X27))))|(~v1_relat_1(X27)|~v1_funct_1(X27)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).
% 0.20/0.51  cnf(c_0_58, negated_conjecture, (~v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)|~v1_funct_1(k2_funct_1(esk3_0))|~r1_tarski(k2_funct_1(esk3_0),k2_zfmisc_1(esk2_0,esk1_0))), inference(pm,[status(thm)],[c_0_48, c_0_21])).
% 0.20/0.51  cnf(c_0_59, plain, (k2_funct_1(X1)=k1_xboole_0|k2_relat_1(X1)!=k1_xboole_0|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(pm,[status(thm)],[c_0_49, c_0_50])).
% 0.20/0.51  cnf(c_0_60, negated_conjecture, (k2_relat_1(esk3_0)=esk2_0), inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_51, c_0_52]), c_0_53])).
% 0.20/0.51  cnf(c_0_61, negated_conjecture, (v2_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.51  cnf(c_0_62, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.51  cnf(c_0_63, negated_conjecture, (v1_relat_1(esk3_0)), inference(pm,[status(thm)],[c_0_23, c_0_52])).
% 0.20/0.51  cnf(c_0_64, plain, (r1_tarski(k1_xboole_0,X1)|k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_54, c_0_33]), c_0_36])])).
% 0.20/0.51  cnf(c_0_65, plain, (k2_relat_1(X1)=k1_xboole_0|~v1_xboole_0(X1)), inference(pm,[status(thm)],[c_0_55, c_0_56])).
% 0.20/0.51  cnf(c_0_66, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.20/0.51  fof(c_0_67, plain, ![X28, X29, X30, X31]:((((v1_funct_1(X31)|X29=k1_xboole_0|~r1_tarski(X29,X30)|(~v1_funct_1(X31)|~v1_funct_2(X31,X28,X29)|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))))&(v1_funct_2(X31,X28,X30)|X29=k1_xboole_0|~r1_tarski(X29,X30)|(~v1_funct_1(X31)|~v1_funct_2(X31,X28,X29)|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X28,X29))))))&(m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X28,X30)))|X29=k1_xboole_0|~r1_tarski(X29,X30)|(~v1_funct_1(X31)|~v1_funct_2(X31,X28,X29)|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X28,X29))))))&(((v1_funct_1(X31)|X28!=k1_xboole_0|~r1_tarski(X29,X30)|(~v1_funct_1(X31)|~v1_funct_2(X31,X28,X29)|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))))&(v1_funct_2(X31,X28,X30)|X28!=k1_xboole_0|~r1_tarski(X29,X30)|(~v1_funct_1(X31)|~v1_funct_2(X31,X28,X29)|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X28,X29))))))&(m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X28,X30)))|X28!=k1_xboole_0|~r1_tarski(X29,X30)|(~v1_funct_1(X31)|~v1_funct_2(X31,X28,X29)|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X28,X29))))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_funct_2])])])).
% 0.20/0.51  cnf(c_0_68, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.20/0.51  cnf(c_0_69, negated_conjecture, (k1_xboole_0!=esk2_0|~v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)|~v1_funct_1(k2_funct_1(esk3_0))|~r1_tarski(k1_xboole_0,k2_zfmisc_1(esk2_0,esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_58, c_0_59]), c_0_60]), c_0_61]), c_0_62]), c_0_63])])).
% 0.20/0.51  cnf(c_0_70, plain, (r1_tarski(k1_xboole_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_64, c_0_65]), c_0_66])])).
% 0.20/0.51  cnf(c_0_71, plain, (v1_funct_2(X1,X2,X3)|X2!=k1_xboole_0|~r1_tarski(X4,X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.20/0.51  cnf(c_0_72, plain, (m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(X1))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)), inference(pm,[status(thm)],[c_0_68, c_0_40])).
% 0.20/0.51  cnf(c_0_73, plain, (k2_relset_1(X1,X2,X3)=k2_relat_1(X3)|~r1_tarski(X3,k2_zfmisc_1(X1,X2))), inference(pm,[status(thm)],[c_0_51, c_0_21])).
% 0.20/0.51  cnf(c_0_74, negated_conjecture, (k1_xboole_0!=esk2_0|~v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)|~v1_funct_1(k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_69, c_0_70])])).
% 0.20/0.51  cnf(c_0_75, plain, (v1_funct_2(X1,X2,X3)|X2!=k1_xboole_0|~v1_funct_2(X1,X2,X4)|~v1_funct_1(X1)|~r1_tarski(X1,k2_zfmisc_1(X2,X4))|~r1_tarski(X4,X3)), inference(pm,[status(thm)],[c_0_71, c_0_21])).
% 0.20/0.51  cnf(c_0_76, plain, (v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.20/0.51  cnf(c_0_77, negated_conjecture, (m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,k2_relat_1(k2_funct_1(esk3_0)))))|~v1_funct_1(k2_funct_1(esk3_0))|~v1_relat_1(k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_72, c_0_60]), c_0_61]), c_0_62]), c_0_63])])).
% 0.20/0.51  cnf(c_0_78, plain, (k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.51  cnf(c_0_79, plain, (X1=k1_xboole_0|k2_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.51  cnf(c_0_80, plain, (k2_relset_1(X1,X2,k1_xboole_0)=k2_relat_1(k1_xboole_0)), inference(pm,[status(thm)],[c_0_73, c_0_70])).
% 0.20/0.51  cnf(c_0_81, negated_conjecture, (k1_xboole_0!=esk2_0|~v1_funct_2(k2_funct_1(esk3_0),esk2_0,X1)|~v1_funct_1(k2_funct_1(esk3_0))|~r1_tarski(k2_funct_1(esk3_0),k2_zfmisc_1(esk2_0,X1))|~r1_tarski(X1,esk1_0)), inference(pm,[status(thm)],[c_0_74, c_0_75])).
% 0.20/0.51  cnf(c_0_82, plain, (v1_funct_2(k2_funct_1(X1),k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(X1))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)), inference(pm,[status(thm)],[c_0_76, c_0_40])).
% 0.20/0.51  cnf(c_0_83, negated_conjecture, (m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,k1_relat_1(esk3_0))))|~v1_funct_1(k2_funct_1(esk3_0))|~v1_relat_1(k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_77, c_0_78]), c_0_61]), c_0_62]), c_0_63])])).
% 0.20/0.51  cnf(c_0_84, plain, (k2_funct_1(X1)=k1_xboole_0|k1_relat_1(X1)!=k1_xboole_0|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)), inference(pm,[status(thm)],[c_0_79, c_0_78])).
% 0.20/0.51  cnf(c_0_85, plain, (v1_xboole_0(k2_relset_1(X1,X2,k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_56, c_0_80]), c_0_66])])).
% 0.20/0.51  cnf(c_0_86, negated_conjecture, (k1_xboole_0!=esk2_0|~v1_funct_2(k2_funct_1(esk3_0),esk2_0,X1)|~v1_funct_1(k2_funct_1(esk3_0))|~r1_tarski(X1,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_81, c_0_59]), c_0_70]), c_0_60]), c_0_61]), c_0_62]), c_0_63])])).
% 0.20/0.51  cnf(c_0_87, plain, (v1_funct_1(k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.51  cnf(c_0_88, negated_conjecture, (v1_funct_2(k2_funct_1(esk3_0),esk2_0,k2_relat_1(k2_funct_1(esk3_0)))|~v1_funct_1(k2_funct_1(esk3_0))|~v1_relat_1(k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_82, c_0_60]), c_0_61]), c_0_62]), c_0_63])])).
% 0.20/0.51  cnf(c_0_89, negated_conjecture, (k2_relset_1(esk2_0,k1_relat_1(esk3_0),k2_funct_1(esk3_0))=k2_relat_1(k2_funct_1(esk3_0))|~v1_funct_1(k2_funct_1(esk3_0))|~v1_relat_1(k2_funct_1(esk3_0))), inference(pm,[status(thm)],[c_0_51, c_0_83])).
% 0.20/0.51  cnf(c_0_90, plain, (k2_funct_1(X1)=k1_xboole_0|k1_relat_1(X1)!=k1_xboole_0|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(pm,[status(thm)],[c_0_84, c_0_50])).
% 0.20/0.51  cnf(c_0_91, plain, (k2_relset_1(X1,X2,k1_xboole_0)=k1_xboole_0), inference(pm,[status(thm)],[c_0_55, c_0_85])).
% 0.20/0.51  cnf(c_0_92, negated_conjecture, (k1_xboole_0!=esk2_0|~v1_funct_2(k2_funct_1(esk3_0),esk2_0,X1)|~r1_tarski(X1,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_86, c_0_59]), c_0_87]), c_0_60]), c_0_61]), c_0_62]), c_0_63])])).
% 0.20/0.51  cnf(c_0_93, negated_conjecture, (v1_funct_2(k2_funct_1(esk3_0),esk2_0,k1_relat_1(esk3_0))|~v1_funct_1(k2_funct_1(esk3_0))|~v1_relat_1(k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_88, c_0_78]), c_0_61]), c_0_62]), c_0_63])])).
% 0.20/0.51  cnf(c_0_94, negated_conjecture, (k2_relat_1(k2_funct_1(esk3_0))=k1_xboole_0|k1_relat_1(esk3_0)!=k1_xboole_0|~v1_funct_1(k2_funct_1(esk3_0))|~v1_relat_1(k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_89, c_0_90]), c_0_91]), c_0_61]), c_0_62]), c_0_63])])).
% 0.20/0.51  cnf(c_0_95, negated_conjecture, (k1_xboole_0!=esk2_0|~v1_funct_1(k2_funct_1(esk3_0))|~v1_relat_1(k2_funct_1(esk3_0))|~r1_tarski(k1_relat_1(esk3_0),esk1_0)), inference(pm,[status(thm)],[c_0_92, c_0_93])).
% 0.20/0.51  cnf(c_0_96, negated_conjecture, (k2_funct_1(esk3_0)=k1_xboole_0|k1_relat_1(esk3_0)!=k1_xboole_0|~v1_funct_1(k2_funct_1(esk3_0))|~v1_relat_1(k2_funct_1(esk3_0))), inference(pm,[status(thm)],[c_0_79, c_0_94])).
% 0.20/0.51  cnf(c_0_97, negated_conjecture, (k1_xboole_0!=esk2_0|~v1_funct_1(k2_funct_1(esk3_0))|~v1_relat_1(k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_95, c_0_33]), c_0_70]), c_0_60]), c_0_63])])).
% 0.20/0.51  cnf(c_0_98, negated_conjecture, (k2_funct_1(esk3_0)=k1_xboole_0|k1_relat_1(esk3_0)!=k1_xboole_0|~v1_relat_1(k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_96, c_0_90]), c_0_87]), c_0_61]), c_0_62]), c_0_63])])).
% 0.20/0.51  cnf(c_0_99, plain, (v1_xboole_0(k2_relat_1(k1_xboole_0))), inference(pm,[status(thm)],[c_0_85, c_0_80])).
% 0.20/0.51  cnf(c_0_100, negated_conjecture, (k1_xboole_0!=esk2_0|~v1_relat_1(k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_97, c_0_59]), c_0_87]), c_0_60]), c_0_61]), c_0_62]), c_0_63])])).
% 0.20/0.51  cnf(c_0_101, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|X4=k1_xboole_0|~r1_tarski(X4,X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.20/0.51  cnf(c_0_102, plain, (k2_relat_1(X1)=k1_xboole_0|k2_relat_1(k2_funct_1(X1))!=k1_xboole_0|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)), inference(pm,[status(thm)],[c_0_33, c_0_40])).
% 0.20/0.51  cnf(c_0_103, negated_conjecture, (k2_funct_1(esk3_0)=k1_xboole_0|k1_relat_1(esk3_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_98, c_0_90]), c_0_36]), c_0_61]), c_0_62]), c_0_63])])).
% 0.20/0.51  cnf(c_0_104, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(pm,[status(thm)],[c_0_55, c_0_99])).
% 0.20/0.51  cnf(c_0_105, negated_conjecture, (k1_xboole_0!=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_100, c_0_59]), c_0_36]), c_0_60]), c_0_61]), c_0_62]), c_0_63])])).
% 0.20/0.51  cnf(c_0_106, negated_conjecture, (X1=k1_xboole_0|~v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)|~v1_funct_2(k2_funct_1(esk3_0),esk2_0,X1)|~v1_funct_1(k2_funct_1(esk3_0))|~r1_tarski(X1,esk1_0)|~m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,X1)))), inference(pm,[status(thm)],[c_0_48, c_0_101])).
% 0.20/0.51  cnf(c_0_107, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.51  cnf(c_0_108, negated_conjecture, (k1_relat_1(esk3_0)!=k1_xboole_0|~v1_relat_1(k2_funct_1(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_102, c_0_103]), c_0_60]), c_0_104]), c_0_61]), c_0_62]), c_0_63])]), c_0_105])).
% 0.20/0.51  cnf(c_0_109, negated_conjecture, (X1=k1_xboole_0|~v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)|~v1_funct_2(k2_funct_1(esk3_0),esk2_0,X1)|~v1_funct_1(k2_funct_1(esk3_0))|~r1_tarski(k2_funct_1(esk3_0),k2_zfmisc_1(esk2_0,X1))|~r1_tarski(X1,esk1_0)), inference(pm,[status(thm)],[c_0_106, c_0_21])).
% 0.20/0.51  cnf(c_0_110, negated_conjecture, (r1_tarski(k2_funct_1(esk3_0),k2_zfmisc_1(esk2_0,k1_relat_1(esk3_0)))|~v1_funct_1(k2_funct_1(esk3_0))|~v1_relat_1(k2_funct_1(esk3_0))), inference(pm,[status(thm)],[c_0_107, c_0_83])).
% 0.20/0.51  cnf(c_0_111, negated_conjecture, (k1_relat_1(esk3_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_108, c_0_90]), c_0_36]), c_0_61]), c_0_62]), c_0_63])])).
% 0.20/0.51  cnf(c_0_112, negated_conjecture, (~v1_funct_2(k2_funct_1(esk3_0),esk2_0,k1_relat_1(esk3_0))|~v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)|~v1_funct_1(k2_funct_1(esk3_0))|~v1_relat_1(k2_funct_1(esk3_0))|~r1_tarski(k1_relat_1(esk3_0),esk1_0)), inference(sr,[status(thm)],[inference(pm,[status(thm)],[c_0_109, c_0_110]), c_0_111])).
% 0.20/0.51  cnf(c_0_113, plain, (v1_funct_2(X1,X2,X3)|X4=k1_xboole_0|~r1_tarski(X4,X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.20/0.51  cnf(c_0_114, negated_conjecture, (~v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)|~v1_funct_1(k2_funct_1(esk3_0))|~v1_relat_1(k2_funct_1(esk3_0))|~r1_tarski(k1_relat_1(esk3_0),esk1_0)), inference(pm,[status(thm)],[c_0_112, c_0_93])).
% 0.20/0.51  cnf(c_0_115, plain, (X1=k1_xboole_0|v1_funct_2(X2,X3,X4)|~v1_funct_2(X2,X3,X1)|~v1_funct_1(X2)|~r1_tarski(X2,k2_zfmisc_1(X3,X1))|~r1_tarski(X1,X4)), inference(pm,[status(thm)],[c_0_113, c_0_21])).
% 0.20/0.51  cnf(c_0_116, negated_conjecture, (X1=k1_xboole_0|~v1_funct_2(k2_funct_1(esk3_0),esk2_0,X1)|~v1_funct_1(k2_funct_1(esk3_0))|~v1_relat_1(k2_funct_1(esk3_0))|~r1_tarski(k2_funct_1(esk3_0),k2_zfmisc_1(esk2_0,X1))|~r1_tarski(k1_relat_1(esk3_0),esk1_0)|~r1_tarski(X1,esk1_0)), inference(pm,[status(thm)],[c_0_114, c_0_115])).
% 0.20/0.51  cnf(c_0_117, negated_conjecture, (~v1_funct_2(k2_funct_1(esk3_0),esk2_0,k1_relat_1(esk3_0))|~v1_funct_1(k2_funct_1(esk3_0))|~v1_relat_1(k2_funct_1(esk3_0))|~r1_tarski(k1_relat_1(esk3_0),esk1_0)), inference(sr,[status(thm)],[inference(pm,[status(thm)],[c_0_116, c_0_110]), c_0_111])).
% 0.20/0.51  cnf(c_0_118, negated_conjecture, (~v1_funct_1(k2_funct_1(esk3_0))|~v1_relat_1(k2_funct_1(esk3_0))|~r1_tarski(k1_relat_1(esk3_0),esk1_0)), inference(pm,[status(thm)],[c_0_117, c_0_93])).
% 0.20/0.51  cnf(c_0_119, negated_conjecture, (v4_relat_1(esk3_0,esk1_0)), inference(pm,[status(thm)],[c_0_20, c_0_52])).
% 0.20/0.51  cnf(c_0_120, negated_conjecture, (~v1_funct_1(k2_funct_1(esk3_0))|~v1_relat_1(k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_118, c_0_26]), c_0_119]), c_0_63])])).
% 0.20/0.51  cnf(c_0_121, plain, (v1_funct_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.20/0.51  cnf(c_0_122, negated_conjecture, (~v1_relat_1(k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_120, c_0_121]), c_0_62]), c_0_63])])).
% 0.20/0.51  cnf(c_0_123, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_122, c_0_50]), c_0_62]), c_0_63])]), ['proof']).
% 0.20/0.51  # SZS output end CNFRefutation
% 0.20/0.51  # Proof object total steps             : 124
% 0.20/0.51  # Proof object clause steps            : 90
% 0.20/0.51  # Proof object formula steps           : 34
% 0.20/0.51  # Proof object conjectures             : 43
% 0.20/0.51  # Proof object clause conjectures      : 40
% 0.20/0.51  # Proof object formula conjectures     : 3
% 0.20/0.51  # Proof object initial clauses used    : 29
% 0.20/0.51  # Proof object initial formulas used   : 17
% 0.20/0.51  # Proof object generating inferences   : 60
% 0.20/0.51  # Proof object simplifying inferences  : 102
% 0.20/0.51  # Training examples: 0 positive, 0 negative
% 0.20/0.51  # Parsed axioms                        : 17
% 0.20/0.51  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.51  # Initial clauses                      : 40
% 0.20/0.51  # Removed in clause preprocessing      : 3
% 0.20/0.51  # Initial clauses in saturation        : 37
% 0.20/0.51  # Processed clauses                    : 1293
% 0.20/0.51  # ...of these trivial                  : 13
% 0.20/0.51  # ...subsumed                          : 763
% 0.20/0.51  # ...remaining for further processing  : 517
% 0.20/0.51  # Other redundant clauses eliminated   : 0
% 0.20/0.51  # Clauses deleted for lack of memory   : 0
% 0.20/0.51  # Backward-subsumed                    : 102
% 0.20/0.51  # Backward-rewritten                   : 23
% 0.20/0.51  # Generated clauses                    : 6706
% 0.20/0.51  # ...of the previous two non-trivial   : 4619
% 0.20/0.51  # Contextual simplify-reflections      : 0
% 0.20/0.51  # Paramodulations                      : 6705
% 0.20/0.51  # Factorizations                       : 1
% 0.20/0.51  # Equation resolutions                 : 0
% 0.20/0.51  # Propositional unsat checks           : 0
% 0.20/0.51  #    Propositional check models        : 0
% 0.20/0.51  #    Propositional check unsatisfiable : 0
% 0.20/0.51  #    Propositional clauses             : 0
% 0.20/0.51  #    Propositional clauses after purity: 0
% 0.20/0.51  #    Propositional unsat core size     : 0
% 0.20/0.51  #    Propositional preprocessing time  : 0.000
% 0.20/0.51  #    Propositional encoding time       : 0.000
% 0.20/0.51  #    Propositional solver time         : 0.000
% 0.20/0.51  #    Success case prop preproc time    : 0.000
% 0.20/0.51  #    Success case prop encoding time   : 0.000
% 0.20/0.51  #    Success case prop solver time     : 0.000
% 0.20/0.51  # Current number of processed clauses  : 392
% 0.20/0.51  #    Positive orientable unit clauses  : 85
% 0.20/0.51  #    Positive unorientable unit clauses: 0
% 0.20/0.51  #    Negative unit clauses             : 3
% 0.20/0.51  #    Non-unit-clauses                  : 304
% 0.20/0.51  # Current number of unprocessed clauses: 3145
% 0.20/0.51  # ...number of literals in the above   : 23498
% 0.20/0.51  # Current number of archived formulas  : 0
% 0.20/0.51  # Current number of archived clauses   : 125
% 0.20/0.51  # Clause-clause subsumption calls (NU) : 8675
% 0.20/0.51  # Rec. Clause-clause subsumption calls : 3801
% 0.20/0.51  # Non-unit clause-clause subsumptions  : 520
% 0.20/0.51  # Unit Clause-clause subsumption calls : 327
% 0.20/0.51  # Rewrite failures with RHS unbound    : 5
% 0.20/0.51  # BW rewrite match attempts            : 497
% 0.20/0.51  # BW rewrite match successes           : 15
% 0.20/0.51  # Condensation attempts                : 0
% 0.20/0.51  # Condensation successes               : 0
% 0.20/0.51  # Termbank termtop insertions          : 68448
% 0.20/0.51  
% 0.20/0.51  # -------------------------------------------------
% 0.20/0.51  # User time                : 0.161 s
% 0.20/0.51  # System time              : 0.006 s
% 0.20/0.51  # Total time               : 0.167 s
% 0.20/0.51  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
