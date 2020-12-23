%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:58:51 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :  102 (1710 expanded)
%              Number of clauses        :   73 ( 751 expanded)
%              Number of leaves         :   14 ( 470 expanded)
%              Depth                    :   25
%              Number of atoms          :  192 (2635 expanded)
%              Number of equality atoms :  103 (1577 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t123_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t55_relset_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
     => ( r1_xboole_0(X2,X3)
       => k5_relset_1(X3,X1,X4,X2) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relset_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t63_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X2,X3) )
     => r1_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(redefinition_k5_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k5_relset_1(X1,X2,X3,X4) = k7_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

fof(t96_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,X1) = k3_xboole_0(X2,k2_zfmisc_1(X1,k2_relat_1(X2))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_relat_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(c_0_14,plain,(
    ! [X20,X21,X22,X23] : k2_zfmisc_1(k3_xboole_0(X20,X21),k3_xboole_0(X22,X23)) = k3_xboole_0(k2_zfmisc_1(X20,X22),k2_zfmisc_1(X21,X23)) ),
    inference(variable_rename,[status(thm)],[t123_zfmisc_1])).

fof(c_0_15,plain,(
    ! [X10,X11] : k4_xboole_0(X10,k4_xboole_0(X10,X11)) = k3_xboole_0(X10,X11) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_16,plain,(
    ! [X9] : k3_xboole_0(X9,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

cnf(c_0_17,plain,
    ( k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_19,plain,(
    ! [X16,X17] :
      ( ( ~ r1_xboole_0(X16,X17)
        | k4_xboole_0(X16,X17) = X16 )
      & ( k4_xboole_0(X16,X17) != X16
        | r1_xboole_0(X16,X17) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

cnf(c_0_20,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_21,plain,(
    ! [X15] : r1_xboole_0(X15,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

cnf(c_0_22,plain,
    ( k2_zfmisc_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X3,k4_xboole_0(X3,X4))) = k4_xboole_0(k2_zfmisc_1(X1,X3),k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_18]),c_0_18]),c_0_18])).

cnf(c_0_23,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_20,c_0_18])).

cnf(c_0_25,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,plain,
    ( k4_xboole_0(k2_zfmisc_1(X1,X2),k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))) = k2_zfmisc_1(X1,k4_xboole_0(X2,k4_xboole_0(X2,X4)))
    | ~ r1_xboole_0(X1,k4_xboole_0(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_27,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_23]),c_0_25])])).

fof(c_0_28,plain,(
    ! [X18,X19] :
      ( ( k2_zfmisc_1(X18,X19) != k1_xboole_0
        | X18 = k1_xboole_0
        | X19 = k1_xboole_0 )
      & ( X18 != k1_xboole_0
        | k2_zfmisc_1(X18,X19) = k1_xboole_0 )
      & ( X19 != k1_xboole_0
        | k2_zfmisc_1(X18,X19) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_29,plain,(
    ! [X5,X6] :
      ( ( ~ r1_xboole_0(X5,X6)
        | k3_xboole_0(X5,X6) = k1_xboole_0 )
      & ( k3_xboole_0(X5,X6) != k1_xboole_0
        | r1_xboole_0(X5,X6) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_30,plain,
    ( k4_xboole_0(k2_zfmisc_1(X1,X2),k1_xboole_0) = k2_zfmisc_1(X1,k4_xboole_0(X2,k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_27]),c_0_27]),c_0_25])])).

cnf(c_0_31,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_32,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_33,plain,
    ( k4_xboole_0(k2_zfmisc_1(X1,X2),k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))) = k2_zfmisc_1(k4_xboole_0(X1,k4_xboole_0(X1,X3)),X2)
    | ~ r1_xboole_0(X2,k4_xboole_0(X2,X4)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_34,plain,
    ( k2_zfmisc_1(X1,k4_xboole_0(X2,k1_xboole_0)) = k2_zfmisc_1(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_30]),c_0_25])])).

fof(c_0_35,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
       => ( r1_xboole_0(X2,X3)
         => k5_relset_1(X3,X1,X4,X2) = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t55_relset_1])).

cnf(c_0_36,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_37,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_32,c_0_18])).

cnf(c_0_38,plain,
    ( k2_zfmisc_1(k4_xboole_0(X1,k1_xboole_0),X2) = k2_zfmisc_1(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_27]),c_0_27]),c_0_27]),c_0_25])]),c_0_30]),c_0_34])).

fof(c_0_39,plain,(
    ! [X7,X8] :
      ( ~ r1_xboole_0(X7,X8)
      | r1_xboole_0(X8,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

fof(c_0_40,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk1_0)))
    & r1_xboole_0(esk2_0,esk3_0)
    & k5_relset_1(esk3_0,esk1_0,esk4_0,esk2_0) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_35])])])).

cnf(c_0_41,plain,
    ( k4_xboole_0(k2_zfmisc_1(X1,X2),k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))) = k1_xboole_0
    | ~ r1_xboole_0(X2,X4) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_27]),c_0_36])).

cnf(c_0_42,plain,
    ( k4_xboole_0(k2_zfmisc_1(X1,X2),k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k4_xboole_0(X1,X3),X4))) = k2_zfmisc_1(X1,k4_xboole_0(X2,k4_xboole_0(X2,X4)))
    | ~ r1_xboole_0(X1,X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_37]),c_0_38])).

cnf(c_0_43,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( r1_xboole_0(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_45,plain,(
    ! [X24,X25] :
      ( ( ~ m1_subset_1(X24,k1_zfmisc_1(X25))
        | r1_tarski(X24,X25) )
      & ( ~ r1_tarski(X24,X25)
        | m1_subset_1(X24,k1_zfmisc_1(X25)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_46,plain,
    ( k2_zfmisc_1(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) = k1_xboole_0
    | ~ r1_xboole_0(X2,X3)
    | ~ r1_xboole_0(X1,X4) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_47,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

fof(c_0_48,plain,(
    ! [X12,X13,X14] :
      ( ~ r1_tarski(X12,X13)
      | ~ r1_xboole_0(X13,X14)
      | r1_xboole_0(X12,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).

cnf(c_0_49,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_50,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_51,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_52,negated_conjecture,
    ( k2_zfmisc_1(X1,k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk2_0))) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_53,plain,
    ( r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(esk4_0,k2_zfmisc_1(esk3_0,esk1_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_55,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,k4_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_51,c_0_18])).

cnf(c_0_56,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | k2_zfmisc_1(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_57,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk2_0))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_52,c_0_47])).

cnf(c_0_58,negated_conjecture,
    ( r1_xboole_0(esk4_0,X1)
    | ~ r1_xboole_0(k2_zfmisc_1(esk3_0,esk1_0),X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_59,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))
    | k4_xboole_0(X1,k1_xboole_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_55,c_0_24])).

cnf(c_0_60,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_xboole_0
    | k4_xboole_0(X3,k4_xboole_0(X3,X4)) = k1_xboole_0
    | k4_xboole_0(k2_zfmisc_1(X1,X3),k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_56,c_0_22])).

cnf(c_0_61,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,esk3_0) = k1_xboole_0
    | ~ r1_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_23])).

cnf(c_0_62,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X1,X2))
    | k4_xboole_0(X1,k1_xboole_0) != k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_55,c_0_37])).

cnf(c_0_63,negated_conjecture,
    ( r1_xboole_0(esk4_0,k4_xboole_0(k2_zfmisc_1(esk3_0,esk1_0),k1_xboole_0))
    | k4_xboole_0(k2_zfmisc_1(esk3_0,esk1_0),k1_xboole_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_64,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = k1_xboole_0
    | k4_xboole_0(X2,k1_xboole_0) = k1_xboole_0
    | k4_xboole_0(k2_zfmisc_1(X2,X1),k1_xboole_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_27]),c_0_27]),c_0_27])).

cnf(c_0_65,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,esk3_0) = k1_xboole_0
    | k4_xboole_0(esk3_0,k1_xboole_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_47])])).

cnf(c_0_66,negated_conjecture,
    ( r1_xboole_0(esk4_0,k2_zfmisc_1(esk3_0,esk1_0))
    | k2_zfmisc_1(esk3_0,esk1_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_23]),c_0_25])])).

cnf(c_0_67,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = k1_xboole_0
    | k4_xboole_0(X2,k1_xboole_0) = k1_xboole_0
    | k2_zfmisc_1(X1,X2) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_23]),c_0_25])])).

cnf(c_0_68,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,esk3_0) = k1_xboole_0
    | esk3_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_23]),c_0_25])])).

cnf(c_0_69,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_70,plain,(
    ! [X31,X32,X33,X34] :
      ( ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))
      | k5_relset_1(X31,X32,X33,X34) = k7_relat_1(X33,X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k5_relset_1])])).

cnf(c_0_71,negated_conjecture,
    ( r1_xboole_0(k2_zfmisc_1(esk3_0,esk1_0),esk4_0)
    | k2_zfmisc_1(esk3_0,esk1_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_43,c_0_66])).

cnf(c_0_72,negated_conjecture,
    ( k4_xboole_0(esk3_0,k1_xboole_0) = k1_xboole_0
    | esk3_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_73,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_69])).

cnf(c_0_74,plain,
    ( k5_relset_1(X2,X3,X1,X4) = k7_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_75,plain,
    ( X1 = k1_xboole_0
    | ~ r1_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_23])).

cnf(c_0_76,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk4_0)
    | k2_zfmisc_1(esk3_0,esk1_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_58,c_0_71])).

cnf(c_0_77,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,X1) = k1_xboole_0
    | esk3_0 != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_72]),c_0_73])).

fof(c_0_78,plain,(
    ! [X26,X27] :
      ( ~ v1_relat_1(X27)
      | k7_relat_1(X27,X26) = k3_xboole_0(X27,k2_zfmisc_1(X26,k2_relat_1(X27))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t96_relat_1])])).

fof(c_0_79,plain,(
    ! [X28,X29,X30] :
      ( ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))
      | v1_relat_1(X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_80,negated_conjecture,
    ( k5_relset_1(esk3_0,esk1_0,esk4_0,esk2_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_81,negated_conjecture,
    ( k5_relset_1(esk3_0,esk1_0,esk4_0,X1) = k7_relat_1(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_74,c_0_50])).

cnf(c_0_82,plain,
    ( X1 = k1_xboole_0
    | ~ r1_xboole_0(X1,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_23]),c_0_25])])).

cnf(c_0_83,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk4_0)
    | esk3_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_84,plain,
    ( k7_relat_1(X1,X2) = k3_xboole_0(X1,k2_zfmisc_1(X2,k2_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_85,plain,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_25])).

cnf(c_0_86,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_87,negated_conjecture,
    ( k7_relat_1(esk4_0,esk2_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_88,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk3_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_89,plain,
    ( k7_relat_1(X1,X2) = k4_xboole_0(X1,k4_xboole_0(X1,k2_zfmisc_1(X2,k2_relat_1(X1))))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_84,c_0_18])).

cnf(c_0_90,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k2_zfmisc_1(X1,X2))) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_73]),c_0_73]),c_0_85])])).

cnf(c_0_91,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_86,c_0_50])).

cnf(c_0_92,negated_conjecture,
    ( k7_relat_1(k1_xboole_0,esk2_0) != k1_xboole_0
    | esk3_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_93,plain,
    ( k7_relat_1(k1_xboole_0,X1) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_94,negated_conjecture,
    ( v1_relat_1(k1_xboole_0)
    | esk3_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_91,c_0_88])).

cnf(c_0_95,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_94])).

cnf(c_0_96,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk2_0)) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_95])).

cnf(c_0_97,negated_conjecture,
    ( k4_xboole_0(k2_zfmisc_1(esk3_0,X1),k4_xboole_0(k2_zfmisc_1(esk3_0,X1),k2_zfmisc_1(esk2_0,X2))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_96]),c_0_73])).

cnf(c_0_98,negated_conjecture,
    ( r1_xboole_0(k2_zfmisc_1(esk3_0,X1),k2_zfmisc_1(esk2_0,X2)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_97])).

cnf(c_0_99,plain,
    ( k7_relat_1(X1,X2) = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ r1_xboole_0(X1,k2_zfmisc_1(X2,k2_relat_1(X1))) ),
    inference(spm,[status(thm)],[c_0_37,c_0_89])).

cnf(c_0_100,negated_conjecture,
    ( r1_xboole_0(esk4_0,k2_zfmisc_1(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_98])).

cnf(c_0_101,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_100]),c_0_91])]),c_0_87]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:43:00 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.12/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.12/0.39  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.12/0.39  #
% 0.12/0.39  # Preprocessing time       : 0.027 s
% 0.12/0.39  # Presaturation interreduction done
% 0.12/0.39  
% 0.12/0.39  # Proof found!
% 0.12/0.39  # SZS status Theorem
% 0.12/0.39  # SZS output start CNFRefutation
% 0.12/0.39  fof(t123_zfmisc_1, axiom, ![X1, X2, X3, X4]:k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4))=k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 0.12/0.39  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.12/0.39  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 0.12/0.39  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.12/0.39  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.12/0.39  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.12/0.39  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.12/0.39  fof(t55_relset_1, conjecture, ![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))=>(r1_xboole_0(X2,X3)=>k5_relset_1(X3,X1,X4,X2)=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relset_1)).
% 0.12/0.39  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.12/0.39  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.12/0.39  fof(t63_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X2,X3))=>r1_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 0.12/0.39  fof(redefinition_k5_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k5_relset_1(X1,X2,X3,X4)=k7_relat_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 0.12/0.39  fof(t96_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(X2,X1)=k3_xboole_0(X2,k2_zfmisc_1(X1,k2_relat_1(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t96_relat_1)).
% 0.12/0.39  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.12/0.39  fof(c_0_14, plain, ![X20, X21, X22, X23]:k2_zfmisc_1(k3_xboole_0(X20,X21),k3_xboole_0(X22,X23))=k3_xboole_0(k2_zfmisc_1(X20,X22),k2_zfmisc_1(X21,X23)), inference(variable_rename,[status(thm)],[t123_zfmisc_1])).
% 0.12/0.39  fof(c_0_15, plain, ![X10, X11]:k4_xboole_0(X10,k4_xboole_0(X10,X11))=k3_xboole_0(X10,X11), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.12/0.39  fof(c_0_16, plain, ![X9]:k3_xboole_0(X9,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.12/0.39  cnf(c_0_17, plain, (k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4))=k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.39  cnf(c_0_18, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.39  fof(c_0_19, plain, ![X16, X17]:((~r1_xboole_0(X16,X17)|k4_xboole_0(X16,X17)=X16)&(k4_xboole_0(X16,X17)!=X16|r1_xboole_0(X16,X17))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.12/0.39  cnf(c_0_20, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.39  fof(c_0_21, plain, ![X15]:r1_xboole_0(X15,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.12/0.39  cnf(c_0_22, plain, (k2_zfmisc_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X3,k4_xboole_0(X3,X4)))=k4_xboole_0(k2_zfmisc_1(X1,X3),k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17, c_0_18]), c_0_18]), c_0_18])).
% 0.12/0.39  cnf(c_0_23, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.39  cnf(c_0_24, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_20, c_0_18])).
% 0.12/0.39  cnf(c_0_25, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.12/0.39  cnf(c_0_26, plain, (k4_xboole_0(k2_zfmisc_1(X1,X2),k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)))=k2_zfmisc_1(X1,k4_xboole_0(X2,k4_xboole_0(X2,X4)))|~r1_xboole_0(X1,k4_xboole_0(X1,X3))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.12/0.39  cnf(c_0_27, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_23]), c_0_25])])).
% 0.12/0.39  fof(c_0_28, plain, ![X18, X19]:((k2_zfmisc_1(X18,X19)!=k1_xboole_0|(X18=k1_xboole_0|X19=k1_xboole_0))&((X18!=k1_xboole_0|k2_zfmisc_1(X18,X19)=k1_xboole_0)&(X19!=k1_xboole_0|k2_zfmisc_1(X18,X19)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.12/0.39  fof(c_0_29, plain, ![X5, X6]:((~r1_xboole_0(X5,X6)|k3_xboole_0(X5,X6)=k1_xboole_0)&(k3_xboole_0(X5,X6)!=k1_xboole_0|r1_xboole_0(X5,X6))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.12/0.39  cnf(c_0_30, plain, (k4_xboole_0(k2_zfmisc_1(X1,X2),k1_xboole_0)=k2_zfmisc_1(X1,k4_xboole_0(X2,k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_27]), c_0_27]), c_0_25])])).
% 0.12/0.39  cnf(c_0_31, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.12/0.39  cnf(c_0_32, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.12/0.39  cnf(c_0_33, plain, (k4_xboole_0(k2_zfmisc_1(X1,X2),k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)))=k2_zfmisc_1(k4_xboole_0(X1,k4_xboole_0(X1,X3)),X2)|~r1_xboole_0(X2,k4_xboole_0(X2,X4))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.12/0.39  cnf(c_0_34, plain, (k2_zfmisc_1(X1,k4_xboole_0(X2,k1_xboole_0))=k2_zfmisc_1(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_30]), c_0_25])])).
% 0.12/0.39  fof(c_0_35, negated_conjecture, ~(![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))=>(r1_xboole_0(X2,X3)=>k5_relset_1(X3,X1,X4,X2)=k1_xboole_0))), inference(assume_negation,[status(cth)],[t55_relset_1])).
% 0.12/0.39  cnf(c_0_36, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_31])).
% 0.12/0.39  cnf(c_0_37, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_32, c_0_18])).
% 0.12/0.39  cnf(c_0_38, plain, (k2_zfmisc_1(k4_xboole_0(X1,k1_xboole_0),X2)=k2_zfmisc_1(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_27]), c_0_27]), c_0_27]), c_0_25])]), c_0_30]), c_0_34])).
% 0.12/0.39  fof(c_0_39, plain, ![X7, X8]:(~r1_xboole_0(X7,X8)|r1_xboole_0(X8,X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.12/0.39  fof(c_0_40, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk1_0)))&(r1_xboole_0(esk2_0,esk3_0)&k5_relset_1(esk3_0,esk1_0,esk4_0,esk2_0)!=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_35])])])).
% 0.12/0.39  cnf(c_0_41, plain, (k4_xboole_0(k2_zfmisc_1(X1,X2),k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)))=k1_xboole_0|~r1_xboole_0(X2,X4)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_27]), c_0_36])).
% 0.12/0.39  cnf(c_0_42, plain, (k4_xboole_0(k2_zfmisc_1(X1,X2),k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k4_xboole_0(X1,X3),X4)))=k2_zfmisc_1(X1,k4_xboole_0(X2,k4_xboole_0(X2,X4)))|~r1_xboole_0(X1,X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_37]), c_0_38])).
% 0.12/0.39  cnf(c_0_43, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.12/0.39  cnf(c_0_44, negated_conjecture, (r1_xboole_0(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.12/0.39  fof(c_0_45, plain, ![X24, X25]:((~m1_subset_1(X24,k1_zfmisc_1(X25))|r1_tarski(X24,X25))&(~r1_tarski(X24,X25)|m1_subset_1(X24,k1_zfmisc_1(X25)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.12/0.39  cnf(c_0_46, plain, (k2_zfmisc_1(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))=k1_xboole_0|~r1_xboole_0(X2,X3)|~r1_xboole_0(X1,X4)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.12/0.39  cnf(c_0_47, negated_conjecture, (r1_xboole_0(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.12/0.39  fof(c_0_48, plain, ![X12, X13, X14]:(~r1_tarski(X12,X13)|~r1_xboole_0(X13,X14)|r1_xboole_0(X12,X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).
% 0.12/0.39  cnf(c_0_49, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.12/0.39  cnf(c_0_50, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.12/0.39  cnf(c_0_51, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.12/0.39  cnf(c_0_52, negated_conjecture, (k2_zfmisc_1(X1,k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk2_0)))=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.12/0.39  cnf(c_0_53, plain, (r1_xboole_0(X1,X3)|~r1_tarski(X1,X2)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.12/0.39  cnf(c_0_54, negated_conjecture, (r1_tarski(esk4_0,k2_zfmisc_1(esk3_0,esk1_0))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.12/0.39  cnf(c_0_55, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,k4_xboole_0(X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_51, c_0_18])).
% 0.12/0.39  cnf(c_0_56, plain, (X1=k1_xboole_0|X2=k1_xboole_0|k2_zfmisc_1(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.12/0.39  cnf(c_0_57, negated_conjecture, (k2_zfmisc_1(esk3_0,k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk2_0)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_52, c_0_47])).
% 0.12/0.39  cnf(c_0_58, negated_conjecture, (r1_xboole_0(esk4_0,X1)|~r1_xboole_0(k2_zfmisc_1(esk3_0,esk1_0),X1)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.12/0.39  cnf(c_0_59, plain, (r1_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))|k4_xboole_0(X1,k1_xboole_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_55, c_0_24])).
% 0.12/0.39  cnf(c_0_60, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_xboole_0|k4_xboole_0(X3,k4_xboole_0(X3,X4))=k1_xboole_0|k4_xboole_0(k2_zfmisc_1(X1,X3),k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_56, c_0_22])).
% 0.12/0.39  cnf(c_0_61, negated_conjecture, (k2_zfmisc_1(esk3_0,esk3_0)=k1_xboole_0|~r1_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk2_0))), inference(spm,[status(thm)],[c_0_57, c_0_23])).
% 0.12/0.39  cnf(c_0_62, plain, (r1_xboole_0(X1,k4_xboole_0(X1,X2))|k4_xboole_0(X1,k1_xboole_0)!=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_55, c_0_37])).
% 0.12/0.39  cnf(c_0_63, negated_conjecture, (r1_xboole_0(esk4_0,k4_xboole_0(k2_zfmisc_1(esk3_0,esk1_0),k1_xboole_0))|k4_xboole_0(k2_zfmisc_1(esk3_0,esk1_0),k1_xboole_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.12/0.39  cnf(c_0_64, plain, (k4_xboole_0(X1,k1_xboole_0)=k1_xboole_0|k4_xboole_0(X2,k1_xboole_0)=k1_xboole_0|k4_xboole_0(k2_zfmisc_1(X2,X1),k1_xboole_0)!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_27]), c_0_27]), c_0_27])).
% 0.12/0.39  cnf(c_0_65, negated_conjecture, (k2_zfmisc_1(esk3_0,esk3_0)=k1_xboole_0|k4_xboole_0(esk3_0,k1_xboole_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_47])])).
% 0.12/0.39  cnf(c_0_66, negated_conjecture, (r1_xboole_0(esk4_0,k2_zfmisc_1(esk3_0,esk1_0))|k2_zfmisc_1(esk3_0,esk1_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_23]), c_0_25])])).
% 0.12/0.39  cnf(c_0_67, plain, (k4_xboole_0(X1,k1_xboole_0)=k1_xboole_0|k4_xboole_0(X2,k1_xboole_0)=k1_xboole_0|k2_zfmisc_1(X1,X2)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_23]), c_0_25])])).
% 0.12/0.39  cnf(c_0_68, negated_conjecture, (k2_zfmisc_1(esk3_0,esk3_0)=k1_xboole_0|esk3_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_23]), c_0_25])])).
% 0.12/0.39  cnf(c_0_69, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.12/0.39  fof(c_0_70, plain, ![X31, X32, X33, X34]:(~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))|k5_relset_1(X31,X32,X33,X34)=k7_relat_1(X33,X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k5_relset_1])])).
% 0.12/0.39  cnf(c_0_71, negated_conjecture, (r1_xboole_0(k2_zfmisc_1(esk3_0,esk1_0),esk4_0)|k2_zfmisc_1(esk3_0,esk1_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_43, c_0_66])).
% 0.12/0.39  cnf(c_0_72, negated_conjecture, (k4_xboole_0(esk3_0,k1_xboole_0)=k1_xboole_0|esk3_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.12/0.39  cnf(c_0_73, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_69])).
% 0.12/0.39  cnf(c_0_74, plain, (k5_relset_1(X2,X3,X1,X4)=k7_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.12/0.39  cnf(c_0_75, plain, (X1=k1_xboole_0|~r1_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))), inference(spm,[status(thm)],[c_0_24, c_0_23])).
% 0.12/0.39  cnf(c_0_76, negated_conjecture, (r1_xboole_0(esk4_0,esk4_0)|k2_zfmisc_1(esk3_0,esk1_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_58, c_0_71])).
% 0.12/0.39  cnf(c_0_77, negated_conjecture, (k2_zfmisc_1(esk3_0,X1)=k1_xboole_0|esk3_0!=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_72]), c_0_73])).
% 0.12/0.39  fof(c_0_78, plain, ![X26, X27]:(~v1_relat_1(X27)|k7_relat_1(X27,X26)=k3_xboole_0(X27,k2_zfmisc_1(X26,k2_relat_1(X27)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t96_relat_1])])).
% 0.12/0.39  fof(c_0_79, plain, ![X28, X29, X30]:(~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))|v1_relat_1(X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.12/0.39  cnf(c_0_80, negated_conjecture, (k5_relset_1(esk3_0,esk1_0,esk4_0,esk2_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.12/0.39  cnf(c_0_81, negated_conjecture, (k5_relset_1(esk3_0,esk1_0,esk4_0,X1)=k7_relat_1(esk4_0,X1)), inference(spm,[status(thm)],[c_0_74, c_0_50])).
% 0.12/0.39  cnf(c_0_82, plain, (X1=k1_xboole_0|~r1_xboole_0(X1,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_23]), c_0_25])])).
% 0.12/0.39  cnf(c_0_83, negated_conjecture, (r1_xboole_0(esk4_0,esk4_0)|esk3_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 0.12/0.39  cnf(c_0_84, plain, (k7_relat_1(X1,X2)=k3_xboole_0(X1,k2_zfmisc_1(X2,k2_relat_1(X1)))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_78])).
% 0.12/0.39  cnf(c_0_85, plain, (r1_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_43, c_0_25])).
% 0.12/0.39  cnf(c_0_86, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_79])).
% 0.12/0.39  cnf(c_0_87, negated_conjecture, (k7_relat_1(esk4_0,esk2_0)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_80, c_0_81])).
% 0.12/0.39  cnf(c_0_88, negated_conjecture, (esk4_0=k1_xboole_0|esk3_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 0.12/0.39  cnf(c_0_89, plain, (k7_relat_1(X1,X2)=k4_xboole_0(X1,k4_xboole_0(X1,k2_zfmisc_1(X2,k2_relat_1(X1))))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_84, c_0_18])).
% 0.12/0.39  cnf(c_0_90, plain, (k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k2_zfmisc_1(X1,X2)))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_73]), c_0_73]), c_0_85])])).
% 0.12/0.39  cnf(c_0_91, negated_conjecture, (v1_relat_1(esk4_0)), inference(spm,[status(thm)],[c_0_86, c_0_50])).
% 0.12/0.39  cnf(c_0_92, negated_conjecture, (k7_relat_1(k1_xboole_0,esk2_0)!=k1_xboole_0|esk3_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_87, c_0_88])).
% 0.12/0.39  cnf(c_0_93, plain, (k7_relat_1(k1_xboole_0,X1)=k1_xboole_0|~v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_89, c_0_90])).
% 0.12/0.39  cnf(c_0_94, negated_conjecture, (v1_relat_1(k1_xboole_0)|esk3_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_91, c_0_88])).
% 0.12/0.39  cnf(c_0_95, negated_conjecture, (esk3_0!=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_94])).
% 0.12/0.39  cnf(c_0_96, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk2_0))=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_95])).
% 0.12/0.39  cnf(c_0_97, negated_conjecture, (k4_xboole_0(k2_zfmisc_1(esk3_0,X1),k4_xboole_0(k2_zfmisc_1(esk3_0,X1),k2_zfmisc_1(esk2_0,X2)))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_96]), c_0_73])).
% 0.12/0.39  cnf(c_0_98, negated_conjecture, (r1_xboole_0(k2_zfmisc_1(esk3_0,X1),k2_zfmisc_1(esk2_0,X2))), inference(spm,[status(thm)],[c_0_55, c_0_97])).
% 0.12/0.39  cnf(c_0_99, plain, (k7_relat_1(X1,X2)=k1_xboole_0|~v1_relat_1(X1)|~r1_xboole_0(X1,k2_zfmisc_1(X2,k2_relat_1(X1)))), inference(spm,[status(thm)],[c_0_37, c_0_89])).
% 0.12/0.39  cnf(c_0_100, negated_conjecture, (r1_xboole_0(esk4_0,k2_zfmisc_1(esk2_0,X1))), inference(spm,[status(thm)],[c_0_58, c_0_98])).
% 0.12/0.39  cnf(c_0_101, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_100]), c_0_91])]), c_0_87]), ['proof']).
% 0.12/0.39  # SZS output end CNFRefutation
% 0.12/0.39  # Proof object total steps             : 102
% 0.12/0.39  # Proof object clause steps            : 73
% 0.12/0.39  # Proof object formula steps           : 29
% 0.12/0.39  # Proof object conjectures             : 33
% 0.12/0.39  # Proof object clause conjectures      : 30
% 0.12/0.39  # Proof object formula conjectures     : 3
% 0.12/0.39  # Proof object initial clauses used    : 19
% 0.12/0.39  # Proof object initial formulas used   : 14
% 0.12/0.39  # Proof object generating inferences   : 46
% 0.12/0.39  # Proof object simplifying inferences  : 49
% 0.12/0.39  # Training examples: 0 positive, 0 negative
% 0.12/0.39  # Parsed axioms                        : 14
% 0.12/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.39  # Initial clauses                      : 21
% 0.12/0.39  # Removed in clause preprocessing      : 1
% 0.12/0.39  # Initial clauses in saturation        : 20
% 0.12/0.39  # Processed clauses                    : 361
% 0.12/0.39  # ...of these trivial                  : 10
% 0.12/0.39  # ...subsumed                          : 187
% 0.12/0.39  # ...remaining for further processing  : 164
% 0.12/0.39  # Other redundant clauses eliminated   : 11
% 0.12/0.39  # Clauses deleted for lack of memory   : 0
% 0.12/0.39  # Backward-subsumed                    : 2
% 0.12/0.39  # Backward-rewritten                   : 14
% 0.12/0.39  # Generated clauses                    : 1625
% 0.12/0.39  # ...of the previous two non-trivial   : 1249
% 0.12/0.39  # Contextual simplify-reflections      : 1
% 0.12/0.39  # Paramodulations                      : 1611
% 0.12/0.39  # Factorizations                       : 3
% 0.12/0.39  # Equation resolutions                 : 11
% 0.12/0.39  # Propositional unsat checks           : 0
% 0.12/0.39  #    Propositional check models        : 0
% 0.12/0.39  #    Propositional check unsatisfiable : 0
% 0.12/0.39  #    Propositional clauses             : 0
% 0.12/0.39  #    Propositional clauses after purity: 0
% 0.12/0.39  #    Propositional unsat core size     : 0
% 0.12/0.39  #    Propositional preprocessing time  : 0.000
% 0.12/0.39  #    Propositional encoding time       : 0.000
% 0.12/0.39  #    Propositional solver time         : 0.000
% 0.12/0.39  #    Success case prop preproc time    : 0.000
% 0.12/0.39  #    Success case prop encoding time   : 0.000
% 0.12/0.39  #    Success case prop solver time     : 0.000
% 0.12/0.39  # Current number of processed clauses  : 126
% 0.12/0.39  #    Positive orientable unit clauses  : 23
% 0.12/0.39  #    Positive unorientable unit clauses: 0
% 0.12/0.39  #    Negative unit clauses             : 5
% 0.12/0.39  #    Non-unit-clauses                  : 98
% 0.12/0.39  # Current number of unprocessed clauses: 885
% 0.12/0.39  # ...number of literals in the above   : 2315
% 0.12/0.39  # Current number of archived formulas  : 0
% 0.12/0.39  # Current number of archived clauses   : 37
% 0.12/0.39  # Clause-clause subsumption calls (NU) : 1135
% 0.12/0.39  # Rec. Clause-clause subsumption calls : 1061
% 0.12/0.39  # Non-unit clause-clause subsumptions  : 149
% 0.12/0.39  # Unit Clause-clause subsumption calls : 171
% 0.12/0.39  # Rewrite failures with RHS unbound    : 0
% 0.12/0.39  # BW rewrite match attempts            : 32
% 0.12/0.39  # BW rewrite match successes           : 12
% 0.12/0.39  # Condensation attempts                : 0
% 0.12/0.39  # Condensation successes               : 0
% 0.12/0.39  # Termbank termtop insertions          : 23478
% 0.12/0.39  
% 0.12/0.39  # -------------------------------------------------
% 0.12/0.39  # User time                : 0.055 s
% 0.12/0.39  # System time              : 0.005 s
% 0.12/0.39  # Total time               : 0.060 s
% 0.12/0.39  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
