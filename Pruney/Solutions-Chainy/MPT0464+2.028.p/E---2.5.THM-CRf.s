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
% DateTime   : Thu Dec  3 10:48:41 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 698 expanded)
%              Number of clauses        :   41 ( 281 expanded)
%              Number of leaves         :   15 ( 206 expanded)
%              Depth                    :   14
%              Number of atoms          :  121 ( 806 expanded)
%              Number of equality atoms :   30 ( 625 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    5 (   1 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t23_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t51_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(t31_xboole_1,axiom,(
    ! [X1,X2,X3] : r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)),k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(t48_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => ( r1_tarski(X1,X2)
               => r1_tarski(k5_relat_1(X3,X1),k5_relat_1(X3,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_relat_1)).

fof(t52_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,X3))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relat_1)).

fof(t19_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(X1,k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(c_0_15,plain,(
    ! [X31,X32] : k1_setfam_1(k2_tarski(X31,X32)) = k3_xboole_0(X31,X32) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_16,plain,(
    ! [X20,X21] : k1_enumset1(X20,X20,X21) = k2_tarski(X20,X21) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_17,plain,(
    ! [X29,X30] : k3_tarski(k2_tarski(X29,X30)) = k2_xboole_0(X29,X30) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_18,plain,(
    ! [X5,X6] : k4_xboole_0(X5,X6) = k5_xboole_0(X5,k3_xboole_0(X5,X6)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_19,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_21,plain,(
    ! [X12,X13,X14] : k3_xboole_0(X12,k2_xboole_0(X13,X14)) = k2_xboole_0(k3_xboole_0(X12,X13),k3_xboole_0(X12,X14)) ),
    inference(variable_rename,[status(thm)],[t23_xboole_1])).

cnf(c_0_22,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_23,plain,(
    ! [X22,X23,X24] : k2_enumset1(X22,X22,X23,X24) = k1_enumset1(X22,X23,X24) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_24,plain,(
    ! [X25,X26,X27,X28] : k3_enumset1(X25,X25,X26,X27,X28) = k2_enumset1(X25,X26,X27,X28) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_25,plain,(
    ! [X18,X19] : k2_xboole_0(k3_xboole_0(X18,X19),k4_xboole_0(X18,X19)) = X18 ),
    inference(variable_rename,[status(thm)],[t51_xboole_1])).

cnf(c_0_26,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

fof(c_0_28,plain,(
    ! [X15,X16,X17] : r1_tarski(k2_xboole_0(k3_xboole_0(X15,X16),k3_xboole_0(X15,X17)),k2_xboole_0(X16,X17)) ),
    inference(variable_rename,[status(thm)],[t31_xboole_1])).

cnf(c_0_29,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_22,c_0_20])).

cnf(c_0_31,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_35,plain,
    ( r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)),k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,plain,
    ( k1_setfam_1(k3_enumset1(X1,X1,X1,X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X3)))) = k3_tarski(k3_enumset1(k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)),k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)),k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)),k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)),k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X3)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_30]),c_0_30]),c_0_27]),c_0_27]),c_0_27]),c_0_27]),c_0_31]),c_0_31]),c_0_31]),c_0_31]),c_0_31]),c_0_31]),c_0_32]),c_0_32]),c_0_32]),c_0_32]),c_0_32]),c_0_32]),c_0_32])).

cnf(c_0_37,plain,
    ( k3_tarski(k3_enumset1(k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)),k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)),k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)),k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)),k5_xboole_0(X1,k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2))))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_30]),c_0_27]),c_0_27]),c_0_34]),c_0_31]),c_0_31]),c_0_31]),c_0_31]),c_0_32]),c_0_32]),c_0_32]),c_0_32]),c_0_32])).

fof(c_0_38,plain,(
    ! [X33,X34] :
      ( ( ~ m1_subset_1(X33,k1_zfmisc_1(X34))
        | r1_tarski(X33,X34) )
      & ( ~ r1_tarski(X33,X34)
        | m1_subset_1(X33,k1_zfmisc_1(X34)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_39,plain,
    ( r1_tarski(k3_tarski(k3_enumset1(k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)),k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)),k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)),k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)),k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X3)))),k3_tarski(k3_enumset1(X2,X2,X2,X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_30]),c_0_30]),c_0_27]),c_0_27]),c_0_27]),c_0_31]),c_0_31]),c_0_31]),c_0_31]),c_0_31]),c_0_32]),c_0_32]),c_0_32]),c_0_32]),c_0_32]),c_0_32])).

cnf(c_0_40,plain,
    ( k3_tarski(k3_enumset1(k1_setfam_1(k3_enumset1(X1,X1,X1,X1,k1_setfam_1(k3_enumset1(X2,X2,X2,X2,X3)))),k1_setfam_1(k3_enumset1(X1,X1,X1,X1,k1_setfam_1(k3_enumset1(X2,X2,X2,X2,X3)))),k1_setfam_1(k3_enumset1(X1,X1,X1,X1,k1_setfam_1(k3_enumset1(X2,X2,X2,X2,X3)))),k1_setfam_1(k3_enumset1(X1,X1,X1,X1,k1_setfam_1(k3_enumset1(X2,X2,X2,X2,X3)))),k1_setfam_1(k3_enumset1(X1,X1,X1,X1,k5_xboole_0(X2,k1_setfam_1(k3_enumset1(X2,X2,X2,X2,X3))))))) = k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

fof(c_0_41,plain,(
    ! [X7,X8] : r1_tarski(k3_xboole_0(X7,X8),X7) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

fof(c_0_42,plain,(
    ! [X35,X36] :
      ( ~ v1_relat_1(X35)
      | ~ m1_subset_1(X36,k1_zfmisc_1(X35))
      | v1_relat_1(X36) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

cnf(c_0_43,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_44,plain,
    ( r1_tarski(k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_37])).

cnf(c_0_45,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_46,plain,(
    ! [X37,X38,X39] :
      ( ~ v1_relat_1(X37)
      | ~ v1_relat_1(X38)
      | ~ v1_relat_1(X39)
      | ~ r1_tarski(X37,X38)
      | r1_tarski(k5_relat_1(X39,X37),k5_relat_1(X39,X38)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_relat_1])])])).

cnf(c_0_47,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_48,plain,
    ( m1_subset_1(k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)),k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

fof(c_0_49,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ! [X3] :
                ( v1_relat_1(X3)
               => r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,X3))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t52_relat_1])).

cnf(c_0_50,plain,
    ( r1_tarski(k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_27]),c_0_31]),c_0_32])).

cnf(c_0_51,plain,
    ( r1_tarski(k5_relat_1(X3,X1),k5_relat_1(X3,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_52,plain,
    ( v1_relat_1(k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

fof(c_0_53,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_relat_1(esk2_0)
    & v1_relat_1(esk3_0)
    & ~ r1_tarski(k5_relat_1(esk1_0,k3_xboole_0(esk2_0,esk3_0)),k3_xboole_0(k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk3_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_49])])])).

cnf(c_0_54,plain,
    ( m1_subset_1(k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_50])).

fof(c_0_55,plain,(
    ! [X9,X10,X11] :
      ( ~ r1_tarski(X9,X10)
      | ~ r1_tarski(X9,X11)
      | r1_tarski(X9,k3_xboole_0(X10,X11)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).

cnf(c_0_56,plain,
    ( r1_tarski(k5_relat_1(X1,k1_setfam_1(k3_enumset1(X2,X2,X2,X2,X3))),k5_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_44]),c_0_52])).

cnf(c_0_57,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_58,plain,
    ( v1_relat_1(k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_54])).

cnf(c_0_59,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk1_0,k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2))),k5_relat_1(esk1_0,X2))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_61,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_62,plain,
    ( r1_tarski(k5_relat_1(X1,k1_setfam_1(k3_enumset1(X2,X2,X2,X2,X3))),k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_50]),c_0_58])).

cnf(c_0_63,plain,
    ( r1_tarski(X1,k1_setfam_1(k3_enumset1(X2,X2,X2,X2,X3)))
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_27]),c_0_31]),c_0_32])).

cnf(c_0_64,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk1_0,k1_setfam_1(k3_enumset1(X1,X1,X1,X1,esk3_0))),k5_relat_1(esk1_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_65,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk1_0,k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2))),k5_relat_1(esk1_0,X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_62,c_0_57])).

cnf(c_0_66,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_67,negated_conjecture,
    ( ~ r1_tarski(k5_relat_1(esk1_0,k3_xboole_0(esk2_0,esk3_0)),k3_xboole_0(k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_68,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk1_0,k1_setfam_1(k3_enumset1(X1,X1,X1,X1,esk3_0))),k1_setfam_1(k3_enumset1(X2,X2,X2,X2,k5_relat_1(esk1_0,esk3_0))))
    | ~ r1_tarski(k5_relat_1(esk1_0,k1_setfam_1(k3_enumset1(X1,X1,X1,X1,esk3_0))),X2) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_69,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk1_0,k1_setfam_1(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,X1))),k5_relat_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_70,negated_conjecture,
    ( ~ r1_tarski(k5_relat_1(esk1_0,k1_setfam_1(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0))),k1_setfam_1(k3_enumset1(k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk3_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_27]),c_0_27]),c_0_31]),c_0_31]),c_0_32]),c_0_32])).

cnf(c_0_71,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_70]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:04:14 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.19/0.42  # AutoSched0-Mode selected heuristic G_E___107_B00_00_F1_PI_AE_Q4_CS_SP_PS_S064A
% 0.19/0.42  # and selection function SelectComplexG.
% 0.19/0.42  #
% 0.19/0.42  # Preprocessing time       : 0.027 s
% 0.19/0.42  # Presaturation interreduction done
% 0.19/0.42  
% 0.19/0.42  # Proof found!
% 0.19/0.42  # SZS status Theorem
% 0.19/0.42  # SZS output start CNFRefutation
% 0.19/0.42  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.19/0.42  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.42  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.19/0.42  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.19/0.42  fof(t23_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_xboole_1)).
% 0.19/0.42  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.42  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.19/0.42  fof(t51_xboole_1, axiom, ![X1, X2]:k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 0.19/0.42  fof(t31_xboole_1, axiom, ![X1, X2, X3]:r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)),k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_xboole_1)).
% 0.19/0.42  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.42  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.19/0.42  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.19/0.42  fof(t48_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>r1_tarski(k5_relat_1(X3,X1),k5_relat_1(X3,X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_relat_1)).
% 0.19/0.42  fof(t52_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_relat_1)).
% 0.19/0.42  fof(t19_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(X1,k3_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 0.19/0.42  fof(c_0_15, plain, ![X31, X32]:k1_setfam_1(k2_tarski(X31,X32))=k3_xboole_0(X31,X32), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.19/0.42  fof(c_0_16, plain, ![X20, X21]:k1_enumset1(X20,X20,X21)=k2_tarski(X20,X21), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.42  fof(c_0_17, plain, ![X29, X30]:k3_tarski(k2_tarski(X29,X30))=k2_xboole_0(X29,X30), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.19/0.42  fof(c_0_18, plain, ![X5, X6]:k4_xboole_0(X5,X6)=k5_xboole_0(X5,k3_xboole_0(X5,X6)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.19/0.42  cnf(c_0_19, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.42  cnf(c_0_20, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.42  fof(c_0_21, plain, ![X12, X13, X14]:k3_xboole_0(X12,k2_xboole_0(X13,X14))=k2_xboole_0(k3_xboole_0(X12,X13),k3_xboole_0(X12,X14)), inference(variable_rename,[status(thm)],[t23_xboole_1])).
% 0.19/0.42  cnf(c_0_22, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.42  fof(c_0_23, plain, ![X22, X23, X24]:k2_enumset1(X22,X22,X23,X24)=k1_enumset1(X22,X23,X24), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.19/0.42  fof(c_0_24, plain, ![X25, X26, X27, X28]:k3_enumset1(X25,X25,X26,X27,X28)=k2_enumset1(X25,X26,X27,X28), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.19/0.42  fof(c_0_25, plain, ![X18, X19]:k2_xboole_0(k3_xboole_0(X18,X19),k4_xboole_0(X18,X19))=X18, inference(variable_rename,[status(thm)],[t51_xboole_1])).
% 0.19/0.42  cnf(c_0_26, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.42  cnf(c_0_27, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_19, c_0_20])).
% 0.19/0.42  fof(c_0_28, plain, ![X15, X16, X17]:r1_tarski(k2_xboole_0(k3_xboole_0(X15,X16),k3_xboole_0(X15,X17)),k2_xboole_0(X16,X17)), inference(variable_rename,[status(thm)],[t31_xboole_1])).
% 0.19/0.42  cnf(c_0_29, plain, (k3_xboole_0(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.42  cnf(c_0_30, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_22, c_0_20])).
% 0.19/0.42  cnf(c_0_31, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.42  cnf(c_0_32, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.42  cnf(c_0_33, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.42  cnf(c_0_34, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))), inference(rw,[status(thm)],[c_0_26, c_0_27])).
% 0.19/0.42  cnf(c_0_35, plain, (r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)),k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.42  cnf(c_0_36, plain, (k1_setfam_1(k3_enumset1(X1,X1,X1,X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X3))))=k3_tarski(k3_enumset1(k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)),k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)),k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)),k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)),k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X3))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_30]), c_0_30]), c_0_27]), c_0_27]), c_0_27]), c_0_27]), c_0_31]), c_0_31]), c_0_31]), c_0_31]), c_0_31]), c_0_31]), c_0_32]), c_0_32]), c_0_32]), c_0_32]), c_0_32]), c_0_32]), c_0_32])).
% 0.19/0.42  cnf(c_0_37, plain, (k3_tarski(k3_enumset1(k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)),k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)),k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)),k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)),k5_xboole_0(X1,k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)))))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_30]), c_0_27]), c_0_27]), c_0_34]), c_0_31]), c_0_31]), c_0_31]), c_0_31]), c_0_32]), c_0_32]), c_0_32]), c_0_32]), c_0_32])).
% 0.19/0.42  fof(c_0_38, plain, ![X33, X34]:((~m1_subset_1(X33,k1_zfmisc_1(X34))|r1_tarski(X33,X34))&(~r1_tarski(X33,X34)|m1_subset_1(X33,k1_zfmisc_1(X34)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.42  cnf(c_0_39, plain, (r1_tarski(k3_tarski(k3_enumset1(k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)),k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)),k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)),k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)),k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X3)))),k3_tarski(k3_enumset1(X2,X2,X2,X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_30]), c_0_30]), c_0_27]), c_0_27]), c_0_27]), c_0_31]), c_0_31]), c_0_31]), c_0_31]), c_0_31]), c_0_32]), c_0_32]), c_0_32]), c_0_32]), c_0_32]), c_0_32])).
% 0.19/0.42  cnf(c_0_40, plain, (k3_tarski(k3_enumset1(k1_setfam_1(k3_enumset1(X1,X1,X1,X1,k1_setfam_1(k3_enumset1(X2,X2,X2,X2,X3)))),k1_setfam_1(k3_enumset1(X1,X1,X1,X1,k1_setfam_1(k3_enumset1(X2,X2,X2,X2,X3)))),k1_setfam_1(k3_enumset1(X1,X1,X1,X1,k1_setfam_1(k3_enumset1(X2,X2,X2,X2,X3)))),k1_setfam_1(k3_enumset1(X1,X1,X1,X1,k1_setfam_1(k3_enumset1(X2,X2,X2,X2,X3)))),k1_setfam_1(k3_enumset1(X1,X1,X1,X1,k5_xboole_0(X2,k1_setfam_1(k3_enumset1(X2,X2,X2,X2,X3)))))))=k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.19/0.42  fof(c_0_41, plain, ![X7, X8]:r1_tarski(k3_xboole_0(X7,X8),X7), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.19/0.42  fof(c_0_42, plain, ![X35, X36]:(~v1_relat_1(X35)|(~m1_subset_1(X36,k1_zfmisc_1(X35))|v1_relat_1(X36))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.19/0.42  cnf(c_0_43, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.42  cnf(c_0_44, plain, (r1_tarski(k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_37])).
% 0.19/0.42  cnf(c_0_45, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.19/0.42  fof(c_0_46, plain, ![X37, X38, X39]:(~v1_relat_1(X37)|(~v1_relat_1(X38)|(~v1_relat_1(X39)|(~r1_tarski(X37,X38)|r1_tarski(k5_relat_1(X39,X37),k5_relat_1(X39,X38)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_relat_1])])])).
% 0.19/0.42  cnf(c_0_47, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.42  cnf(c_0_48, plain, (m1_subset_1(k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)),k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.19/0.42  fof(c_0_49, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,X3))))))), inference(assume_negation,[status(cth)],[t52_relat_1])).
% 0.19/0.42  cnf(c_0_50, plain, (r1_tarski(k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_27]), c_0_31]), c_0_32])).
% 0.19/0.42  cnf(c_0_51, plain, (r1_tarski(k5_relat_1(X3,X1),k5_relat_1(X3,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X3)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.19/0.42  cnf(c_0_52, plain, (v1_relat_1(k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)))|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.19/0.42  fof(c_0_53, negated_conjecture, (v1_relat_1(esk1_0)&(v1_relat_1(esk2_0)&(v1_relat_1(esk3_0)&~r1_tarski(k5_relat_1(esk1_0,k3_xboole_0(esk2_0,esk3_0)),k3_xboole_0(k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk3_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_49])])])).
% 0.19/0.42  cnf(c_0_54, plain, (m1_subset_1(k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_43, c_0_50])).
% 0.19/0.42  fof(c_0_55, plain, ![X9, X10, X11]:(~r1_tarski(X9,X10)|~r1_tarski(X9,X11)|r1_tarski(X9,k3_xboole_0(X10,X11))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).
% 0.19/0.42  cnf(c_0_56, plain, (r1_tarski(k5_relat_1(X1,k1_setfam_1(k3_enumset1(X2,X2,X2,X2,X3))),k5_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_relat_1(X3)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_44]), c_0_52])).
% 0.19/0.42  cnf(c_0_57, negated_conjecture, (v1_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.19/0.42  cnf(c_0_58, plain, (v1_relat_1(k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_47, c_0_54])).
% 0.19/0.42  cnf(c_0_59, plain, (r1_tarski(X1,k3_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.19/0.42  cnf(c_0_60, negated_conjecture, (r1_tarski(k5_relat_1(esk1_0,k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2))),k5_relat_1(esk1_0,X2))|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.19/0.42  cnf(c_0_61, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.19/0.42  cnf(c_0_62, plain, (r1_tarski(k5_relat_1(X1,k1_setfam_1(k3_enumset1(X2,X2,X2,X2,X3))),k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_50]), c_0_58])).
% 0.19/0.42  cnf(c_0_63, plain, (r1_tarski(X1,k1_setfam_1(k3_enumset1(X2,X2,X2,X2,X3)))|~r1_tarski(X1,X3)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_27]), c_0_31]), c_0_32])).
% 0.19/0.42  cnf(c_0_64, negated_conjecture, (r1_tarski(k5_relat_1(esk1_0,k1_setfam_1(k3_enumset1(X1,X1,X1,X1,esk3_0))),k5_relat_1(esk1_0,esk3_0))), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.19/0.42  cnf(c_0_65, negated_conjecture, (r1_tarski(k5_relat_1(esk1_0,k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2))),k5_relat_1(esk1_0,X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_62, c_0_57])).
% 0.19/0.42  cnf(c_0_66, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.19/0.42  cnf(c_0_67, negated_conjecture, (~r1_tarski(k5_relat_1(esk1_0,k3_xboole_0(esk2_0,esk3_0)),k3_xboole_0(k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.19/0.42  cnf(c_0_68, negated_conjecture, (r1_tarski(k5_relat_1(esk1_0,k1_setfam_1(k3_enumset1(X1,X1,X1,X1,esk3_0))),k1_setfam_1(k3_enumset1(X2,X2,X2,X2,k5_relat_1(esk1_0,esk3_0))))|~r1_tarski(k5_relat_1(esk1_0,k1_setfam_1(k3_enumset1(X1,X1,X1,X1,esk3_0))),X2)), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.19/0.42  cnf(c_0_69, negated_conjecture, (r1_tarski(k5_relat_1(esk1_0,k1_setfam_1(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,X1))),k5_relat_1(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.19/0.42  cnf(c_0_70, negated_conjecture, (~r1_tarski(k5_relat_1(esk1_0,k1_setfam_1(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0))),k1_setfam_1(k3_enumset1(k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk3_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67, c_0_27]), c_0_27]), c_0_31]), c_0_31]), c_0_32]), c_0_32])).
% 0.19/0.42  cnf(c_0_71, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_70]), ['proof']).
% 0.19/0.42  # SZS output end CNFRefutation
% 0.19/0.42  # Proof object total steps             : 72
% 0.19/0.42  # Proof object clause steps            : 41
% 0.19/0.42  # Proof object formula steps           : 31
% 0.19/0.42  # Proof object conjectures             : 14
% 0.19/0.42  # Proof object clause conjectures      : 11
% 0.19/0.42  # Proof object formula conjectures     : 3
% 0.19/0.42  # Proof object initial clauses used    : 18
% 0.19/0.42  # Proof object initial formulas used   : 15
% 0.19/0.42  # Proof object generating inferences   : 14
% 0.19/0.42  # Proof object simplifying inferences  : 67
% 0.19/0.42  # Training examples: 0 positive, 0 negative
% 0.19/0.42  # Parsed axioms                        : 15
% 0.19/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.42  # Initial clauses                      : 19
% 0.19/0.42  # Removed in clause preprocessing      : 6
% 0.19/0.42  # Initial clauses in saturation        : 13
% 0.19/0.42  # Processed clauses                    : 364
% 0.19/0.42  # ...of these trivial                  : 8
% 0.19/0.42  # ...subsumed                          : 3
% 0.19/0.42  # ...remaining for further processing  : 353
% 0.19/0.42  # Other redundant clauses eliminated   : 0
% 0.19/0.42  # Clauses deleted for lack of memory   : 0
% 0.19/0.42  # Backward-subsumed                    : 0
% 0.19/0.42  # Backward-rewritten                   : 9
% 0.19/0.42  # Generated clauses                    : 2339
% 0.19/0.42  # ...of the previous two non-trivial   : 2190
% 0.19/0.42  # Contextual simplify-reflections      : 20
% 0.19/0.42  # Paramodulations                      : 2339
% 0.19/0.42  # Factorizations                       : 0
% 0.19/0.42  # Equation resolutions                 : 0
% 0.19/0.42  # Propositional unsat checks           : 0
% 0.19/0.42  #    Propositional check models        : 0
% 0.19/0.42  #    Propositional check unsatisfiable : 0
% 0.19/0.42  #    Propositional clauses             : 0
% 0.19/0.42  #    Propositional clauses after purity: 0
% 0.19/0.42  #    Propositional unsat core size     : 0
% 0.19/0.42  #    Propositional preprocessing time  : 0.000
% 0.19/0.42  #    Propositional encoding time       : 0.000
% 0.19/0.42  #    Propositional solver time         : 0.000
% 0.19/0.42  #    Success case prop preproc time    : 0.000
% 0.19/0.42  #    Success case prop encoding time   : 0.000
% 0.19/0.42  #    Success case prop solver time     : 0.000
% 0.19/0.42  # Current number of processed clauses  : 331
% 0.19/0.42  #    Positive orientable unit clauses  : 220
% 0.19/0.42  #    Positive unorientable unit clauses: 0
% 0.19/0.42  #    Negative unit clauses             : 1
% 0.19/0.42  #    Non-unit-clauses                  : 110
% 0.19/0.42  # Current number of unprocessed clauses: 1851
% 0.19/0.42  # ...number of literals in the above   : 2457
% 0.19/0.42  # Current number of archived formulas  : 0
% 0.19/0.42  # Current number of archived clauses   : 28
% 0.19/0.42  # Clause-clause subsumption calls (NU) : 2950
% 0.19/0.42  # Rec. Clause-clause subsumption calls : 2438
% 0.19/0.42  # Non-unit clause-clause subsumptions  : 23
% 0.19/0.42  # Unit Clause-clause subsumption calls : 2300
% 0.19/0.42  # Rewrite failures with RHS unbound    : 0
% 0.19/0.42  # BW rewrite match attempts            : 1532
% 0.19/0.42  # BW rewrite match successes           : 9
% 0.19/0.42  # Condensation attempts                : 0
% 0.19/0.42  # Condensation successes               : 0
% 0.19/0.42  # Termbank termtop insertions          : 113300
% 0.19/0.42  
% 0.19/0.42  # -------------------------------------------------
% 0.19/0.42  # User time                : 0.080 s
% 0.19/0.42  # System time              : 0.008 s
% 0.19/0.42  # Total time               : 0.088 s
% 0.19/0.42  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
