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
% DateTime   : Thu Dec  3 10:55:26 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 405 expanded)
%              Number of clauses        :   40 ( 179 expanded)
%              Number of leaves         :   17 ( 112 expanded)
%              Depth                    :   12
%              Number of atoms          :  114 ( 479 expanded)
%              Number of equality atoms :   57 ( 384 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t43_funct_1,axiom,(
    ! [X1,X2] : k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) = k6_relat_1(k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t162_funct_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k9_relat_1(k6_relat_1(X1),X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_funct_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(t63_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X2,X3) )
     => r1_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(t160_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k2_relat_1(k5_relat_1(X1,X2)) = k9_relat_1(X2,k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(t54_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k4_relat_1(k5_relat_1(X1,X2)) = k5_relat_1(k4_relat_1(X2),k4_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

fof(t72_relat_1,axiom,(
    ! [X1] : k4_relat_1(k6_relat_1(X1)) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_relat_1)).

fof(c_0_17,plain,(
    ! [X25,X26] : k1_setfam_1(k2_tarski(X25,X26)) = k3_xboole_0(X25,X26) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_18,plain,(
    ! [X16,X17] : k1_enumset1(X16,X16,X17) = k2_tarski(X16,X17) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_19,plain,(
    ! [X36,X37] : k5_relat_1(k6_relat_1(X37),k6_relat_1(X36)) = k6_relat_1(k3_xboole_0(X36,X37)) ),
    inference(variable_rename,[status(thm)],[t43_funct_1])).

cnf(c_0_20,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_22,plain,(
    ! [X18,X19,X20] : k2_enumset1(X18,X18,X19,X20) = k1_enumset1(X18,X19,X20) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_23,plain,(
    ! [X21,X22,X23,X24] : k3_enumset1(X21,X21,X22,X23,X24) = k2_enumset1(X21,X22,X23,X24) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_24,plain,(
    ! [X7,X8] : k4_xboole_0(X7,k4_xboole_0(X7,X8)) = k3_xboole_0(X7,X8) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_25,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => k9_relat_1(k6_relat_1(X1),X2) = X2 ) ),
    inference(assume_negation,[status(cth)],[t162_funct_1])).

cnf(c_0_26,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k6_relat_1(k3_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_28,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_31,plain,(
    ! [X27,X28] :
      ( ( ~ m1_subset_1(X27,k1_zfmisc_1(X28))
        | r1_tarski(X27,X28) )
      & ( ~ r1_tarski(X27,X28)
        | m1_subset_1(X27,k1_zfmisc_1(X28)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_32,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0))
    & k9_relat_1(k6_relat_1(esk1_0),esk2_0) != esk2_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).

fof(c_0_33,plain,(
    ! [X34] :
      ( k1_relat_1(k6_relat_1(X34)) = X34
      & k2_relat_1(k6_relat_1(X34)) = X34 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

cnf(c_0_34,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k6_relat_1(k1_setfam_1(k3_enumset1(X2,X2,X2,X2,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29])).

cnf(c_0_35,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_27]),c_0_28]),c_0_29])).

fof(c_0_36,plain,(
    ! [X9,X10,X11] :
      ( ~ r1_tarski(X9,X10)
      | ~ r1_xboole_0(X10,X11)
      | r1_xboole_0(X9,X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_39,plain,(
    ! [X5,X6] :
      ( ~ r1_xboole_0(X5,X6)
      | r1_xboole_0(X6,X5) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

fof(c_0_40,plain,(
    ! [X12,X13] : r1_xboole_0(k4_xboole_0(X12,X13),X13) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

cnf(c_0_41,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_42,plain,
    ( k6_relat_1(k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) ),
    inference(rw,[status(thm)],[c_0_34,c_0_35])).

fof(c_0_43,plain,(
    ! [X30,X31] :
      ( ~ v1_relat_1(X30)
      | ~ v1_relat_1(X31)
      | k2_relat_1(k5_relat_1(X30,X31)) = k9_relat_1(X31,k2_relat_1(X30)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t160_relat_1])])])).

fof(c_0_44,plain,(
    ! [X29] : v1_relat_1(k6_relat_1(X29)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

cnf(c_0_45,plain,
    ( r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(esk2_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_47,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_48,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_49,plain,
    ( k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_50,plain,
    ( k2_relat_1(k5_relat_1(X1,X2)) = k9_relat_1(X2,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_51,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

fof(c_0_52,plain,(
    ! [X14,X15] :
      ( ( ~ r1_xboole_0(X14,X15)
        | k4_xboole_0(X14,X15) = X14 )
      & ( k4_xboole_0(X14,X15) != X14
        | r1_xboole_0(X14,X15) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

cnf(c_0_53,negated_conjecture,
    ( r1_xboole_0(esk2_0,X1)
    | ~ r1_xboole_0(esk1_0,X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_54,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

fof(c_0_55,plain,(
    ! [X32,X33] :
      ( ~ v1_relat_1(X32)
      | ~ v1_relat_1(X33)
      | k4_relat_1(k5_relat_1(X32,X33)) = k5_relat_1(k4_relat_1(X33),k4_relat_1(X32)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_relat_1])])])).

fof(c_0_56,plain,(
    ! [X35] : k4_relat_1(k6_relat_1(X35)) = k6_relat_1(X35) ),
    inference(variable_rename,[status(thm)],[t72_relat_1])).

cnf(c_0_57,plain,
    ( k6_relat_1(k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_49])).

cnf(c_0_58,plain,
    ( k2_relat_1(k5_relat_1(k6_relat_1(X1),X2)) = k9_relat_1(X2,X1)
    | ~ v1_relat_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_41]),c_0_51])])).

cnf(c_0_59,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_60,negated_conjecture,
    ( r1_xboole_0(esk2_0,k4_xboole_0(X1,esk1_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_61,plain,
    ( k4_relat_1(k5_relat_1(X1,X2)) = k5_relat_1(k4_relat_1(X2),k4_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_62,plain,
    ( k4_relat_1(k6_relat_1(X1)) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_63,plain,
    ( k6_relat_1(k9_relat_1(k6_relat_1(X1),X2)) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_51])])).

cnf(c_0_64,negated_conjecture,
    ( k4_xboole_0(esk2_0,k4_xboole_0(X1,esk1_0)) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_65,plain,
    ( k5_relat_1(k4_relat_1(X1),k6_relat_1(X2)) = k4_relat_1(k5_relat_1(k6_relat_1(X2),X1))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_51])])).

cnf(c_0_66,plain,
    ( k4_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_42])).

cnf(c_0_67,plain,
    ( k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k9_relat_1(k6_relat_1(X2),X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_63])).

cnf(c_0_68,negated_conjecture,
    ( k5_relat_1(k6_relat_1(esk1_0),k6_relat_1(esk2_0)) = k6_relat_1(esk2_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_64])).

cnf(c_0_69,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_62]),c_0_66]),c_0_51])])).

cnf(c_0_70,negated_conjecture,
    ( k9_relat_1(k6_relat_1(esk1_0),esk2_0) != esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_71,plain,
    ( k9_relat_1(k6_relat_1(X1),X2) = k4_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[c_0_49,c_0_67])).

cnf(c_0_72,negated_conjecture,
    ( k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)) = k6_relat_1(esk2_0) ),
    inference(rw,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_73,negated_conjecture,
    ( k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0)) != esk2_0 ),
    inference(rw,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_74,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_72]),c_0_41]),c_0_71]),c_0_51])]),c_0_73]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:27:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S081N
% 0.13/0.38  # and selection function SelectCQArNTNp.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.028 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.13/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.13/0.38  fof(t43_funct_1, axiom, ![X1, X2]:k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))=k6_relat_1(k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 0.13/0.38  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.13/0.38  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.13/0.38  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.13/0.38  fof(t162_funct_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k9_relat_1(k6_relat_1(X1),X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_funct_1)).
% 0.13/0.38  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.13/0.38  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 0.13/0.38  fof(t63_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X2,X3))=>r1_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 0.13/0.38  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.13/0.38  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 0.13/0.38  fof(t160_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k2_relat_1(k5_relat_1(X1,X2))=k9_relat_1(X2,k2_relat_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t160_relat_1)).
% 0.13/0.38  fof(dt_k6_relat_1, axiom, ![X1]:v1_relat_1(k6_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 0.13/0.38  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.13/0.38  fof(t54_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k4_relat_1(k5_relat_1(X1,X2))=k5_relat_1(k4_relat_1(X2),k4_relat_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_relat_1)).
% 0.13/0.38  fof(t72_relat_1, axiom, ![X1]:k4_relat_1(k6_relat_1(X1))=k6_relat_1(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_relat_1)).
% 0.13/0.38  fof(c_0_17, plain, ![X25, X26]:k1_setfam_1(k2_tarski(X25,X26))=k3_xboole_0(X25,X26), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.13/0.38  fof(c_0_18, plain, ![X16, X17]:k1_enumset1(X16,X16,X17)=k2_tarski(X16,X17), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.13/0.38  fof(c_0_19, plain, ![X36, X37]:k5_relat_1(k6_relat_1(X37),k6_relat_1(X36))=k6_relat_1(k3_xboole_0(X36,X37)), inference(variable_rename,[status(thm)],[t43_funct_1])).
% 0.13/0.38  cnf(c_0_20, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.38  cnf(c_0_21, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.38  fof(c_0_22, plain, ![X18, X19, X20]:k2_enumset1(X18,X18,X19,X20)=k1_enumset1(X18,X19,X20), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.13/0.38  fof(c_0_23, plain, ![X21, X22, X23, X24]:k3_enumset1(X21,X21,X22,X23,X24)=k2_enumset1(X21,X22,X23,X24), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.13/0.38  fof(c_0_24, plain, ![X7, X8]:k4_xboole_0(X7,k4_xboole_0(X7,X8))=k3_xboole_0(X7,X8), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.13/0.38  fof(c_0_25, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k9_relat_1(k6_relat_1(X1),X2)=X2)), inference(assume_negation,[status(cth)],[t162_funct_1])).
% 0.13/0.38  cnf(c_0_26, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k6_relat_1(k3_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_27, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 0.13/0.38  cnf(c_0_28, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.38  cnf(c_0_29, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.38  cnf(c_0_30, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.38  fof(c_0_31, plain, ![X27, X28]:((~m1_subset_1(X27,k1_zfmisc_1(X28))|r1_tarski(X27,X28))&(~r1_tarski(X27,X28)|m1_subset_1(X27,k1_zfmisc_1(X28)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.13/0.38  fof(c_0_32, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0))&k9_relat_1(k6_relat_1(esk1_0),esk2_0)!=esk2_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).
% 0.13/0.38  fof(c_0_33, plain, ![X34]:(k1_relat_1(k6_relat_1(X34))=X34&k2_relat_1(k6_relat_1(X34))=X34), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.13/0.38  cnf(c_0_34, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k6_relat_1(k1_setfam_1(k3_enumset1(X2,X2,X2,X2,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_29])).
% 0.13/0.38  cnf(c_0_35, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_27]), c_0_28]), c_0_29])).
% 0.13/0.38  fof(c_0_36, plain, ![X9, X10, X11]:(~r1_tarski(X9,X10)|~r1_xboole_0(X10,X11)|r1_xboole_0(X9,X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).
% 0.13/0.38  cnf(c_0_37, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.13/0.38  cnf(c_0_38, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.13/0.38  fof(c_0_39, plain, ![X5, X6]:(~r1_xboole_0(X5,X6)|r1_xboole_0(X6,X5)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.13/0.38  fof(c_0_40, plain, ![X12, X13]:r1_xboole_0(k4_xboole_0(X12,X13),X13), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 0.13/0.38  cnf(c_0_41, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.13/0.38  cnf(c_0_42, plain, (k6_relat_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))), inference(rw,[status(thm)],[c_0_34, c_0_35])).
% 0.13/0.38  fof(c_0_43, plain, ![X30, X31]:(~v1_relat_1(X30)|(~v1_relat_1(X31)|k2_relat_1(k5_relat_1(X30,X31))=k9_relat_1(X31,k2_relat_1(X30)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t160_relat_1])])])).
% 0.13/0.38  fof(c_0_44, plain, ![X29]:v1_relat_1(k6_relat_1(X29)), inference(variable_rename,[status(thm)],[dt_k6_relat_1])).
% 0.13/0.38  cnf(c_0_45, plain, (r1_xboole_0(X1,X3)|~r1_tarski(X1,X2)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.13/0.38  cnf(c_0_46, negated_conjecture, (r1_tarski(esk2_0,esk1_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.13/0.38  cnf(c_0_47, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.13/0.38  cnf(c_0_48, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.13/0.38  cnf(c_0_49, plain, (k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.13/0.38  cnf(c_0_50, plain, (k2_relat_1(k5_relat_1(X1,X2))=k9_relat_1(X2,k2_relat_1(X1))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.13/0.38  cnf(c_0_51, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.13/0.38  fof(c_0_52, plain, ![X14, X15]:((~r1_xboole_0(X14,X15)|k4_xboole_0(X14,X15)=X14)&(k4_xboole_0(X14,X15)!=X14|r1_xboole_0(X14,X15))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.13/0.38  cnf(c_0_53, negated_conjecture, (r1_xboole_0(esk2_0,X1)|~r1_xboole_0(esk1_0,X1)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.13/0.38  cnf(c_0_54, plain, (r1_xboole_0(X1,k4_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.13/0.38  fof(c_0_55, plain, ![X32, X33]:(~v1_relat_1(X32)|(~v1_relat_1(X33)|k4_relat_1(k5_relat_1(X32,X33))=k5_relat_1(k4_relat_1(X33),k4_relat_1(X32)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_relat_1])])])).
% 0.13/0.38  fof(c_0_56, plain, ![X35]:k4_relat_1(k6_relat_1(X35))=k6_relat_1(X35), inference(variable_rename,[status(thm)],[t72_relat_1])).
% 0.13/0.38  cnf(c_0_57, plain, (k6_relat_1(k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))))=k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))), inference(spm,[status(thm)],[c_0_42, c_0_49])).
% 0.13/0.38  cnf(c_0_58, plain, (k2_relat_1(k5_relat_1(k6_relat_1(X1),X2))=k9_relat_1(X2,X1)|~v1_relat_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_41]), c_0_51])])).
% 0.13/0.38  cnf(c_0_59, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.13/0.38  cnf(c_0_60, negated_conjecture, (r1_xboole_0(esk2_0,k4_xboole_0(X1,esk1_0))), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.13/0.38  cnf(c_0_61, plain, (k4_relat_1(k5_relat_1(X1,X2))=k5_relat_1(k4_relat_1(X2),k4_relat_1(X1))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.13/0.38  cnf(c_0_62, plain, (k4_relat_1(k6_relat_1(X1))=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.13/0.38  cnf(c_0_63, plain, (k6_relat_1(k9_relat_1(k6_relat_1(X1),X2))=k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_51])])).
% 0.13/0.38  cnf(c_0_64, negated_conjecture, (k4_xboole_0(esk2_0,k4_xboole_0(X1,esk1_0))=esk2_0), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.13/0.38  cnf(c_0_65, plain, (k5_relat_1(k4_relat_1(X1),k6_relat_1(X2))=k4_relat_1(k5_relat_1(k6_relat_1(X2),X1))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_51])])).
% 0.13/0.38  cnf(c_0_66, plain, (k4_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))=k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))), inference(spm,[status(thm)],[c_0_62, c_0_42])).
% 0.13/0.38  cnf(c_0_67, plain, (k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))=k9_relat_1(k6_relat_1(X2),X1)), inference(spm,[status(thm)],[c_0_41, c_0_63])).
% 0.13/0.38  cnf(c_0_68, negated_conjecture, (k5_relat_1(k6_relat_1(esk1_0),k6_relat_1(esk2_0))=k6_relat_1(esk2_0)), inference(spm,[status(thm)],[c_0_42, c_0_64])).
% 0.13/0.38  cnf(c_0_69, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_62]), c_0_66]), c_0_51])])).
% 0.13/0.38  cnf(c_0_70, negated_conjecture, (k9_relat_1(k6_relat_1(esk1_0),esk2_0)!=esk2_0), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.13/0.38  cnf(c_0_71, plain, (k9_relat_1(k6_relat_1(X1),X2)=k4_xboole_0(X1,k4_xboole_0(X1,X2))), inference(rw,[status(thm)],[c_0_49, c_0_67])).
% 0.13/0.38  cnf(c_0_72, negated_conjecture, (k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))=k6_relat_1(esk2_0)), inference(rw,[status(thm)],[c_0_68, c_0_69])).
% 0.13/0.38  cnf(c_0_73, negated_conjecture, (k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0))!=esk2_0), inference(rw,[status(thm)],[c_0_70, c_0_71])).
% 0.13/0.38  cnf(c_0_74, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_72]), c_0_41]), c_0_71]), c_0_51])]), c_0_73]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 75
% 0.13/0.38  # Proof object clause steps            : 40
% 0.13/0.38  # Proof object formula steps           : 35
% 0.13/0.38  # Proof object conjectures             : 13
% 0.13/0.38  # Proof object clause conjectures      : 10
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 18
% 0.13/0.38  # Proof object initial formulas used   : 17
% 0.13/0.38  # Proof object generating inferences   : 15
% 0.13/0.38  # Proof object simplifying inferences  : 25
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 17
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 21
% 0.13/0.38  # Removed in clause preprocessing      : 4
% 0.13/0.38  # Initial clauses in saturation        : 17
% 0.13/0.38  # Processed clauses                    : 100
% 0.13/0.38  # ...of these trivial                  : 5
% 0.13/0.38  # ...subsumed                          : 13
% 0.13/0.38  # ...remaining for further processing  : 82
% 0.13/0.38  # Other redundant clauses eliminated   : 0
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 0
% 0.13/0.38  # Backward-rewritten                   : 10
% 0.13/0.38  # Generated clauses                    : 406
% 0.13/0.38  # ...of the previous two non-trivial   : 259
% 0.13/0.38  # Contextual simplify-reflections      : 0
% 0.13/0.38  # Paramodulations                      : 406
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 0
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 55
% 0.13/0.38  #    Positive orientable unit clauses  : 35
% 0.13/0.38  #    Positive unorientable unit clauses: 2
% 0.13/0.38  #    Negative unit clauses             : 1
% 0.13/0.38  #    Non-unit-clauses                  : 17
% 0.13/0.38  # Current number of unprocessed clauses: 189
% 0.13/0.38  # ...number of literals in the above   : 247
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 31
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 87
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 77
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 12
% 0.13/0.38  # Unit Clause-clause subsumption calls : 6
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 40
% 0.13/0.38  # BW rewrite match successes           : 26
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 5437
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.035 s
% 0.13/0.38  # System time              : 0.004 s
% 0.13/0.38  # Total time               : 0.038 s
% 0.13/0.38  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
