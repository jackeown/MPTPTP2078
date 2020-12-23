%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:48:39 EST 2020

% Result     : Theorem 0.53s
% Output     : CNFRefutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :  124 (4919 expanded)
%              Number of clauses        :   79 (2216 expanded)
%              Number of leaves         :   22 (1348 expanded)
%              Depth                    :   22
%              Number of atoms          :  220 (6105 expanded)
%              Number of equality atoms :   49 (4179 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t51_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(t31_xboole_1,axiom,(
    ! [X1,X2,X3] : r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)),k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

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

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

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

fof(c_0_22,plain,(
    ! [X46,X47] : k1_setfam_1(k2_tarski(X46,X47)) = k3_xboole_0(X46,X47) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_23,plain,(
    ! [X39,X40] : k1_enumset1(X39,X39,X40) = k2_tarski(X39,X40) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_24,plain,(
    ! [X19,X20] : k4_xboole_0(X19,X20) = k5_xboole_0(X19,k3_xboole_0(X19,X20)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_25,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_26,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_27,plain,(
    ! [X11,X12,X14,X15,X16] :
      ( ( r1_xboole_0(X11,X12)
        | r2_hidden(esk2_2(X11,X12),k3_xboole_0(X11,X12)) )
      & ( ~ r2_hidden(X16,k3_xboole_0(X14,X15))
        | ~ r1_xboole_0(X14,X15) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_28,plain,(
    ! [X41,X42,X43] : k2_enumset1(X41,X41,X42,X43) = k1_enumset1(X41,X42,X43) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_29,plain,(
    ! [X37,X38] : r1_xboole_0(k4_xboole_0(X37,X38),X38) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_32,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_33,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk2_2(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_35,plain,(
    ! [X10] : k3_xboole_0(X10,X10) = X10 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

cnf(c_0_36,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_38,plain,
    ( ~ r1_xboole_0(X2,X3)
    | ~ r2_hidden(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_31]),c_0_33])).

cnf(c_0_39,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk2_2(X1,X2),k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_31]),c_0_33])).

cnf(c_0_40,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_41,plain,
    ( r1_xboole_0(k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_37]),c_0_33])).

cnf(c_0_42,plain,
    ( r2_hidden(esk2_2(X1,X2),k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))
    | ~ r2_hidden(X3,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_43,plain,
    ( k1_setfam_1(k2_enumset1(X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_31]),c_0_33])).

fof(c_0_44,plain,(
    ! [X4,X5,X6,X7,X8] :
      ( ( ~ r1_tarski(X4,X5)
        | ~ r2_hidden(X6,X4)
        | r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_2(X7,X8),X7)
        | r1_tarski(X7,X8) )
      & ( ~ r2_hidden(esk1_2(X7,X8),X8)
        | r1_tarski(X7,X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_45,plain,(
    ! [X26,X27] :
      ( ~ r1_tarski(X26,X27)
      | k3_xboole_0(X26,X27) = X26 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_46,plain,(
    ! [X33,X34] : r1_tarski(k4_xboole_0(X33,X34),X33) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_47,plain,(
    ! [X17,X18] :
      ( ( r1_tarski(X17,X18)
        | X17 != X18 )
      & ( r1_tarski(X18,X17)
        | X17 != X18 )
      & ( ~ r1_tarski(X17,X18)
        | ~ r1_tarski(X18,X17)
        | X17 = X18 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_48,plain,(
    ! [X29] : r1_tarski(k1_xboole_0,X29) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_49,plain,
    ( ~ r2_hidden(X1,k1_setfam_1(k2_enumset1(k5_xboole_0(X2,k1_setfam_1(k2_enumset1(X2,X2,X2,X3))),k5_xboole_0(X2,k1_setfam_1(k2_enumset1(X2,X2,X2,X3))),k5_xboole_0(X2,k1_setfam_1(k2_enumset1(X2,X2,X2,X3))),X3))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_41])).

cnf(c_0_50,plain,
    ( r2_hidden(esk2_2(X1,X1),X1)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_51,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

fof(c_0_52,plain,(
    ! [X44,X45] : k3_tarski(k2_tarski(X44,X45)) = k2_xboole_0(X44,X45) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

cnf(c_0_53,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_54,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_55,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_56,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_57,plain,
    ( ~ r2_hidden(X1,k1_setfam_1(k2_enumset1(k5_xboole_0(X2,X2),k5_xboole_0(X2,X2),k5_xboole_0(X2,X2),X2))) ),
    inference(spm,[status(thm)],[c_0_49,c_0_43])).

cnf(c_0_58,plain,
    ( r2_hidden(esk2_2(X1,X1),X1)
    | r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

fof(c_0_59,plain,(
    ! [X35,X36] : k2_xboole_0(k3_xboole_0(X35,X36),k4_xboole_0(X35,X36)) = X35 ),
    inference(variable_rename,[status(thm)],[t51_xboole_1])).

cnf(c_0_60,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_61,plain,
    ( k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_31]),c_0_33])).

cnf(c_0_62,plain,
    ( r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_37]),c_0_33])).

cnf(c_0_63,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_64,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(k5_xboole_0(X1,X1),k5_xboole_0(X1,X1),k5_xboole_0(X1,X1),X1)),X2) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

fof(c_0_65,plain,(
    ! [X30,X31,X32] : r1_tarski(k2_xboole_0(k3_xboole_0(X30,X31),k3_xboole_0(X30,X32)),k2_xboole_0(X31,X32)) ),
    inference(variable_rename,[status(thm)],[t31_xboole_1])).

cnf(c_0_66,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_67,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_60,c_0_26])).

cnf(c_0_68,plain,
    ( k1_setfam_1(k2_enumset1(k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))),k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))),k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))),X1)) = k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_69,plain,
    ( k1_setfam_1(k2_enumset1(k5_xboole_0(X1,X1),k5_xboole_0(X1,X1),k5_xboole_0(X1,X1),X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

fof(c_0_70,plain,(
    ! [X28] : k3_xboole_0(X28,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

cnf(c_0_71,plain,
    ( r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)),k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_72,plain,
    ( k3_tarski(k2_enumset1(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_67]),c_0_31]),c_0_31]),c_0_37]),c_0_33]),c_0_33]),c_0_33]),c_0_33])).

cnf(c_0_73,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_43]),c_0_69])).

cnf(c_0_74,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

fof(c_0_75,plain,(
    ! [X21,X22] : r1_tarski(k3_xboole_0(X21,X22),X21) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

fof(c_0_76,plain,(
    ! [X48,X49] :
      ( ( ~ m1_subset_1(X48,k1_zfmisc_1(X49))
        | r1_tarski(X48,X49) )
      & ( ~ r1_tarski(X48,X49)
        | m1_subset_1(X48,k1_zfmisc_1(X49)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_77,plain,
    ( r1_tarski(k3_tarski(k2_enumset1(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),k1_setfam_1(k2_enumset1(X1,X1,X1,X3)))),k3_tarski(k2_enumset1(X2,X2,X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_67]),c_0_67]),c_0_31]),c_0_31]),c_0_31]),c_0_33]),c_0_33]),c_0_33]),c_0_33]),c_0_33])).

cnf(c_0_78,plain,
    ( k3_tarski(k2_enumset1(X1,X1,X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_43]),c_0_73])).

cnf(c_0_79,plain,
    ( k1_setfam_1(k2_enumset1(X1,X1,X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_31]),c_0_33])).

fof(c_0_80,plain,(
    ! [X52,X53,X54] :
      ( ~ v1_relat_1(X52)
      | ~ v1_relat_1(X53)
      | ~ v1_relat_1(X54)
      | ~ r1_tarski(X52,X53)
      | r1_tarski(k5_relat_1(X54,X52),k5_relat_1(X54,X53)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_relat_1])])])).

cnf(c_0_81,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

fof(c_0_82,plain,(
    ! [X50,X51] :
      ( ~ v1_relat_1(X50)
      | ~ m1_subset_1(X51,k1_zfmisc_1(X50))
      | v1_relat_1(X51) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

cnf(c_0_83,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_84,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_79]),c_0_78])).

cnf(c_0_85,plain,
    ( r1_tarski(k5_relat_1(X3,X1),k5_relat_1(X3,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_86,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_31]),c_0_33])).

cnf(c_0_87,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_88,plain,
    ( m1_subset_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

fof(c_0_89,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ! [X3] :
                ( v1_relat_1(X3)
               => r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,X3))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t52_relat_1])).

fof(c_0_90,plain,(
    ! [X23,X24,X25] :
      ( ~ r1_tarski(X23,X24)
      | ~ r1_tarski(X23,X25)
      | r1_tarski(X23,k3_xboole_0(X24,X25)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).

cnf(c_0_91,plain,
    ( r1_tarski(k5_relat_1(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3))),k5_relat_1(X1,X2))
    | ~ v1_relat_1(k1_setfam_1(k2_enumset1(X2,X2,X2,X3)))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_92,plain,
    ( v1_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_87,c_0_88])).

fof(c_0_93,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & v1_relat_1(esk4_0)
    & v1_relat_1(esk5_0)
    & ~ r1_tarski(k5_relat_1(esk3_0,k3_xboole_0(esk4_0,esk5_0)),k3_xboole_0(k5_relat_1(esk3_0,esk4_0),k5_relat_1(esk3_0,esk5_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_89])])])).

cnf(c_0_94,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_90])).

cnf(c_0_95,plain,
    ( r1_tarski(k5_relat_1(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3))),k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3) ),
    inference(spm,[status(thm)],[c_0_91,c_0_92])).

cnf(c_0_96,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_93])).

cnf(c_0_97,plain,
    ( r1_tarski(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3)))
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_94,c_0_31]),c_0_33])).

cnf(c_0_98,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_99,negated_conjecture,
    ( r1_tarski(k5_relat_1(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,esk5_0))),k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_95,c_0_96])).

cnf(c_0_100,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_93])).

cnf(c_0_101,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),k1_setfam_1(k2_enumset1(X3,X3,X3,X1)))
    | ~ r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X3) ),
    inference(spm,[status(thm)],[c_0_97,c_0_86])).

cnf(c_0_102,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_98])).

cnf(c_0_103,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk3_0,k1_setfam_1(k2_enumset1(X1,X1,X1,esk5_0))),k5_relat_1(esk3_0,X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_99,c_0_100])).

cnf(c_0_104,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_93])).

cnf(c_0_105,negated_conjecture,
    ( r1_tarski(k5_relat_1(X1,k1_setfam_1(k2_enumset1(esk5_0,esk5_0,esk5_0,X2))),k5_relat_1(X1,esk5_0))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_95,c_0_96])).

cnf(c_0_106,plain,
    ( m1_subset_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_83,c_0_86])).

cnf(c_0_107,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),k1_setfam_1(k2_enumset1(X2,X2,X2,X1))) ),
    inference(spm,[status(thm)],[c_0_101,c_0_84])).

cnf(c_0_108,plain,
    ( r1_tarski(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X1)))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_97,c_0_102])).

cnf(c_0_109,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk3_0,k1_setfam_1(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0))),k5_relat_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_103,c_0_104])).

cnf(c_0_110,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk3_0,k1_setfam_1(k2_enumset1(esk5_0,esk5_0,esk5_0,X1))),k5_relat_1(esk3_0,esk5_0))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_105,c_0_100])).

cnf(c_0_111,plain,
    ( v1_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_87,c_0_106])).

cnf(c_0_112,plain,
    ( k1_setfam_1(k2_enumset1(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X1)) = k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_86])).

cnf(c_0_113,plain,
    ( k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) = k1_setfam_1(k2_enumset1(X2,X2,X2,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_107]),c_0_107])])).

cnf(c_0_114,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk3_0,k1_setfam_1(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0))),k1_setfam_1(k2_enumset1(k5_relat_1(esk3_0,esk4_0),k5_relat_1(esk3_0,esk4_0),k5_relat_1(esk3_0,esk4_0),k5_relat_1(esk3_0,k1_setfam_1(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0)))))) ),
    inference(spm,[status(thm)],[c_0_108,c_0_109])).

cnf(c_0_115,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk3_0,k1_setfam_1(k2_enumset1(esk5_0,esk5_0,esk5_0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))))),k5_relat_1(esk3_0,esk5_0))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_110,c_0_111])).

cnf(c_0_116,plain,
    ( k1_setfam_1(k2_enumset1(X1,X1,X1,k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))) = k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) ),
    inference(rw,[status(thm)],[c_0_112,c_0_113])).

cnf(c_0_117,negated_conjecture,
    ( k1_setfam_1(k2_enumset1(k5_relat_1(esk3_0,esk4_0),k5_relat_1(esk3_0,esk4_0),k5_relat_1(esk3_0,esk4_0),k5_relat_1(esk3_0,k1_setfam_1(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0))))) = k5_relat_1(esk3_0,k1_setfam_1(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_114]),c_0_84])])).

cnf(c_0_118,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk3_0,k1_setfam_1(k2_enumset1(esk5_0,esk5_0,esk5_0,X1))),k5_relat_1(esk3_0,esk5_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_96]),c_0_116])).

cnf(c_0_119,negated_conjecture,
    ( ~ r1_tarski(k5_relat_1(esk3_0,k3_xboole_0(esk4_0,esk5_0)),k3_xboole_0(k5_relat_1(esk3_0,esk4_0),k5_relat_1(esk3_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_93])).

cnf(c_0_120,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk3_0,k1_setfam_1(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0))),k1_setfam_1(k2_enumset1(X1,X1,X1,k5_relat_1(esk3_0,esk4_0))))
    | ~ r1_tarski(k5_relat_1(esk3_0,k1_setfam_1(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0))),X1) ),
    inference(spm,[status(thm)],[c_0_101,c_0_117])).

cnf(c_0_121,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk3_0,k1_setfam_1(k2_enumset1(X1,X1,X1,esk5_0))),k5_relat_1(esk3_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_118,c_0_113])).

cnf(c_0_122,negated_conjecture,
    ( ~ r1_tarski(k5_relat_1(esk3_0,k1_setfam_1(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0))),k1_setfam_1(k2_enumset1(k5_relat_1(esk3_0,esk4_0),k5_relat_1(esk3_0,esk4_0),k5_relat_1(esk3_0,esk4_0),k5_relat_1(esk3_0,esk5_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_119,c_0_31]),c_0_31]),c_0_33]),c_0_33])).

cnf(c_0_123,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_121]),c_0_113]),c_0_122]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:18:02 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.53/0.70  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_S2mI
% 0.53/0.70  # and selection function SelectCQArNTNpEqFirst.
% 0.53/0.70  #
% 0.53/0.70  # Preprocessing time       : 0.028 s
% 0.53/0.70  # Presaturation interreduction done
% 0.53/0.70  
% 0.53/0.70  # Proof found!
% 0.53/0.70  # SZS status Theorem
% 0.53/0.70  # SZS output start CNFRefutation
% 0.53/0.70  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.53/0.70  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.53/0.70  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.53/0.70  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.53/0.70  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.53/0.70  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 0.53/0.70  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.53/0.70  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.53/0.70  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.53/0.70  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.53/0.70  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.53/0.70  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.53/0.70  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.53/0.70  fof(t51_xboole_1, axiom, ![X1, X2]:k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 0.53/0.70  fof(t31_xboole_1, axiom, ![X1, X2, X3]:r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)),k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_xboole_1)).
% 0.53/0.70  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 0.53/0.70  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.53/0.70  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.53/0.70  fof(t48_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>r1_tarski(k5_relat_1(X3,X1),k5_relat_1(X3,X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_relat_1)).
% 0.53/0.70  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.53/0.70  fof(t52_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_relat_1)).
% 0.53/0.70  fof(t19_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(X1,k3_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 0.53/0.70  fof(c_0_22, plain, ![X46, X47]:k1_setfam_1(k2_tarski(X46,X47))=k3_xboole_0(X46,X47), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.53/0.70  fof(c_0_23, plain, ![X39, X40]:k1_enumset1(X39,X39,X40)=k2_tarski(X39,X40), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.53/0.70  fof(c_0_24, plain, ![X19, X20]:k4_xboole_0(X19,X20)=k5_xboole_0(X19,k3_xboole_0(X19,X20)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.53/0.70  cnf(c_0_25, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.53/0.70  cnf(c_0_26, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.53/0.70  fof(c_0_27, plain, ![X11, X12, X14, X15, X16]:((r1_xboole_0(X11,X12)|r2_hidden(esk2_2(X11,X12),k3_xboole_0(X11,X12)))&(~r2_hidden(X16,k3_xboole_0(X14,X15))|~r1_xboole_0(X14,X15))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.53/0.70  fof(c_0_28, plain, ![X41, X42, X43]:k2_enumset1(X41,X41,X42,X43)=k1_enumset1(X41,X42,X43), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.53/0.70  fof(c_0_29, plain, ![X37, X38]:r1_xboole_0(k4_xboole_0(X37,X38),X38), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 0.53/0.70  cnf(c_0_30, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.53/0.70  cnf(c_0_31, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_25, c_0_26])).
% 0.53/0.70  cnf(c_0_32, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.53/0.70  cnf(c_0_33, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.53/0.70  cnf(c_0_34, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk2_2(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.53/0.70  fof(c_0_35, plain, ![X10]:k3_xboole_0(X10,X10)=X10, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.53/0.70  cnf(c_0_36, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.53/0.70  cnf(c_0_37, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))), inference(rw,[status(thm)],[c_0_30, c_0_31])).
% 0.53/0.70  cnf(c_0_38, plain, (~r1_xboole_0(X2,X3)|~r2_hidden(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_31]), c_0_33])).
% 0.53/0.70  cnf(c_0_39, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk2_2(X1,X2),k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_31]), c_0_33])).
% 0.53/0.70  cnf(c_0_40, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.53/0.70  cnf(c_0_41, plain, (r1_xboole_0(k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_37]), c_0_33])).
% 0.53/0.70  cnf(c_0_42, plain, (r2_hidden(esk2_2(X1,X2),k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))|~r2_hidden(X3,k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.53/0.70  cnf(c_0_43, plain, (k1_setfam_1(k2_enumset1(X1,X1,X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_31]), c_0_33])).
% 0.53/0.70  fof(c_0_44, plain, ![X4, X5, X6, X7, X8]:((~r1_tarski(X4,X5)|(~r2_hidden(X6,X4)|r2_hidden(X6,X5)))&((r2_hidden(esk1_2(X7,X8),X7)|r1_tarski(X7,X8))&(~r2_hidden(esk1_2(X7,X8),X8)|r1_tarski(X7,X8)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.53/0.70  fof(c_0_45, plain, ![X26, X27]:(~r1_tarski(X26,X27)|k3_xboole_0(X26,X27)=X26), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.53/0.70  fof(c_0_46, plain, ![X33, X34]:r1_tarski(k4_xboole_0(X33,X34),X33), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.53/0.70  fof(c_0_47, plain, ![X17, X18]:(((r1_tarski(X17,X18)|X17!=X18)&(r1_tarski(X18,X17)|X17!=X18))&(~r1_tarski(X17,X18)|~r1_tarski(X18,X17)|X17=X18)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.53/0.70  fof(c_0_48, plain, ![X29]:r1_tarski(k1_xboole_0,X29), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.53/0.70  cnf(c_0_49, plain, (~r2_hidden(X1,k1_setfam_1(k2_enumset1(k5_xboole_0(X2,k1_setfam_1(k2_enumset1(X2,X2,X2,X3))),k5_xboole_0(X2,k1_setfam_1(k2_enumset1(X2,X2,X2,X3))),k5_xboole_0(X2,k1_setfam_1(k2_enumset1(X2,X2,X2,X3))),X3)))), inference(spm,[status(thm)],[c_0_38, c_0_41])).
% 0.53/0.70  cnf(c_0_50, plain, (r2_hidden(esk2_2(X1,X1),X1)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.53/0.70  cnf(c_0_51, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.53/0.70  fof(c_0_52, plain, ![X44, X45]:k3_tarski(k2_tarski(X44,X45))=k2_xboole_0(X44,X45), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.53/0.70  cnf(c_0_53, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.53/0.70  cnf(c_0_54, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.53/0.70  cnf(c_0_55, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.53/0.70  cnf(c_0_56, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.53/0.70  cnf(c_0_57, plain, (~r2_hidden(X1,k1_setfam_1(k2_enumset1(k5_xboole_0(X2,X2),k5_xboole_0(X2,X2),k5_xboole_0(X2,X2),X2)))), inference(spm,[status(thm)],[c_0_49, c_0_43])).
% 0.53/0.70  cnf(c_0_58, plain, (r2_hidden(esk2_2(X1,X1),X1)|r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.53/0.70  fof(c_0_59, plain, ![X35, X36]:k2_xboole_0(k3_xboole_0(X35,X36),k4_xboole_0(X35,X36))=X35, inference(variable_rename,[status(thm)],[t51_xboole_1])).
% 0.53/0.70  cnf(c_0_60, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.53/0.70  cnf(c_0_61, plain, (k1_setfam_1(k2_enumset1(X1,X1,X1,X2))=X1|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_31]), c_0_33])).
% 0.53/0.70  cnf(c_0_62, plain, (r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_37]), c_0_33])).
% 0.53/0.70  cnf(c_0_63, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.53/0.70  cnf(c_0_64, plain, (r1_tarski(k1_setfam_1(k2_enumset1(k5_xboole_0(X1,X1),k5_xboole_0(X1,X1),k5_xboole_0(X1,X1),X1)),X2)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.53/0.70  fof(c_0_65, plain, ![X30, X31, X32]:r1_tarski(k2_xboole_0(k3_xboole_0(X30,X31),k3_xboole_0(X30,X32)),k2_xboole_0(X31,X32)), inference(variable_rename,[status(thm)],[t31_xboole_1])).
% 0.53/0.70  cnf(c_0_66, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.53/0.70  cnf(c_0_67, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_60, c_0_26])).
% 0.53/0.70  cnf(c_0_68, plain, (k1_setfam_1(k2_enumset1(k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))),k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))),k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))),X1))=k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.53/0.70  cnf(c_0_69, plain, (k1_setfam_1(k2_enumset1(k5_xboole_0(X1,X1),k5_xboole_0(X1,X1),k5_xboole_0(X1,X1),X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.53/0.70  fof(c_0_70, plain, ![X28]:k3_xboole_0(X28,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.53/0.70  cnf(c_0_71, plain, (r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)),k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.53/0.70  cnf(c_0_72, plain, (k3_tarski(k2_enumset1(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_67]), c_0_31]), c_0_31]), c_0_37]), c_0_33]), c_0_33]), c_0_33]), c_0_33])).
% 0.53/0.70  cnf(c_0_73, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_43]), c_0_69])).
% 0.53/0.70  cnf(c_0_74, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.53/0.70  fof(c_0_75, plain, ![X21, X22]:r1_tarski(k3_xboole_0(X21,X22),X21), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.53/0.70  fof(c_0_76, plain, ![X48, X49]:((~m1_subset_1(X48,k1_zfmisc_1(X49))|r1_tarski(X48,X49))&(~r1_tarski(X48,X49)|m1_subset_1(X48,k1_zfmisc_1(X49)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.53/0.70  cnf(c_0_77, plain, (r1_tarski(k3_tarski(k2_enumset1(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),k1_setfam_1(k2_enumset1(X1,X1,X1,X3)))),k3_tarski(k2_enumset1(X2,X2,X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71, c_0_67]), c_0_67]), c_0_31]), c_0_31]), c_0_31]), c_0_33]), c_0_33]), c_0_33]), c_0_33]), c_0_33])).
% 0.53/0.70  cnf(c_0_78, plain, (k3_tarski(k2_enumset1(X1,X1,X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_43]), c_0_73])).
% 0.53/0.70  cnf(c_0_79, plain, (k1_setfam_1(k2_enumset1(X1,X1,X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74, c_0_31]), c_0_33])).
% 0.53/0.70  fof(c_0_80, plain, ![X52, X53, X54]:(~v1_relat_1(X52)|(~v1_relat_1(X53)|(~v1_relat_1(X54)|(~r1_tarski(X52,X53)|r1_tarski(k5_relat_1(X54,X52),k5_relat_1(X54,X53)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_relat_1])])])).
% 0.53/0.70  cnf(c_0_81, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.53/0.70  fof(c_0_82, plain, ![X50, X51]:(~v1_relat_1(X50)|(~m1_subset_1(X51,k1_zfmisc_1(X50))|v1_relat_1(X51))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.53/0.70  cnf(c_0_83, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_76])).
% 0.53/0.70  cnf(c_0_84, plain, (r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_79]), c_0_78])).
% 0.53/0.70  cnf(c_0_85, plain, (r1_tarski(k5_relat_1(X3,X1),k5_relat_1(X3,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X3)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_80])).
% 0.53/0.70  cnf(c_0_86, plain, (r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81, c_0_31]), c_0_33])).
% 0.53/0.70  cnf(c_0_87, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_82])).
% 0.53/0.70  cnf(c_0_88, plain, (m1_subset_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 0.53/0.70  fof(c_0_89, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,X3))))))), inference(assume_negation,[status(cth)],[t52_relat_1])).
% 0.53/0.70  fof(c_0_90, plain, ![X23, X24, X25]:(~r1_tarski(X23,X24)|~r1_tarski(X23,X25)|r1_tarski(X23,k3_xboole_0(X24,X25))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).
% 0.53/0.70  cnf(c_0_91, plain, (r1_tarski(k5_relat_1(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3))),k5_relat_1(X1,X2))|~v1_relat_1(k1_setfam_1(k2_enumset1(X2,X2,X2,X3)))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_85, c_0_86])).
% 0.53/0.70  cnf(c_0_92, plain, (v1_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_87, c_0_88])).
% 0.53/0.70  fof(c_0_93, negated_conjecture, (v1_relat_1(esk3_0)&(v1_relat_1(esk4_0)&(v1_relat_1(esk5_0)&~r1_tarski(k5_relat_1(esk3_0,k3_xboole_0(esk4_0,esk5_0)),k3_xboole_0(k5_relat_1(esk3_0,esk4_0),k5_relat_1(esk3_0,esk5_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_89])])])).
% 0.53/0.70  cnf(c_0_94, plain, (r1_tarski(X1,k3_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_90])).
% 0.53/0.70  cnf(c_0_95, plain, (r1_tarski(k5_relat_1(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3))),k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X3)), inference(spm,[status(thm)],[c_0_91, c_0_92])).
% 0.53/0.70  cnf(c_0_96, negated_conjecture, (v1_relat_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_93])).
% 0.53/0.70  cnf(c_0_97, plain, (r1_tarski(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3)))|~r1_tarski(X1,X3)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_94, c_0_31]), c_0_33])).
% 0.53/0.70  cnf(c_0_98, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.53/0.70  cnf(c_0_99, negated_conjecture, (r1_tarski(k5_relat_1(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,esk5_0))),k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_95, c_0_96])).
% 0.53/0.70  cnf(c_0_100, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_93])).
% 0.53/0.70  cnf(c_0_101, plain, (r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),k1_setfam_1(k2_enumset1(X3,X3,X3,X1)))|~r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X3)), inference(spm,[status(thm)],[c_0_97, c_0_86])).
% 0.53/0.70  cnf(c_0_102, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_98])).
% 0.53/0.70  cnf(c_0_103, negated_conjecture, (r1_tarski(k5_relat_1(esk3_0,k1_setfam_1(k2_enumset1(X1,X1,X1,esk5_0))),k5_relat_1(esk3_0,X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_99, c_0_100])).
% 0.53/0.70  cnf(c_0_104, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_93])).
% 0.53/0.70  cnf(c_0_105, negated_conjecture, (r1_tarski(k5_relat_1(X1,k1_setfam_1(k2_enumset1(esk5_0,esk5_0,esk5_0,X2))),k5_relat_1(X1,esk5_0))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_95, c_0_96])).
% 0.53/0.70  cnf(c_0_106, plain, (m1_subset_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_83, c_0_86])).
% 0.53/0.70  cnf(c_0_107, plain, (r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),k1_setfam_1(k2_enumset1(X2,X2,X2,X1)))), inference(spm,[status(thm)],[c_0_101, c_0_84])).
% 0.53/0.70  cnf(c_0_108, plain, (r1_tarski(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X1)))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_97, c_0_102])).
% 0.53/0.70  cnf(c_0_109, negated_conjecture, (r1_tarski(k5_relat_1(esk3_0,k1_setfam_1(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0))),k5_relat_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_103, c_0_104])).
% 0.53/0.70  cnf(c_0_110, negated_conjecture, (r1_tarski(k5_relat_1(esk3_0,k1_setfam_1(k2_enumset1(esk5_0,esk5_0,esk5_0,X1))),k5_relat_1(esk3_0,esk5_0))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_105, c_0_100])).
% 0.53/0.70  cnf(c_0_111, plain, (v1_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_87, c_0_106])).
% 0.53/0.70  cnf(c_0_112, plain, (k1_setfam_1(k2_enumset1(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X1))=k1_setfam_1(k2_enumset1(X1,X1,X1,X2))), inference(spm,[status(thm)],[c_0_61, c_0_86])).
% 0.53/0.70  cnf(c_0_113, plain, (k1_setfam_1(k2_enumset1(X1,X1,X1,X2))=k1_setfam_1(k2_enumset1(X2,X2,X2,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_107]), c_0_107])])).
% 0.53/0.70  cnf(c_0_114, negated_conjecture, (r1_tarski(k5_relat_1(esk3_0,k1_setfam_1(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0))),k1_setfam_1(k2_enumset1(k5_relat_1(esk3_0,esk4_0),k5_relat_1(esk3_0,esk4_0),k5_relat_1(esk3_0,esk4_0),k5_relat_1(esk3_0,k1_setfam_1(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0))))))), inference(spm,[status(thm)],[c_0_108, c_0_109])).
% 0.53/0.70  cnf(c_0_115, negated_conjecture, (r1_tarski(k5_relat_1(esk3_0,k1_setfam_1(k2_enumset1(esk5_0,esk5_0,esk5_0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))))),k5_relat_1(esk3_0,esk5_0))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_110, c_0_111])).
% 0.53/0.70  cnf(c_0_116, plain, (k1_setfam_1(k2_enumset1(X1,X1,X1,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))))=k1_setfam_1(k2_enumset1(X1,X1,X1,X2))), inference(rw,[status(thm)],[c_0_112, c_0_113])).
% 0.53/0.70  cnf(c_0_117, negated_conjecture, (k1_setfam_1(k2_enumset1(k5_relat_1(esk3_0,esk4_0),k5_relat_1(esk3_0,esk4_0),k5_relat_1(esk3_0,esk4_0),k5_relat_1(esk3_0,k1_setfam_1(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0)))))=k5_relat_1(esk3_0,k1_setfam_1(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_114]), c_0_84])])).
% 0.53/0.70  cnf(c_0_118, negated_conjecture, (r1_tarski(k5_relat_1(esk3_0,k1_setfam_1(k2_enumset1(esk5_0,esk5_0,esk5_0,X1))),k5_relat_1(esk3_0,esk5_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_96]), c_0_116])).
% 0.53/0.70  cnf(c_0_119, negated_conjecture, (~r1_tarski(k5_relat_1(esk3_0,k3_xboole_0(esk4_0,esk5_0)),k3_xboole_0(k5_relat_1(esk3_0,esk4_0),k5_relat_1(esk3_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_93])).
% 0.53/0.70  cnf(c_0_120, negated_conjecture, (r1_tarski(k5_relat_1(esk3_0,k1_setfam_1(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0))),k1_setfam_1(k2_enumset1(X1,X1,X1,k5_relat_1(esk3_0,esk4_0))))|~r1_tarski(k5_relat_1(esk3_0,k1_setfam_1(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0))),X1)), inference(spm,[status(thm)],[c_0_101, c_0_117])).
% 0.53/0.70  cnf(c_0_121, negated_conjecture, (r1_tarski(k5_relat_1(esk3_0,k1_setfam_1(k2_enumset1(X1,X1,X1,esk5_0))),k5_relat_1(esk3_0,esk5_0))), inference(spm,[status(thm)],[c_0_118, c_0_113])).
% 0.53/0.70  cnf(c_0_122, negated_conjecture, (~r1_tarski(k5_relat_1(esk3_0,k1_setfam_1(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0))),k1_setfam_1(k2_enumset1(k5_relat_1(esk3_0,esk4_0),k5_relat_1(esk3_0,esk4_0),k5_relat_1(esk3_0,esk4_0),k5_relat_1(esk3_0,esk5_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_119, c_0_31]), c_0_31]), c_0_33]), c_0_33])).
% 0.53/0.70  cnf(c_0_123, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120, c_0_121]), c_0_113]), c_0_122]), ['proof']).
% 0.53/0.70  # SZS output end CNFRefutation
% 0.53/0.70  # Proof object total steps             : 124
% 0.53/0.70  # Proof object clause steps            : 79
% 0.53/0.70  # Proof object formula steps           : 45
% 0.53/0.70  # Proof object conjectures             : 20
% 0.53/0.70  # Proof object clause conjectures      : 17
% 0.53/0.70  # Proof object formula conjectures     : 3
% 0.53/0.70  # Proof object initial clauses used    : 27
% 0.53/0.70  # Proof object initial formulas used   : 22
% 0.53/0.70  # Proof object generating inferences   : 35
% 0.53/0.70  # Proof object simplifying inferences  : 56
% 0.53/0.70  # Training examples: 0 positive, 0 negative
% 0.53/0.70  # Parsed axioms                        : 22
% 0.53/0.70  # Removed by relevancy pruning/SinE    : 0
% 0.53/0.70  # Initial clauses                      : 31
% 0.53/0.70  # Removed in clause preprocessing      : 5
% 0.53/0.70  # Initial clauses in saturation        : 26
% 0.53/0.70  # Processed clauses                    : 3214
% 0.53/0.70  # ...of these trivial                  : 263
% 0.53/0.70  # ...subsumed                          : 1386
% 0.53/0.70  # ...remaining for further processing  : 1565
% 0.53/0.70  # Other redundant clauses eliminated   : 2
% 0.53/0.70  # Clauses deleted for lack of memory   : 0
% 0.53/0.70  # Backward-subsumed                    : 133
% 0.53/0.70  # Backward-rewritten                   : 308
% 0.53/0.70  # Generated clauses                    : 23073
% 0.53/0.70  # ...of the previous two non-trivial   : 19100
% 0.53/0.70  # Contextual simplify-reflections      : 40
% 0.53/0.70  # Paramodulations                      : 23071
% 0.53/0.70  # Factorizations                       : 0
% 0.53/0.70  # Equation resolutions                 : 2
% 0.53/0.70  # Propositional unsat checks           : 0
% 0.53/0.70  #    Propositional check models        : 0
% 0.53/0.70  #    Propositional check unsatisfiable : 0
% 0.53/0.70  #    Propositional clauses             : 0
% 0.53/0.70  #    Propositional clauses after purity: 0
% 0.53/0.70  #    Propositional unsat core size     : 0
% 0.53/0.70  #    Propositional preprocessing time  : 0.000
% 0.53/0.70  #    Propositional encoding time       : 0.000
% 0.53/0.70  #    Propositional solver time         : 0.000
% 0.53/0.70  #    Success case prop preproc time    : 0.000
% 0.53/0.70  #    Success case prop encoding time   : 0.000
% 0.53/0.70  #    Success case prop solver time     : 0.000
% 0.53/0.70  # Current number of processed clauses  : 1097
% 0.53/0.70  #    Positive orientable unit clauses  : 375
% 0.53/0.70  #    Positive unorientable unit clauses: 1
% 0.53/0.70  #    Negative unit clauses             : 5
% 0.53/0.70  #    Non-unit-clauses                  : 716
% 0.53/0.70  # Current number of unprocessed clauses: 15729
% 0.53/0.70  # ...number of literals in the above   : 28313
% 0.53/0.70  # Current number of archived formulas  : 0
% 0.53/0.70  # Current number of archived clauses   : 471
% 0.53/0.70  # Clause-clause subsumption calls (NU) : 73121
% 0.53/0.70  # Rec. Clause-clause subsumption calls : 60258
% 0.53/0.70  # Non-unit clause-clause subsumptions  : 1310
% 0.53/0.70  # Unit Clause-clause subsumption calls : 27548
% 0.53/0.70  # Rewrite failures with RHS unbound    : 0
% 0.53/0.70  # BW rewrite match attempts            : 5550
% 0.53/0.70  # BW rewrite match successes           : 446
% 0.53/0.70  # Condensation attempts                : 0
% 0.53/0.70  # Condensation successes               : 0
% 0.53/0.70  # Termbank termtop insertions          : 761873
% 0.53/0.70  
% 0.53/0.70  # -------------------------------------------------
% 0.53/0.70  # User time                : 0.358 s
% 0.53/0.70  # System time              : 0.015 s
% 0.53/0.70  # Total time               : 0.373 s
% 0.53/0.70  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
