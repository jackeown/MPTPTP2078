%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:45:59 EST 2020

% Result     : Theorem 3.50s
% Output     : CNFRefutation 3.50s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 878 expanded)
%              Number of clauses        :   78 ( 391 expanded)
%              Number of leaves         :   27 ( 238 expanded)
%              Depth                    :   14
%              Number of atoms          :  212 (1349 expanded)
%              Number of equality atoms :  100 ( 728 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t22_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = k3_subset_1(X1,k1_subset_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(d3_subset_1,axiom,(
    ! [X1] : k1_subset_1(X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t46_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t83_zfmisc_1,axiom,(
    ! [X1,X2] : k1_zfmisc_1(k3_xboole_0(X1,X2)) = k3_xboole_0(k1_zfmisc_1(X1),k1_zfmisc_1(X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_zfmisc_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t31_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( r1_tarski(X2,X3)
          <=> r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t79_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).

fof(t22_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(t39_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( r1_tarski(k3_subset_1(X1,X2),X2)
      <=> X2 = k2_subset_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_subset_1)).

fof(dt_k6_subset_1,axiom,(
    ! [X1,X2] : m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(c_0_27,plain,(
    ! [X46] : k2_subset_1(X46) = k3_subset_1(X46,k1_subset_1(X46)) ),
    inference(variable_rename,[status(thm)],[t22_subset_1])).

fof(c_0_28,plain,(
    ! [X36] : k2_subset_1(X36) = X36 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

fof(c_0_29,plain,(
    ! [X35] : k1_subset_1(X35) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[d3_subset_1])).

fof(c_0_30,plain,(
    ! [X29,X30] : k3_tarski(k2_tarski(X29,X30)) = k2_xboole_0(X29,X30) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_31,plain,(
    ! [X24,X25] : k1_enumset1(X24,X24,X25) = k2_tarski(X24,X25) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_32,plain,(
    ! [X42,X43] :
      ( ~ m1_subset_1(X43,k1_zfmisc_1(X42))
      | k3_subset_1(X42,k3_subset_1(X42,X43)) = X43 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

cnf(c_0_33,plain,
    ( k2_subset_1(X1) = k3_subset_1(X1,k1_subset_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,plain,
    ( k1_subset_1(X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_36,plain,(
    ! [X50] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X50)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

fof(c_0_37,plain,(
    ! [X39] : m1_subset_1(k2_subset_1(X39),k1_zfmisc_1(X39)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_38,plain,(
    ! [X9,X10] :
      ( ( k4_xboole_0(X9,X10) != k1_xboole_0
        | r1_tarski(X9,X10) )
      & ( ~ r1_tarski(X9,X10)
        | k4_xboole_0(X9,X10) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_39,plain,(
    ! [X11,X12] : k4_xboole_0(X11,X12) = k5_xboole_0(X11,k3_xboole_0(X11,X12)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_40,plain,(
    ! [X18,X19] : k4_xboole_0(X18,k2_xboole_0(X18,X19)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t46_xboole_1])).

cnf(c_0_41,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_42,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_43,plain,(
    ! [X26,X27,X28] : k2_enumset1(X26,X26,X27,X28) = k1_enumset1(X26,X27,X28) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_44,plain,(
    ! [X33,X34] : k1_zfmisc_1(k3_xboole_0(X33,X34)) = k3_xboole_0(k1_zfmisc_1(X33),k1_zfmisc_1(X34)) ),
    inference(variable_rename,[status(thm)],[t83_zfmisc_1])).

fof(c_0_45,plain,(
    ! [X15,X16] :
      ( ~ r1_tarski(X15,X16)
      | k3_xboole_0(X15,X16) = X15 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_46,plain,(
    ! [X47,X48,X49] :
      ( ( ~ r1_tarski(X48,X49)
        | r1_tarski(k3_subset_1(X47,X49),k3_subset_1(X47,X48))
        | ~ m1_subset_1(X49,k1_zfmisc_1(X47))
        | ~ m1_subset_1(X48,k1_zfmisc_1(X47)) )
      & ( ~ r1_tarski(k3_subset_1(X47,X49),k3_subset_1(X47,X48))
        | r1_tarski(X48,X49)
        | ~ m1_subset_1(X49,k1_zfmisc_1(X47))
        | ~ m1_subset_1(X48,k1_zfmisc_1(X47)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_subset_1])])])])).

cnf(c_0_47,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_48,plain,
    ( X1 = k3_subset_1(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_34]),c_0_35])).

cnf(c_0_49,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_50,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_51,plain,(
    ! [X17] : r1_tarski(k1_xboole_0,X17) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_52,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_53,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_54,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_55,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_56,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

fof(c_0_57,plain,(
    ! [X22,X23] : k2_tarski(X22,X23) = k2_tarski(X23,X22) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

fof(c_0_58,plain,(
    ! [X31,X32] :
      ( ~ r1_tarski(X31,X32)
      | r1_tarski(k1_zfmisc_1(X31),k1_zfmisc_1(X32)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_zfmisc_1])])).

cnf(c_0_59,plain,
    ( k1_zfmisc_1(k3_xboole_0(X1,X2)) = k3_xboole_0(k1_zfmisc_1(X1),k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_60,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_61,plain,
    ( r1_tarski(X3,X2)
    | ~ r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_62,plain,
    ( k3_subset_1(X1,X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49])])).

cnf(c_0_63,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_50,c_0_34])).

cnf(c_0_64,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_65,plain,
    ( r1_tarski(X1,X2)
    | k5_xboole_0(X1,k3_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_66,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k3_tarski(k2_enumset1(X1,X1,X1,X2)))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_55]),c_0_53]),c_0_56])).

cnf(c_0_67,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

fof(c_0_68,plain,(
    ! [X13,X14] : k2_xboole_0(X13,k3_xboole_0(X13,X14)) = X13 ),
    inference(variable_rename,[status(thm)],[t22_xboole_1])).

cnf(c_0_69,plain,
    ( r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_70,plain,
    ( k1_zfmisc_1(k3_xboole_0(X1,X2)) = k1_zfmisc_1(X1)
    | ~ r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_71,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63]),c_0_64])])).

fof(c_0_72,plain,(
    ! [X7,X8] :
      ( ( r1_tarski(X7,X8)
        | X7 != X8 )
      & ( r1_tarski(X8,X7)
        | X7 != X8 )
      & ( ~ r1_tarski(X7,X8)
        | ~ r1_tarski(X8,X7)
        | X7 = X8 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_73,plain,(
    ! [X20,X21] : k2_xboole_0(X20,X21) = k5_xboole_0(X20,k4_xboole_0(X21,X20)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_74,plain,(
    ! [X37,X38] :
      ( ~ m1_subset_1(X38,k1_zfmisc_1(X37))
      | k3_subset_1(X37,X38) = k4_xboole_0(X37,X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

cnf(c_0_75,plain,
    ( r1_tarski(X1,k3_tarski(k2_enumset1(X1,X1,X1,X2))) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_76,plain,
    ( k2_enumset1(X1,X1,X1,X2) = k2_enumset1(X2,X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_42]),c_0_42]),c_0_56]),c_0_56])).

cnf(c_0_77,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_78,plain,
    ( r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))
    | ~ r1_tarski(k1_zfmisc_1(X2),k1_zfmisc_1(X3))
    | ~ r1_tarski(X1,k3_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_79,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(k1_zfmisc_1(X2),k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_71,c_0_70])).

cnf(c_0_80,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

fof(c_0_81,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ( r1_tarski(k3_subset_1(X1,X2),X2)
        <=> X2 = k2_subset_1(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t39_subset_1])).

fof(c_0_82,plain,(
    ! [X40,X41] : m1_subset_1(k6_subset_1(X40,X41),k1_zfmisc_1(X40)) ),
    inference(variable_rename,[status(thm)],[dt_k6_subset_1])).

fof(c_0_83,plain,(
    ! [X44,X45] : k6_subset_1(X44,X45) = k4_xboole_0(X44,X45) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

cnf(c_0_84,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_85,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_86,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_87,plain,
    ( r1_tarski(X1,k3_tarski(k2_enumset1(X2,X2,X2,X1))) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_88,plain,
    ( k3_tarski(k2_enumset1(X1,X1,X1,k3_xboole_0(X1,X2))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_77,c_0_55]),c_0_56])).

cnf(c_0_89,plain,
    ( r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(k1_zfmisc_1(X2),k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_90,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_80])).

fof(c_0_91,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0))
    & ( ~ r1_tarski(k3_subset_1(esk1_0,esk2_0),esk2_0)
      | esk2_0 != k2_subset_1(esk1_0) )
    & ( r1_tarski(k3_subset_1(esk1_0,esk2_0),esk2_0)
      | esk2_0 = k2_subset_1(esk1_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_81])])])).

cnf(c_0_92,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_93,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_94,plain,(
    ! [X6] : k3_xboole_0(X6,X6) = X6 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

cnf(c_0_95,plain,
    ( m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_96,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_97,plain,
    ( k3_tarski(k2_enumset1(X1,X1,X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_84,c_0_55]),c_0_53]),c_0_56])).

cnf(c_0_98,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k3_xboole_0(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_85,c_0_53])).

cnf(c_0_99,plain,
    ( k3_xboole_0(X1,X2) = X3
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))
    | ~ r1_tarski(k3_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_86,c_0_79])).

cnf(c_0_100,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_101,plain,
    ( r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_102,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_91])).

cnf(c_0_103,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_92,c_0_53])).

cnf(c_0_104,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_93])).

cnf(c_0_105,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_94])).

cnf(c_0_106,plain,
    ( m1_subset_1(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_95,c_0_96]),c_0_53])).

cnf(c_0_107,plain,
    ( k3_tarski(k2_enumset1(X1,X1,X1,X2)) = k5_xboole_0(X1,k3_subset_1(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_97,c_0_98])).

cnf(c_0_108,plain,
    ( k3_tarski(k2_enumset1(X1,X1,X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_97,c_0_76])).

cnf(c_0_109,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_100]),c_0_63])])).

cnf(c_0_110,negated_conjecture,
    ( r1_tarski(k1_zfmisc_1(esk2_0),k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_101,c_0_102])).

cnf(c_0_111,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X2,X1)) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_103,c_0_104])).

cnf(c_0_112,plain,
    ( k3_tarski(k2_enumset1(X1,X1,X1,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_88,c_0_105])).

cnf(c_0_113,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(esk1_0,esk2_0),esk2_0)
    | esk2_0 != k2_subset_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_91])).

cnf(c_0_114,plain,
    ( k3_subset_1(X1,X2) = k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_103,c_0_98])).

cnf(c_0_115,negated_conjecture,
    ( r1_tarski(esk2_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_71,c_0_102])).

cnf(c_0_116,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_71,c_0_106])).

cnf(c_0_117,plain,
    ( k3_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_60,c_0_104])).

cnf(c_0_118,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k5_xboole_0(X2,k3_subset_1(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_107,c_0_108])).

cnf(c_0_119,negated_conjecture,
    ( k3_xboole_0(esk2_0,esk1_0) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_109,c_0_110])).

cnf(c_0_120,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_105]),c_0_90])])).

cnf(c_0_121,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_111]),c_0_112]),c_0_90])])).

cnf(c_0_122,negated_conjecture,
    ( esk2_0 != esk1_0
    | ~ r1_tarski(k3_subset_1(esk1_0,esk2_0),esk2_0) ),
    inference(rw,[status(thm)],[c_0_113,c_0_34])).

cnf(c_0_123,negated_conjecture,
    ( k3_subset_1(esk1_0,esk2_0) = k1_xboole_0
    | ~ r1_tarski(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_114,c_0_102])).

cnf(c_0_124,negated_conjecture,
    ( esk1_0 = esk2_0
    | ~ r1_tarski(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_86,c_0_115])).

cnf(c_0_125,negated_conjecture,
    ( r1_tarski(k3_subset_1(esk1_0,esk2_0),esk2_0)
    | esk2_0 = k2_subset_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_91])).

cnf(c_0_126,plain,
    ( r1_tarski(k5_xboole_0(X1,X2),X1)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_116,c_0_117])).

cnf(c_0_127,negated_conjecture,
    ( k5_xboole_0(esk2_0,k3_subset_1(esk1_0,esk2_0)) = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118,c_0_119]),c_0_120]),c_0_121]),c_0_102])])).

cnf(c_0_128,negated_conjecture,
    ( ~ r1_tarski(esk1_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122,c_0_123]),c_0_64])]),c_0_124])).

cnf(c_0_129,negated_conjecture,
    ( esk2_0 = esk1_0
    | r1_tarski(k3_subset_1(esk1_0,esk2_0),esk2_0) ),
    inference(rw,[status(thm)],[c_0_125,c_0_34])).

cnf(c_0_130,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(esk1_0,esk2_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_126,c_0_127]),c_0_128])).

cnf(c_0_131,negated_conjecture,
    ( esk1_0 = esk2_0 ),
    inference(sr,[status(thm)],[c_0_129,c_0_130])).

cnf(c_0_132,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_130,c_0_131]),c_0_62]),c_0_64])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:28:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 3.50/3.77  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 3.50/3.77  # and selection function PSelectComplexExceptUniqMaxHorn.
% 3.50/3.77  #
% 3.50/3.77  # Preprocessing time       : 0.027 s
% 3.50/3.77  # Presaturation interreduction done
% 3.50/3.77  
% 3.50/3.77  # Proof found!
% 3.50/3.77  # SZS status Theorem
% 3.50/3.77  # SZS output start CNFRefutation
% 3.50/3.77  fof(t22_subset_1, axiom, ![X1]:k2_subset_1(X1)=k3_subset_1(X1,k1_subset_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_subset_1)).
% 3.50/3.77  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 3.50/3.77  fof(d3_subset_1, axiom, ![X1]:k1_subset_1(X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 3.50/3.77  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.50/3.77  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.50/3.77  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 3.50/3.77  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.50/3.77  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.50/3.77  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.50/3.77  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.50/3.77  fof(t46_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 3.50/3.77  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 3.50/3.77  fof(t83_zfmisc_1, axiom, ![X1, X2]:k1_zfmisc_1(k3_xboole_0(X1,X2))=k3_xboole_0(k1_zfmisc_1(X1),k1_zfmisc_1(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_zfmisc_1)).
% 3.50/3.77  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.50/3.77  fof(t31_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_tarski(X2,X3)<=>r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_subset_1)).
% 3.50/3.77  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.50/3.77  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.50/3.77  fof(t79_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 3.50/3.77  fof(t22_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 3.50/3.77  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.50/3.77  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.50/3.77  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 3.50/3.77  fof(t39_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(r1_tarski(k3_subset_1(X1,X2),X2)<=>X2=k2_subset_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_subset_1)).
% 3.50/3.77  fof(dt_k6_subset_1, axiom, ![X1, X2]:m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 3.50/3.77  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 3.50/3.77  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.50/3.77  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.50/3.77  fof(c_0_27, plain, ![X46]:k2_subset_1(X46)=k3_subset_1(X46,k1_subset_1(X46)), inference(variable_rename,[status(thm)],[t22_subset_1])).
% 3.50/3.77  fof(c_0_28, plain, ![X36]:k2_subset_1(X36)=X36, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 3.50/3.77  fof(c_0_29, plain, ![X35]:k1_subset_1(X35)=k1_xboole_0, inference(variable_rename,[status(thm)],[d3_subset_1])).
% 3.50/3.77  fof(c_0_30, plain, ![X29, X30]:k3_tarski(k2_tarski(X29,X30))=k2_xboole_0(X29,X30), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 3.50/3.77  fof(c_0_31, plain, ![X24, X25]:k1_enumset1(X24,X24,X25)=k2_tarski(X24,X25), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 3.50/3.77  fof(c_0_32, plain, ![X42, X43]:(~m1_subset_1(X43,k1_zfmisc_1(X42))|k3_subset_1(X42,k3_subset_1(X42,X43))=X43), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 3.50/3.77  cnf(c_0_33, plain, (k2_subset_1(X1)=k3_subset_1(X1,k1_subset_1(X1))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 3.50/3.77  cnf(c_0_34, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_28])).
% 3.50/3.77  cnf(c_0_35, plain, (k1_subset_1(X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_29])).
% 3.50/3.77  fof(c_0_36, plain, ![X50]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X50)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 3.50/3.77  fof(c_0_37, plain, ![X39]:m1_subset_1(k2_subset_1(X39),k1_zfmisc_1(X39)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 3.50/3.77  fof(c_0_38, plain, ![X9, X10]:((k4_xboole_0(X9,X10)!=k1_xboole_0|r1_tarski(X9,X10))&(~r1_tarski(X9,X10)|k4_xboole_0(X9,X10)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 3.50/3.77  fof(c_0_39, plain, ![X11, X12]:k4_xboole_0(X11,X12)=k5_xboole_0(X11,k3_xboole_0(X11,X12)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 3.50/3.77  fof(c_0_40, plain, ![X18, X19]:k4_xboole_0(X18,k2_xboole_0(X18,X19))=k1_xboole_0, inference(variable_rename,[status(thm)],[t46_xboole_1])).
% 3.50/3.77  cnf(c_0_41, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 3.50/3.77  cnf(c_0_42, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 3.50/3.77  fof(c_0_43, plain, ![X26, X27, X28]:k2_enumset1(X26,X26,X27,X28)=k1_enumset1(X26,X27,X28), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 3.50/3.77  fof(c_0_44, plain, ![X33, X34]:k1_zfmisc_1(k3_xboole_0(X33,X34))=k3_xboole_0(k1_zfmisc_1(X33),k1_zfmisc_1(X34)), inference(variable_rename,[status(thm)],[t83_zfmisc_1])).
% 3.50/3.77  fof(c_0_45, plain, ![X15, X16]:(~r1_tarski(X15,X16)|k3_xboole_0(X15,X16)=X15), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 3.50/3.77  fof(c_0_46, plain, ![X47, X48, X49]:((~r1_tarski(X48,X49)|r1_tarski(k3_subset_1(X47,X49),k3_subset_1(X47,X48))|~m1_subset_1(X49,k1_zfmisc_1(X47))|~m1_subset_1(X48,k1_zfmisc_1(X47)))&(~r1_tarski(k3_subset_1(X47,X49),k3_subset_1(X47,X48))|r1_tarski(X48,X49)|~m1_subset_1(X49,k1_zfmisc_1(X47))|~m1_subset_1(X48,k1_zfmisc_1(X47)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_subset_1])])])])).
% 3.50/3.77  cnf(c_0_47, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 3.50/3.77  cnf(c_0_48, plain, (X1=k3_subset_1(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_34]), c_0_35])).
% 3.50/3.77  cnf(c_0_49, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 3.50/3.77  cnf(c_0_50, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 3.50/3.77  fof(c_0_51, plain, ![X17]:r1_tarski(k1_xboole_0,X17), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 3.50/3.77  cnf(c_0_52, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_38])).
% 3.50/3.77  cnf(c_0_53, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 3.50/3.77  cnf(c_0_54, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_40])).
% 3.50/3.77  cnf(c_0_55, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_41, c_0_42])).
% 3.50/3.77  cnf(c_0_56, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 3.50/3.77  fof(c_0_57, plain, ![X22, X23]:k2_tarski(X22,X23)=k2_tarski(X23,X22), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 3.50/3.77  fof(c_0_58, plain, ![X31, X32]:(~r1_tarski(X31,X32)|r1_tarski(k1_zfmisc_1(X31),k1_zfmisc_1(X32))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_zfmisc_1])])).
% 3.50/3.77  cnf(c_0_59, plain, (k1_zfmisc_1(k3_xboole_0(X1,X2))=k3_xboole_0(k1_zfmisc_1(X1),k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 3.50/3.77  cnf(c_0_60, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 3.50/3.77  cnf(c_0_61, plain, (r1_tarski(X3,X2)|~r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X3))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 3.50/3.77  cnf(c_0_62, plain, (k3_subset_1(X1,X1)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49])])).
% 3.50/3.77  cnf(c_0_63, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_50, c_0_34])).
% 3.50/3.77  cnf(c_0_64, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 3.50/3.77  cnf(c_0_65, plain, (r1_tarski(X1,X2)|k5_xboole_0(X1,k3_xboole_0(X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_52, c_0_53])).
% 3.50/3.77  cnf(c_0_66, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k3_tarski(k2_enumset1(X1,X1,X1,X2))))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_55]), c_0_53]), c_0_56])).
% 3.50/3.77  cnf(c_0_67, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 3.50/3.77  fof(c_0_68, plain, ![X13, X14]:k2_xboole_0(X13,k3_xboole_0(X13,X14))=X13, inference(variable_rename,[status(thm)],[t22_xboole_1])).
% 3.50/3.77  cnf(c_0_69, plain, (r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 3.50/3.77  cnf(c_0_70, plain, (k1_zfmisc_1(k3_xboole_0(X1,X2))=k1_zfmisc_1(X1)|~r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 3.50/3.77  cnf(c_0_71, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_63]), c_0_64])])).
% 3.50/3.77  fof(c_0_72, plain, ![X7, X8]:(((r1_tarski(X7,X8)|X7!=X8)&(r1_tarski(X8,X7)|X7!=X8))&(~r1_tarski(X7,X8)|~r1_tarski(X8,X7)|X7=X8)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 3.50/3.77  fof(c_0_73, plain, ![X20, X21]:k2_xboole_0(X20,X21)=k5_xboole_0(X20,k4_xboole_0(X21,X20)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 3.50/3.77  fof(c_0_74, plain, ![X37, X38]:(~m1_subset_1(X38,k1_zfmisc_1(X37))|k3_subset_1(X37,X38)=k4_xboole_0(X37,X38)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 3.50/3.77  cnf(c_0_75, plain, (r1_tarski(X1,k3_tarski(k2_enumset1(X1,X1,X1,X2)))), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 3.50/3.77  cnf(c_0_76, plain, (k2_enumset1(X1,X1,X1,X2)=k2_enumset1(X2,X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67, c_0_42]), c_0_42]), c_0_56]), c_0_56])).
% 3.50/3.77  cnf(c_0_77, plain, (k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_68])).
% 3.50/3.77  cnf(c_0_78, plain, (r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))|~r1_tarski(k1_zfmisc_1(X2),k1_zfmisc_1(X3))|~r1_tarski(X1,k3_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 3.50/3.77  cnf(c_0_79, plain, (r1_tarski(X1,k3_xboole_0(X2,X3))|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(k1_zfmisc_1(X2),k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_71, c_0_70])).
% 3.50/3.77  cnf(c_0_80, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_72])).
% 3.50/3.77  fof(c_0_81, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(r1_tarski(k3_subset_1(X1,X2),X2)<=>X2=k2_subset_1(X1)))), inference(assume_negation,[status(cth)],[t39_subset_1])).
% 3.50/3.77  fof(c_0_82, plain, ![X40, X41]:m1_subset_1(k6_subset_1(X40,X41),k1_zfmisc_1(X40)), inference(variable_rename,[status(thm)],[dt_k6_subset_1])).
% 3.50/3.77  fof(c_0_83, plain, ![X44, X45]:k6_subset_1(X44,X45)=k4_xboole_0(X44,X45), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 3.50/3.77  cnf(c_0_84, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_73])).
% 3.50/3.77  cnf(c_0_85, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_74])).
% 3.50/3.77  cnf(c_0_86, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 3.50/3.77  cnf(c_0_87, plain, (r1_tarski(X1,k3_tarski(k2_enumset1(X2,X2,X2,X1)))), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 3.50/3.77  cnf(c_0_88, plain, (k3_tarski(k2_enumset1(X1,X1,X1,k3_xboole_0(X1,X2)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_77, c_0_55]), c_0_56])).
% 3.50/3.77  cnf(c_0_89, plain, (r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(k1_zfmisc_1(X2),k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 3.50/3.77  cnf(c_0_90, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_80])).
% 3.50/3.77  fof(c_0_91, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0))&((~r1_tarski(k3_subset_1(esk1_0,esk2_0),esk2_0)|esk2_0!=k2_subset_1(esk1_0))&(r1_tarski(k3_subset_1(esk1_0,esk2_0),esk2_0)|esk2_0=k2_subset_1(esk1_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_81])])])).
% 3.50/3.77  cnf(c_0_92, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 3.50/3.77  fof(c_0_93, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 3.50/3.77  fof(c_0_94, plain, ![X6]:k3_xboole_0(X6,X6)=X6, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 3.50/3.77  cnf(c_0_95, plain, (m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_82])).
% 3.50/3.77  cnf(c_0_96, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_83])).
% 3.50/3.77  cnf(c_0_97, plain, (k3_tarski(k2_enumset1(X1,X1,X1,X2))=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_84, c_0_55]), c_0_53]), c_0_56])).
% 3.50/3.77  cnf(c_0_98, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k3_xboole_0(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_85, c_0_53])).
% 3.50/3.77  cnf(c_0_99, plain, (k3_xboole_0(X1,X2)=X3|~m1_subset_1(X3,k1_zfmisc_1(X1))|~r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))|~r1_tarski(k3_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_86, c_0_79])).
% 3.50/3.77  cnf(c_0_100, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_87, c_0_88])).
% 3.50/3.77  cnf(c_0_101, plain, (r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_89, c_0_90])).
% 3.50/3.77  cnf(c_0_102, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_91])).
% 3.50/3.77  cnf(c_0_103, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=k1_xboole_0|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_92, c_0_53])).
% 3.50/3.77  cnf(c_0_104, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_93])).
% 3.50/3.77  cnf(c_0_105, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_94])).
% 3.50/3.77  cnf(c_0_106, plain, (m1_subset_1(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k1_zfmisc_1(X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_95, c_0_96]), c_0_53])).
% 3.50/3.77  cnf(c_0_107, plain, (k3_tarski(k2_enumset1(X1,X1,X1,X2))=k5_xboole_0(X1,k3_subset_1(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_97, c_0_98])).
% 3.50/3.77  cnf(c_0_108, plain, (k3_tarski(k2_enumset1(X1,X1,X1,X2))=k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_97, c_0_76])).
% 3.50/3.77  cnf(c_0_109, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_100]), c_0_63])])).
% 3.50/3.77  cnf(c_0_110, negated_conjecture, (r1_tarski(k1_zfmisc_1(esk2_0),k1_zfmisc_1(esk1_0))), inference(spm,[status(thm)],[c_0_101, c_0_102])).
% 3.50/3.77  cnf(c_0_111, plain, (k5_xboole_0(X1,k3_xboole_0(X2,X1))=k1_xboole_0|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_103, c_0_104])).
% 3.50/3.77  cnf(c_0_112, plain, (k3_tarski(k2_enumset1(X1,X1,X1,X1))=X1), inference(spm,[status(thm)],[c_0_88, c_0_105])).
% 3.50/3.77  cnf(c_0_113, negated_conjecture, (~r1_tarski(k3_subset_1(esk1_0,esk2_0),esk2_0)|esk2_0!=k2_subset_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_91])).
% 3.50/3.77  cnf(c_0_114, plain, (k3_subset_1(X1,X2)=k1_xboole_0|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_103, c_0_98])).
% 3.50/3.77  cnf(c_0_115, negated_conjecture, (r1_tarski(esk2_0,esk1_0)), inference(spm,[status(thm)],[c_0_71, c_0_102])).
% 3.50/3.77  cnf(c_0_116, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1)), inference(spm,[status(thm)],[c_0_71, c_0_106])).
% 3.50/3.77  cnf(c_0_117, plain, (k3_xboole_0(X1,X2)=X2|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_60, c_0_104])).
% 3.50/3.77  cnf(c_0_118, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))=k5_xboole_0(X2,k3_subset_1(X1,X2))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_107, c_0_108])).
% 3.50/3.77  cnf(c_0_119, negated_conjecture, (k3_xboole_0(esk2_0,esk1_0)=esk2_0), inference(spm,[status(thm)],[c_0_109, c_0_110])).
% 3.50/3.77  cnf(c_0_120, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_105]), c_0_90])])).
% 3.50/3.77  cnf(c_0_121, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_111]), c_0_112]), c_0_90])])).
% 3.50/3.77  cnf(c_0_122, negated_conjecture, (esk2_0!=esk1_0|~r1_tarski(k3_subset_1(esk1_0,esk2_0),esk2_0)), inference(rw,[status(thm)],[c_0_113, c_0_34])).
% 3.50/3.77  cnf(c_0_123, negated_conjecture, (k3_subset_1(esk1_0,esk2_0)=k1_xboole_0|~r1_tarski(esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_114, c_0_102])).
% 3.50/3.77  cnf(c_0_124, negated_conjecture, (esk1_0=esk2_0|~r1_tarski(esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_86, c_0_115])).
% 3.50/3.77  cnf(c_0_125, negated_conjecture, (r1_tarski(k3_subset_1(esk1_0,esk2_0),esk2_0)|esk2_0=k2_subset_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_91])).
% 3.50/3.77  cnf(c_0_126, plain, (r1_tarski(k5_xboole_0(X1,X2),X1)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_116, c_0_117])).
% 3.50/3.77  cnf(c_0_127, negated_conjecture, (k5_xboole_0(esk2_0,k3_subset_1(esk1_0,esk2_0))=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118, c_0_119]), c_0_120]), c_0_121]), c_0_102])])).
% 3.50/3.77  cnf(c_0_128, negated_conjecture, (~r1_tarski(esk1_0,esk2_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122, c_0_123]), c_0_64])]), c_0_124])).
% 3.50/3.77  cnf(c_0_129, negated_conjecture, (esk2_0=esk1_0|r1_tarski(k3_subset_1(esk1_0,esk2_0),esk2_0)), inference(rw,[status(thm)],[c_0_125, c_0_34])).
% 3.50/3.77  cnf(c_0_130, negated_conjecture, (~r1_tarski(k3_subset_1(esk1_0,esk2_0),esk2_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_126, c_0_127]), c_0_128])).
% 3.50/3.77  cnf(c_0_131, negated_conjecture, (esk1_0=esk2_0), inference(sr,[status(thm)],[c_0_129, c_0_130])).
% 3.50/3.77  cnf(c_0_132, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_130, c_0_131]), c_0_62]), c_0_64])]), ['proof']).
% 3.50/3.77  # SZS output end CNFRefutation
% 3.50/3.77  # Proof object total steps             : 133
% 3.50/3.77  # Proof object clause steps            : 78
% 3.50/3.77  # Proof object formula steps           : 55
% 3.50/3.77  # Proof object conjectures             : 18
% 3.50/3.77  # Proof object clause conjectures      : 15
% 3.50/3.77  # Proof object formula conjectures     : 3
% 3.50/3.77  # Proof object initial clauses used    : 31
% 3.50/3.77  # Proof object initial formulas used   : 27
% 3.50/3.77  # Proof object generating inferences   : 31
% 3.50/3.77  # Proof object simplifying inferences  : 49
% 3.50/3.77  # Training examples: 0 positive, 0 negative
% 3.50/3.77  # Parsed axioms                        : 27
% 3.50/3.77  # Removed by relevancy pruning/SinE    : 0
% 3.50/3.77  # Initial clauses                      : 33
% 3.50/3.77  # Removed in clause preprocessing      : 7
% 3.50/3.77  # Initial clauses in saturation        : 26
% 3.50/3.77  # Processed clauses                    : 23805
% 3.50/3.77  # ...of these trivial                  : 104
% 3.50/3.77  # ...subsumed                          : 20426
% 3.50/3.77  # ...remaining for further processing  : 3275
% 3.50/3.77  # Other redundant clauses eliminated   : 285
% 3.50/3.77  # Clauses deleted for lack of memory   : 0
% 3.50/3.77  # Backward-subsumed                    : 754
% 3.50/3.77  # Backward-rewritten                   : 1467
% 3.50/3.77  # Generated clauses                    : 336737
% 3.50/3.77  # ...of the previous two non-trivial   : 309816
% 3.50/3.77  # Contextual simplify-reflections      : 377
% 3.50/3.77  # Paramodulations                      : 336451
% 3.50/3.77  # Factorizations                       : 0
% 3.50/3.77  # Equation resolutions                 : 285
% 3.50/3.77  # Propositional unsat checks           : 0
% 3.50/3.77  #    Propositional check models        : 0
% 3.50/3.77  #    Propositional check unsatisfiable : 0
% 3.50/3.77  #    Propositional clauses             : 0
% 3.50/3.77  #    Propositional clauses after purity: 0
% 3.50/3.77  #    Propositional unsat core size     : 0
% 3.50/3.77  #    Propositional preprocessing time  : 0.000
% 3.50/3.77  #    Propositional encoding time       : 0.000
% 3.50/3.77  #    Propositional solver time         : 0.000
% 3.50/3.77  #    Success case prop preproc time    : 0.000
% 3.50/3.77  #    Success case prop encoding time   : 0.000
% 3.50/3.77  #    Success case prop solver time     : 0.000
% 3.50/3.77  # Current number of processed clauses  : 1026
% 3.50/3.77  #    Positive orientable unit clauses  : 66
% 3.50/3.77  #    Positive unorientable unit clauses: 13
% 3.50/3.77  #    Negative unit clauses             : 5
% 3.50/3.77  #    Non-unit-clauses                  : 942
% 3.50/3.77  # Current number of unprocessed clauses: 284638
% 3.50/3.77  # ...number of literals in the above   : 1409491
% 3.50/3.77  # Current number of archived formulas  : 0
% 3.50/3.77  # Current number of archived clauses   : 2254
% 3.50/3.77  # Clause-clause subsumption calls (NU) : 1775831
% 3.50/3.77  # Rec. Clause-clause subsumption calls : 236405
% 3.50/3.77  # Non-unit clause-clause subsumptions  : 15529
% 3.50/3.77  # Unit Clause-clause subsumption calls : 29121
% 3.50/3.77  # Rewrite failures with RHS unbound    : 0
% 3.50/3.77  # BW rewrite match attempts            : 542
% 3.50/3.77  # BW rewrite match successes           : 135
% 3.50/3.77  # Condensation attempts                : 0
% 3.50/3.77  # Condensation successes               : 0
% 3.50/3.77  # Termbank termtop insertions          : 6441340
% 3.50/3.79  
% 3.50/3.79  # -------------------------------------------------
% 3.50/3.79  # User time                : 3.271 s
% 3.50/3.79  # System time              : 0.119 s
% 3.50/3.79  # Total time               : 3.390 s
% 3.50/3.79  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
