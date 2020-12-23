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
% DateTime   : Thu Dec  3 10:47:45 EST 2020

% Result     : Theorem 0.68s
% Output     : CNFRefutation 0.68s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 950 expanded)
%              Number of clauses        :   74 ( 358 expanded)
%              Number of leaves         :   29 ( 294 expanded)
%              Depth                    :   12
%              Number of atoms          :  334 (1337 expanded)
%              Number of equality atoms :  160 ( 937 expanded)
%              Maximal formula depth    :   47 (   4 average)
%              Maximal clause size      :   68 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t55_setfam_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( X2 = k1_tarski(X1)
       => k7_setfam_1(X1,X2) = k1_tarski(k1_xboole_0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_setfam_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t39_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,k1_tarski(X2))
    <=> ( X1 = k1_xboole_0
        | X1 = k1_tarski(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(t20_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
    <=> X1 != X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(t11_setfam_1,axiom,(
    ! [X1] : k1_setfam_1(k1_tarski(X1)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

fof(l1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(dt_k7_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => m1_subset_1(k7_setfam_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_setfam_1)).

fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(t63_subset_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

fof(dt_k1_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_subset_1)).

fof(d3_subset_1,axiom,(
    ! [X1] : k1_subset_1(X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

fof(t49_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( r2_hidden(k3_subset_1(X1,X3),k7_setfam_1(X1,X2))
          <=> r2_hidden(X3,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_setfam_1)).

fof(involutiveness_k7_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => k7_setfam_1(X1,k7_setfam_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

fof(t22_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = k3_subset_1(X1,k1_subset_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(t1_zfmisc_1,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).

fof(d6_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( X9 = k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)
    <=> ! [X10] :
          ( r2_hidden(X10,X9)
        <=> ~ ( X10 != X1
              & X10 != X2
              & X10 != X3
              & X10 != X4
              & X10 != X5
              & X10 != X6
              & X10 != X7
              & X10 != X8 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_enumset1)).

fof(t51_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
         => ( r1_tarski(k7_setfam_1(X1,X2),k7_setfam_1(X1,X3))
           => r1_tarski(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_setfam_1)).

fof(t46_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ~ ( X2 != k1_xboole_0
          & k7_setfam_1(X1,X2) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_setfam_1)).

fof(c_0_29,plain,(
    ! [X83,X84] : k1_setfam_1(k2_tarski(X83,X84)) = k3_xboole_0(X83,X84) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_30,plain,(
    ! [X15,X16] : k1_enumset1(X15,X15,X16) = k2_tarski(X15,X16) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_31,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
       => ( X2 = k1_tarski(X1)
         => k7_setfam_1(X1,X2) = k1_tarski(k1_xboole_0) ) ) ),
    inference(assume_negation,[status(cth)],[t55_setfam_1])).

fof(c_0_32,plain,(
    ! [X11,X12] : k4_xboole_0(X11,X12) = k5_xboole_0(X11,k3_xboole_0(X11,X12)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_33,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_34,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_35,plain,(
    ! [X46,X47] :
      ( ( ~ r1_tarski(X46,k1_tarski(X47))
        | X46 = k1_xboole_0
        | X46 = k1_tarski(X47) )
      & ( X46 != k1_xboole_0
        | r1_tarski(X46,k1_tarski(X47)) )
      & ( X46 != k1_tarski(X47)
        | r1_tarski(X46,k1_tarski(X47)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t39_zfmisc_1])])])).

fof(c_0_36,plain,(
    ! [X14] : k2_tarski(X14,X14) = k1_tarski(X14) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_37,plain,(
    ! [X17,X18,X19] : k2_enumset1(X17,X17,X18,X19) = k1_enumset1(X17,X18,X19) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_38,plain,(
    ! [X20,X21,X22,X23] : k3_enumset1(X20,X20,X21,X22,X23) = k2_enumset1(X20,X21,X22,X23) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_39,plain,(
    ! [X24,X25,X26,X27,X28] : k4_enumset1(X24,X24,X25,X26,X27,X28) = k3_enumset1(X24,X25,X26,X27,X28) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_40,plain,(
    ! [X29,X30,X31,X32,X33,X34] : k5_enumset1(X29,X29,X30,X31,X32,X33,X34) = k4_enumset1(X29,X30,X31,X32,X33,X34) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_41,plain,(
    ! [X35,X36,X37,X38,X39,X40,X41] : k6_enumset1(X35,X35,X36,X37,X38,X39,X40,X41) = k5_enumset1(X35,X36,X37,X38,X39,X40,X41) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_42,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))
    & esk3_0 = k1_tarski(esk2_0)
    & k7_setfam_1(esk2_0,esk3_0) != k1_tarski(k1_xboole_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_31])])])).

fof(c_0_43,plain,(
    ! [X44,X45] :
      ( ( k4_xboole_0(k1_tarski(X44),k1_tarski(X45)) != k1_tarski(X44)
        | X44 != X45 )
      & ( X44 = X45
        | k4_xboole_0(k1_tarski(X44),k1_tarski(X45)) = k1_tarski(X44) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_zfmisc_1])])).

cnf(c_0_44,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_45,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_33,c_0_34])).

fof(c_0_46,plain,(
    ! [X82] : k1_setfam_1(k1_tarski(X82)) = X82 ),
    inference(variable_rename,[status(thm)],[t11_setfam_1])).

cnf(c_0_47,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_tarski(X2)
    | ~ r1_tarski(X1,k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_48,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_49,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_50,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_51,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_52,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_53,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_54,negated_conjecture,
    ( esk3_0 = k1_tarski(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

fof(c_0_55,plain,(
    ! [X42,X43] :
      ( ( ~ r1_tarski(k1_tarski(X42),X43)
        | r2_hidden(X42,X43) )
      & ( ~ r2_hidden(X42,X43)
        | r1_tarski(k1_tarski(X42),X43) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).

cnf(c_0_56,plain,
    ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) != k1_tarski(X1)
    | X1 != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_57,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_58,plain,
    ( k1_setfam_1(k1_tarski(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

fof(c_0_59,plain,(
    ! [X13] : k5_xboole_0(X13,X13) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

fof(c_0_60,plain,(
    ! [X48,X49] :
      ( ( ~ m1_subset_1(X49,X48)
        | r2_hidden(X49,X48)
        | v1_xboole_0(X48) )
      & ( ~ r2_hidden(X49,X48)
        | m1_subset_1(X49,X48)
        | v1_xboole_0(X48) )
      & ( ~ m1_subset_1(X49,X48)
        | v1_xboole_0(X49)
        | ~ v1_xboole_0(X48) )
      & ( ~ v1_xboole_0(X49)
        | m1_subset_1(X49,X48)
        | ~ v1_xboole_0(X48) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_61,plain,(
    ! [X78,X79] :
      ( ~ m1_subset_1(X79,k1_zfmisc_1(k1_zfmisc_1(X78)))
      | m1_subset_1(k7_setfam_1(X78,X79),k1_zfmisc_1(k1_zfmisc_1(X78))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_setfam_1])])).

fof(c_0_62,plain,(
    ! [X74] : ~ v1_xboole_0(k1_zfmisc_1(X74)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

fof(c_0_63,plain,(
    ! [X76,X77] :
      ( ~ r2_hidden(X76,X77)
      | m1_subset_1(k1_tarski(X76),k1_zfmisc_1(X77)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_subset_1])])).

fof(c_0_64,plain,(
    ! [X73] : m1_subset_1(k1_subset_1(X73),k1_zfmisc_1(X73)) ),
    inference(variable_rename,[status(thm)],[dt_k1_subset_1])).

fof(c_0_65,plain,(
    ! [X50] : k1_subset_1(X50) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[d3_subset_1])).

cnf(c_0_66,plain,
    ( X1 = k1_xboole_0
    | X1 = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)
    | ~ r1_tarski(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_48]),c_0_48]),c_0_34]),c_0_34]),c_0_49]),c_0_49]),c_0_50]),c_0_50]),c_0_51]),c_0_51]),c_0_52]),c_0_52]),c_0_53]),c_0_53])).

cnf(c_0_67,negated_conjecture,
    ( esk3_0 = k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_48]),c_0_34]),c_0_49]),c_0_50]),c_0_51]),c_0_52]),c_0_53])).

cnf(c_0_68,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_69,plain,
    ( X1 != X2
    | k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)))) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_48]),c_0_48]),c_0_48]),c_0_34]),c_0_34]),c_0_34]),c_0_57]),c_0_49]),c_0_49]),c_0_49]),c_0_49]),c_0_49]),c_0_49]),c_0_50]),c_0_50]),c_0_50]),c_0_50]),c_0_50]),c_0_50]),c_0_50]),c_0_51]),c_0_51]),c_0_51]),c_0_51]),c_0_51]),c_0_51]),c_0_51]),c_0_51]),c_0_52]),c_0_52]),c_0_52]),c_0_52]),c_0_52]),c_0_52]),c_0_52]),c_0_52]),c_0_52]),c_0_53]),c_0_53]),c_0_53]),c_0_53]),c_0_53]),c_0_53]),c_0_53]),c_0_53]),c_0_53]),c_0_53])).

cnf(c_0_70,plain,
    ( k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_48]),c_0_34]),c_0_49]),c_0_50]),c_0_51]),c_0_52]),c_0_53])).

cnf(c_0_71,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

fof(c_0_72,plain,(
    ! [X87,X88,X89] :
      ( ( ~ r2_hidden(k3_subset_1(X87,X89),k7_setfam_1(X87,X88))
        | r2_hidden(X89,X88)
        | ~ m1_subset_1(X89,k1_zfmisc_1(X87))
        | ~ m1_subset_1(X88,k1_zfmisc_1(k1_zfmisc_1(X87))) )
      & ( ~ r2_hidden(X89,X88)
        | r2_hidden(k3_subset_1(X87,X89),k7_setfam_1(X87,X88))
        | ~ m1_subset_1(X89,k1_zfmisc_1(X87))
        | ~ m1_subset_1(X88,k1_zfmisc_1(k1_zfmisc_1(X87))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t49_setfam_1])])])])).

fof(c_0_73,plain,(
    ! [X80,X81] :
      ( ~ m1_subset_1(X81,k1_zfmisc_1(k1_zfmisc_1(X80)))
      | k7_setfam_1(X80,k7_setfam_1(X80,X81)) = X81 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k7_setfam_1])])).

fof(c_0_74,plain,(
    ! [X75] : k2_subset_1(X75) = k3_subset_1(X75,k1_subset_1(X75)) ),
    inference(variable_rename,[status(thm)],[t22_subset_1])).

fof(c_0_75,plain,(
    ! [X51] : k2_subset_1(X51) = X51 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

cnf(c_0_76,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_77,plain,
    ( m1_subset_1(k7_setfam_1(X2,X1),k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_78,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_79,plain,
    ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_80,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[t1_zfmisc_1])).

cnf(c_0_81,plain,
    ( m1_subset_1(k1_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_82,plain,
    ( k1_subset_1(X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_83,negated_conjecture,
    ( X1 = k1_xboole_0
    | X1 = esk3_0
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_84,plain,
    ( r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_48]),c_0_34]),c_0_49]),c_0_50]),c_0_51]),c_0_52]),c_0_53])).

cnf(c_0_85,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_69]),c_0_70]),c_0_71])).

cnf(c_0_86,plain,
    ( r2_hidden(k3_subset_1(X3,X1),k7_setfam_1(X3,X2))
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_87,plain,
    ( k7_setfam_1(X2,k7_setfam_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_88,plain,
    ( k2_subset_1(X1) = k3_subset_1(X1,k1_subset_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_89,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

fof(c_0_90,plain,(
    ! [X52,X53,X54,X55,X56,X57,X58,X59,X60,X61,X62,X63,X64,X65,X66,X67,X68,X69,X70,X71] :
      ( ( ~ r2_hidden(X61,X60)
        | X61 = X52
        | X61 = X53
        | X61 = X54
        | X61 = X55
        | X61 = X56
        | X61 = X57
        | X61 = X58
        | X61 = X59
        | X60 != k6_enumset1(X52,X53,X54,X55,X56,X57,X58,X59) )
      & ( X62 != X52
        | r2_hidden(X62,X60)
        | X60 != k6_enumset1(X52,X53,X54,X55,X56,X57,X58,X59) )
      & ( X62 != X53
        | r2_hidden(X62,X60)
        | X60 != k6_enumset1(X52,X53,X54,X55,X56,X57,X58,X59) )
      & ( X62 != X54
        | r2_hidden(X62,X60)
        | X60 != k6_enumset1(X52,X53,X54,X55,X56,X57,X58,X59) )
      & ( X62 != X55
        | r2_hidden(X62,X60)
        | X60 != k6_enumset1(X52,X53,X54,X55,X56,X57,X58,X59) )
      & ( X62 != X56
        | r2_hidden(X62,X60)
        | X60 != k6_enumset1(X52,X53,X54,X55,X56,X57,X58,X59) )
      & ( X62 != X57
        | r2_hidden(X62,X60)
        | X60 != k6_enumset1(X52,X53,X54,X55,X56,X57,X58,X59) )
      & ( X62 != X58
        | r2_hidden(X62,X60)
        | X60 != k6_enumset1(X52,X53,X54,X55,X56,X57,X58,X59) )
      & ( X62 != X59
        | r2_hidden(X62,X60)
        | X60 != k6_enumset1(X52,X53,X54,X55,X56,X57,X58,X59) )
      & ( esk1_9(X63,X64,X65,X66,X67,X68,X69,X70,X71) != X63
        | ~ r2_hidden(esk1_9(X63,X64,X65,X66,X67,X68,X69,X70,X71),X71)
        | X71 = k6_enumset1(X63,X64,X65,X66,X67,X68,X69,X70) )
      & ( esk1_9(X63,X64,X65,X66,X67,X68,X69,X70,X71) != X64
        | ~ r2_hidden(esk1_9(X63,X64,X65,X66,X67,X68,X69,X70,X71),X71)
        | X71 = k6_enumset1(X63,X64,X65,X66,X67,X68,X69,X70) )
      & ( esk1_9(X63,X64,X65,X66,X67,X68,X69,X70,X71) != X65
        | ~ r2_hidden(esk1_9(X63,X64,X65,X66,X67,X68,X69,X70,X71),X71)
        | X71 = k6_enumset1(X63,X64,X65,X66,X67,X68,X69,X70) )
      & ( esk1_9(X63,X64,X65,X66,X67,X68,X69,X70,X71) != X66
        | ~ r2_hidden(esk1_9(X63,X64,X65,X66,X67,X68,X69,X70,X71),X71)
        | X71 = k6_enumset1(X63,X64,X65,X66,X67,X68,X69,X70) )
      & ( esk1_9(X63,X64,X65,X66,X67,X68,X69,X70,X71) != X67
        | ~ r2_hidden(esk1_9(X63,X64,X65,X66,X67,X68,X69,X70,X71),X71)
        | X71 = k6_enumset1(X63,X64,X65,X66,X67,X68,X69,X70) )
      & ( esk1_9(X63,X64,X65,X66,X67,X68,X69,X70,X71) != X68
        | ~ r2_hidden(esk1_9(X63,X64,X65,X66,X67,X68,X69,X70,X71),X71)
        | X71 = k6_enumset1(X63,X64,X65,X66,X67,X68,X69,X70) )
      & ( esk1_9(X63,X64,X65,X66,X67,X68,X69,X70,X71) != X69
        | ~ r2_hidden(esk1_9(X63,X64,X65,X66,X67,X68,X69,X70,X71),X71)
        | X71 = k6_enumset1(X63,X64,X65,X66,X67,X68,X69,X70) )
      & ( esk1_9(X63,X64,X65,X66,X67,X68,X69,X70,X71) != X70
        | ~ r2_hidden(esk1_9(X63,X64,X65,X66,X67,X68,X69,X70,X71),X71)
        | X71 = k6_enumset1(X63,X64,X65,X66,X67,X68,X69,X70) )
      & ( r2_hidden(esk1_9(X63,X64,X65,X66,X67,X68,X69,X70,X71),X71)
        | esk1_9(X63,X64,X65,X66,X67,X68,X69,X70,X71) = X63
        | esk1_9(X63,X64,X65,X66,X67,X68,X69,X70,X71) = X64
        | esk1_9(X63,X64,X65,X66,X67,X68,X69,X70,X71) = X65
        | esk1_9(X63,X64,X65,X66,X67,X68,X69,X70,X71) = X66
        | esk1_9(X63,X64,X65,X66,X67,X68,X69,X70,X71) = X67
        | esk1_9(X63,X64,X65,X66,X67,X68,X69,X70,X71) = X68
        | esk1_9(X63,X64,X65,X66,X67,X68,X69,X70,X71) = X69
        | esk1_9(X63,X64,X65,X66,X67,X68,X69,X70,X71) = X70
        | X71 = k6_enumset1(X63,X64,X65,X66,X67,X68,X69,X70) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_enumset1])])])])])])).

cnf(c_0_91,plain,
    ( r2_hidden(k7_setfam_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_78])).

cnf(c_0_92,plain,
    ( m1_subset_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_48]),c_0_34]),c_0_49]),c_0_50]),c_0_51]),c_0_52]),c_0_53])).

cnf(c_0_93,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_48]),c_0_34]),c_0_49]),c_0_50]),c_0_51]),c_0_52]),c_0_53])).

cnf(c_0_94,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_95,negated_conjecture,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = esk3_0
    | ~ r2_hidden(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_85])).

cnf(c_0_96,plain,
    ( r2_hidden(k3_subset_1(X1,X2),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,k7_setfam_1(X1,X3)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_77])).

cnf(c_0_97,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_98,plain,
    ( X1 = k3_subset_1(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_88,c_0_89]),c_0_82])).

cnf(c_0_99,plain,
    ( r2_hidden(X2,X3)
    | ~ r2_hidden(k3_subset_1(X1,X2),k7_setfam_1(X1,X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_100,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k6_enumset1(X4,X5,X6,X7,X8,X9,X10,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_90])).

fof(c_0_101,plain,(
    ! [X90,X91,X92] :
      ( ~ m1_subset_1(X91,k1_zfmisc_1(k1_zfmisc_1(X90)))
      | ~ m1_subset_1(X92,k1_zfmisc_1(k1_zfmisc_1(X90)))
      | ~ r1_tarski(k7_setfam_1(X90,X91),k7_setfam_1(X90,X92))
      | r1_tarski(X91,X92) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t51_setfam_1])])])).

cnf(c_0_102,plain,
    ( r2_hidden(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_87]),c_0_77])).

cnf(c_0_103,plain,
    ( m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(X1))
    | ~ r2_hidden(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_92,c_0_93])).

cnf(c_0_104,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_94]),c_0_78])).

cnf(c_0_105,negated_conjecture,
    ( r1_tarski(esk3_0,X1)
    | ~ r2_hidden(X2,esk3_0)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_84,c_0_95])).

cnf(c_0_106,negated_conjecture,
    ( r2_hidden(k3_subset_1(esk2_0,X1),esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk2_0))
    | ~ r2_hidden(X1,k7_setfam_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_96,c_0_97])).

cnf(c_0_107,plain,
    ( r2_hidden(X1,k7_setfam_1(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ r2_hidden(k1_xboole_0,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_98]),c_0_94])])).

cnf(c_0_108,plain,
    ( r2_hidden(X1,k7_setfam_1(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(k3_subset_1(X2,X1),X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_87]),c_0_77])).

cnf(c_0_109,plain,
    ( r2_hidden(X1,k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_100])])).

cnf(c_0_110,plain,
    ( r1_tarski(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ r1_tarski(k7_setfam_1(X2,X1),k7_setfam_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_101])).

cnf(c_0_111,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_112,plain,
    ( r2_hidden(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_103]),c_0_104])])).

cnf(c_0_113,negated_conjecture,
    ( r1_tarski(esk3_0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk2_0))
    | ~ r2_hidden(X2,k7_setfam_1(esk2_0,esk3_0))
    | ~ r2_hidden(k3_subset_1(esk2_0,X2),X1) ),
    inference(spm,[status(thm)],[c_0_105,c_0_106])).

cnf(c_0_114,plain,
    ( r2_hidden(X1,k7_setfam_1(X1,k1_zfmisc_1(k1_xboole_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_103]),c_0_104]),c_0_104])])).

cnf(c_0_115,negated_conjecture,
    ( r2_hidden(X1,k7_setfam_1(esk2_0,esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk2_0))
    | ~ r2_hidden(k3_subset_1(esk2_0,X1),esk3_0) ),
    inference(spm,[status(thm)],[c_0_108,c_0_97])).

cnf(c_0_116,negated_conjecture,
    ( r2_hidden(esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_109,c_0_67])).

cnf(c_0_117,negated_conjecture,
    ( k7_setfam_1(esk2_0,esk3_0) != k1_tarski(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

fof(c_0_118,plain,(
    ! [X85,X86] :
      ( ~ m1_subset_1(X86,k1_zfmisc_1(k1_zfmisc_1(X85)))
      | X86 = k1_xboole_0
      | k7_setfam_1(X85,X86) != k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t46_setfam_1])])).

cnf(c_0_119,plain,
    ( X1 = k1_zfmisc_1(k1_xboole_0)
    | X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_93])).

cnf(c_0_120,plain,
    ( r1_tarski(k7_setfam_1(X1,X2),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ r1_tarski(X2,k7_setfam_1(X1,X3)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_87]),c_0_77])).

cnf(c_0_121,plain,
    ( m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_112]),c_0_78])).

cnf(c_0_122,negated_conjecture,
    ( r1_tarski(esk3_0,k7_setfam_1(k3_subset_1(esk2_0,X1),k1_zfmisc_1(k1_xboole_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk2_0))
    | ~ r2_hidden(X1,k7_setfam_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_113,c_0_114])).

cnf(c_0_123,negated_conjecture,
    ( r2_hidden(k1_xboole_0,k7_setfam_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_98]),c_0_94]),c_0_116])])).

cnf(c_0_124,negated_conjecture,
    ( k7_setfam_1(esk2_0,esk3_0) != k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_117,c_0_48]),c_0_34]),c_0_49]),c_0_50]),c_0_51]),c_0_52]),c_0_53])).

cnf(c_0_125,plain,
    ( X1 = k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | k7_setfam_1(X2,X1) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_118])).

cnf(c_0_126,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_85,c_0_67])).

cnf(c_0_127,plain,
    ( k7_setfam_1(X1,X2) = k1_zfmisc_1(k1_xboole_0)
    | k7_setfam_1(X1,X2) = k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ r1_tarski(X2,k7_setfam_1(X1,k1_zfmisc_1(k1_xboole_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_120]),c_0_121])])).

cnf(c_0_128,negated_conjecture,
    ( r1_tarski(esk3_0,k7_setfam_1(esk2_0,k1_zfmisc_1(k1_xboole_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122,c_0_98]),c_0_94]),c_0_123])])).

cnf(c_0_129,negated_conjecture,
    ( k7_setfam_1(esk2_0,esk3_0) != k1_zfmisc_1(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_124,c_0_93])).

cnf(c_0_130,negated_conjecture,
    ( k7_setfam_1(esk2_0,esk3_0) != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_125,c_0_97]),c_0_126])).

cnf(c_0_131,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127,c_0_128]),c_0_97])]),c_0_129]),c_0_130]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 21:10:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.68/0.87  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.68/0.87  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.68/0.87  #
% 0.68/0.87  # Preprocessing time       : 0.029 s
% 0.68/0.87  # Presaturation interreduction done
% 0.68/0.87  
% 0.68/0.87  # Proof found!
% 0.68/0.87  # SZS status Theorem
% 0.68/0.87  # SZS output start CNFRefutation
% 0.68/0.87  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.68/0.87  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.68/0.87  fof(t55_setfam_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(X2=k1_tarski(X1)=>k7_setfam_1(X1,X2)=k1_tarski(k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_setfam_1)).
% 0.68/0.87  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.68/0.87  fof(t39_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,k1_tarski(X2))<=>(X1=k1_xboole_0|X1=k1_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_zfmisc_1)).
% 0.68/0.87  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.68/0.87  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.68/0.87  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.68/0.87  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.68/0.87  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.68/0.87  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.68/0.87  fof(t20_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)<=>X1!=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 0.68/0.87  fof(t11_setfam_1, axiom, ![X1]:k1_setfam_1(k1_tarski(X1))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_setfam_1)).
% 0.68/0.87  fof(l1_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 0.68/0.87  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 0.68/0.87  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 0.68/0.87  fof(dt_k7_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>m1_subset_1(k7_setfam_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_setfam_1)).
% 0.68/0.87  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 0.68/0.87  fof(t63_subset_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 0.68/0.87  fof(dt_k1_subset_1, axiom, ![X1]:m1_subset_1(k1_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_subset_1)).
% 0.68/0.87  fof(d3_subset_1, axiom, ![X1]:k1_subset_1(X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 0.68/0.87  fof(t49_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r2_hidden(k3_subset_1(X1,X3),k7_setfam_1(X1,X2))<=>r2_hidden(X3,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_setfam_1)).
% 0.68/0.87  fof(involutiveness_k7_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>k7_setfam_1(X1,k7_setfam_1(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k7_setfam_1)).
% 0.68/0.87  fof(t22_subset_1, axiom, ![X1]:k2_subset_1(X1)=k3_subset_1(X1,k1_subset_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_subset_1)).
% 0.68/0.87  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 0.68/0.87  fof(t1_zfmisc_1, axiom, k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_zfmisc_1)).
% 0.68/0.87  fof(d6_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:(X9=k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)<=>![X10]:(r2_hidden(X10,X9)<=>~((((((((X10!=X1&X10!=X2)&X10!=X3)&X10!=X4)&X10!=X5)&X10!=X6)&X10!=X7)&X10!=X8)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_enumset1)).
% 0.68/0.87  fof(t51_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(r1_tarski(k7_setfam_1(X1,X2),k7_setfam_1(X1,X3))=>r1_tarski(X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_setfam_1)).
% 0.68/0.87  fof(t46_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>~((X2!=k1_xboole_0&k7_setfam_1(X1,X2)=k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_setfam_1)).
% 0.68/0.87  fof(c_0_29, plain, ![X83, X84]:k1_setfam_1(k2_tarski(X83,X84))=k3_xboole_0(X83,X84), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.68/0.87  fof(c_0_30, plain, ![X15, X16]:k1_enumset1(X15,X15,X16)=k2_tarski(X15,X16), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.68/0.87  fof(c_0_31, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(X2=k1_tarski(X1)=>k7_setfam_1(X1,X2)=k1_tarski(k1_xboole_0)))), inference(assume_negation,[status(cth)],[t55_setfam_1])).
% 0.68/0.87  fof(c_0_32, plain, ![X11, X12]:k4_xboole_0(X11,X12)=k5_xboole_0(X11,k3_xboole_0(X11,X12)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.68/0.87  cnf(c_0_33, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.68/0.87  cnf(c_0_34, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.68/0.87  fof(c_0_35, plain, ![X46, X47]:((~r1_tarski(X46,k1_tarski(X47))|(X46=k1_xboole_0|X46=k1_tarski(X47)))&((X46!=k1_xboole_0|r1_tarski(X46,k1_tarski(X47)))&(X46!=k1_tarski(X47)|r1_tarski(X46,k1_tarski(X47))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t39_zfmisc_1])])])).
% 0.68/0.87  fof(c_0_36, plain, ![X14]:k2_tarski(X14,X14)=k1_tarski(X14), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.68/0.87  fof(c_0_37, plain, ![X17, X18, X19]:k2_enumset1(X17,X17,X18,X19)=k1_enumset1(X17,X18,X19), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.68/0.87  fof(c_0_38, plain, ![X20, X21, X22, X23]:k3_enumset1(X20,X20,X21,X22,X23)=k2_enumset1(X20,X21,X22,X23), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.68/0.87  fof(c_0_39, plain, ![X24, X25, X26, X27, X28]:k4_enumset1(X24,X24,X25,X26,X27,X28)=k3_enumset1(X24,X25,X26,X27,X28), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.68/0.87  fof(c_0_40, plain, ![X29, X30, X31, X32, X33, X34]:k5_enumset1(X29,X29,X30,X31,X32,X33,X34)=k4_enumset1(X29,X30,X31,X32,X33,X34), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.68/0.87  fof(c_0_41, plain, ![X35, X36, X37, X38, X39, X40, X41]:k6_enumset1(X35,X35,X36,X37,X38,X39,X40,X41)=k5_enumset1(X35,X36,X37,X38,X39,X40,X41), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.68/0.87  fof(c_0_42, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))&(esk3_0=k1_tarski(esk2_0)&k7_setfam_1(esk2_0,esk3_0)!=k1_tarski(k1_xboole_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_31])])])).
% 0.68/0.87  fof(c_0_43, plain, ![X44, X45]:((k4_xboole_0(k1_tarski(X44),k1_tarski(X45))!=k1_tarski(X44)|X44!=X45)&(X44=X45|k4_xboole_0(k1_tarski(X44),k1_tarski(X45))=k1_tarski(X44))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_zfmisc_1])])).
% 0.68/0.87  cnf(c_0_44, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.68/0.87  cnf(c_0_45, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_33, c_0_34])).
% 0.68/0.87  fof(c_0_46, plain, ![X82]:k1_setfam_1(k1_tarski(X82))=X82, inference(variable_rename,[status(thm)],[t11_setfam_1])).
% 0.68/0.87  cnf(c_0_47, plain, (X1=k1_xboole_0|X1=k1_tarski(X2)|~r1_tarski(X1,k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.68/0.87  cnf(c_0_48, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.68/0.87  cnf(c_0_49, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.68/0.87  cnf(c_0_50, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.68/0.87  cnf(c_0_51, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.68/0.87  cnf(c_0_52, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.68/0.87  cnf(c_0_53, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.68/0.87  cnf(c_0_54, negated_conjecture, (esk3_0=k1_tarski(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.68/0.87  fof(c_0_55, plain, ![X42, X43]:((~r1_tarski(k1_tarski(X42),X43)|r2_hidden(X42,X43))&(~r2_hidden(X42,X43)|r1_tarski(k1_tarski(X42),X43))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).
% 0.68/0.87  cnf(c_0_56, plain, (k4_xboole_0(k1_tarski(X1),k1_tarski(X2))!=k1_tarski(X1)|X1!=X2), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.68/0.87  cnf(c_0_57, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))), inference(rw,[status(thm)],[c_0_44, c_0_45])).
% 0.68/0.87  cnf(c_0_58, plain, (k1_setfam_1(k1_tarski(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.68/0.87  fof(c_0_59, plain, ![X13]:k5_xboole_0(X13,X13)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 0.68/0.87  fof(c_0_60, plain, ![X48, X49]:(((~m1_subset_1(X49,X48)|r2_hidden(X49,X48)|v1_xboole_0(X48))&(~r2_hidden(X49,X48)|m1_subset_1(X49,X48)|v1_xboole_0(X48)))&((~m1_subset_1(X49,X48)|v1_xboole_0(X49)|~v1_xboole_0(X48))&(~v1_xboole_0(X49)|m1_subset_1(X49,X48)|~v1_xboole_0(X48)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.68/0.87  fof(c_0_61, plain, ![X78, X79]:(~m1_subset_1(X79,k1_zfmisc_1(k1_zfmisc_1(X78)))|m1_subset_1(k7_setfam_1(X78,X79),k1_zfmisc_1(k1_zfmisc_1(X78)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_setfam_1])])).
% 0.68/0.87  fof(c_0_62, plain, ![X74]:~v1_xboole_0(k1_zfmisc_1(X74)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 0.68/0.87  fof(c_0_63, plain, ![X76, X77]:(~r2_hidden(X76,X77)|m1_subset_1(k1_tarski(X76),k1_zfmisc_1(X77))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_subset_1])])).
% 0.68/0.87  fof(c_0_64, plain, ![X73]:m1_subset_1(k1_subset_1(X73),k1_zfmisc_1(X73)), inference(variable_rename,[status(thm)],[dt_k1_subset_1])).
% 0.68/0.87  fof(c_0_65, plain, ![X50]:k1_subset_1(X50)=k1_xboole_0, inference(variable_rename,[status(thm)],[d3_subset_1])).
% 0.68/0.87  cnf(c_0_66, plain, (X1=k1_xboole_0|X1=k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)|~r1_tarski(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_48]), c_0_48]), c_0_34]), c_0_34]), c_0_49]), c_0_49]), c_0_50]), c_0_50]), c_0_51]), c_0_51]), c_0_52]), c_0_52]), c_0_53]), c_0_53])).
% 0.68/0.87  cnf(c_0_67, negated_conjecture, (esk3_0=k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_48]), c_0_34]), c_0_49]), c_0_50]), c_0_51]), c_0_52]), c_0_53])).
% 0.68/0.87  cnf(c_0_68, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.68/0.87  cnf(c_0_69, plain, (X1!=X2|k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))))!=k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_48]), c_0_48]), c_0_48]), c_0_34]), c_0_34]), c_0_34]), c_0_57]), c_0_49]), c_0_49]), c_0_49]), c_0_49]), c_0_49]), c_0_49]), c_0_50]), c_0_50]), c_0_50]), c_0_50]), c_0_50]), c_0_50]), c_0_50]), c_0_51]), c_0_51]), c_0_51]), c_0_51]), c_0_51]), c_0_51]), c_0_51]), c_0_51]), c_0_52]), c_0_52]), c_0_52]), c_0_52]), c_0_52]), c_0_52]), c_0_52]), c_0_52]), c_0_52]), c_0_53]), c_0_53]), c_0_53]), c_0_53]), c_0_53]), c_0_53]), c_0_53]), c_0_53]), c_0_53]), c_0_53])).
% 0.68/0.87  cnf(c_0_70, plain, (k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_48]), c_0_34]), c_0_49]), c_0_50]), c_0_51]), c_0_52]), c_0_53])).
% 0.68/0.87  cnf(c_0_71, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.68/0.87  fof(c_0_72, plain, ![X87, X88, X89]:((~r2_hidden(k3_subset_1(X87,X89),k7_setfam_1(X87,X88))|r2_hidden(X89,X88)|~m1_subset_1(X89,k1_zfmisc_1(X87))|~m1_subset_1(X88,k1_zfmisc_1(k1_zfmisc_1(X87))))&(~r2_hidden(X89,X88)|r2_hidden(k3_subset_1(X87,X89),k7_setfam_1(X87,X88))|~m1_subset_1(X89,k1_zfmisc_1(X87))|~m1_subset_1(X88,k1_zfmisc_1(k1_zfmisc_1(X87))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t49_setfam_1])])])])).
% 0.68/0.87  fof(c_0_73, plain, ![X80, X81]:(~m1_subset_1(X81,k1_zfmisc_1(k1_zfmisc_1(X80)))|k7_setfam_1(X80,k7_setfam_1(X80,X81))=X81), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k7_setfam_1])])).
% 0.68/0.87  fof(c_0_74, plain, ![X75]:k2_subset_1(X75)=k3_subset_1(X75,k1_subset_1(X75)), inference(variable_rename,[status(thm)],[t22_subset_1])).
% 0.68/0.88  fof(c_0_75, plain, ![X51]:k2_subset_1(X51)=X51, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.68/0.88  cnf(c_0_76, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.68/0.88  cnf(c_0_77, plain, (m1_subset_1(k7_setfam_1(X2,X1),k1_zfmisc_1(k1_zfmisc_1(X2)))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.68/0.88  cnf(c_0_78, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.68/0.88  cnf(c_0_79, plain, (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.68/0.88  cnf(c_0_80, plain, (k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(split_conjunct,[status(thm)],[t1_zfmisc_1])).
% 0.68/0.88  cnf(c_0_81, plain, (m1_subset_1(k1_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.68/0.88  cnf(c_0_82, plain, (k1_subset_1(X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.68/0.88  cnf(c_0_83, negated_conjecture, (X1=k1_xboole_0|X1=esk3_0|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.68/0.88  cnf(c_0_84, plain, (r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68, c_0_48]), c_0_34]), c_0_49]), c_0_50]), c_0_51]), c_0_52]), c_0_53])).
% 0.68/0.88  cnf(c_0_85, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_69]), c_0_70]), c_0_71])).
% 0.68/0.88  cnf(c_0_86, plain, (r2_hidden(k3_subset_1(X3,X1),k7_setfam_1(X3,X2))|~r2_hidden(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X3))|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X3)))), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.68/0.88  cnf(c_0_87, plain, (k7_setfam_1(X2,k7_setfam_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.68/0.88  cnf(c_0_88, plain, (k2_subset_1(X1)=k3_subset_1(X1,k1_subset_1(X1))), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.68/0.88  cnf(c_0_89, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.68/0.88  fof(c_0_90, plain, ![X52, X53, X54, X55, X56, X57, X58, X59, X60, X61, X62, X63, X64, X65, X66, X67, X68, X69, X70, X71]:(((~r2_hidden(X61,X60)|(X61=X52|X61=X53|X61=X54|X61=X55|X61=X56|X61=X57|X61=X58|X61=X59)|X60!=k6_enumset1(X52,X53,X54,X55,X56,X57,X58,X59))&((((((((X62!=X52|r2_hidden(X62,X60)|X60!=k6_enumset1(X52,X53,X54,X55,X56,X57,X58,X59))&(X62!=X53|r2_hidden(X62,X60)|X60!=k6_enumset1(X52,X53,X54,X55,X56,X57,X58,X59)))&(X62!=X54|r2_hidden(X62,X60)|X60!=k6_enumset1(X52,X53,X54,X55,X56,X57,X58,X59)))&(X62!=X55|r2_hidden(X62,X60)|X60!=k6_enumset1(X52,X53,X54,X55,X56,X57,X58,X59)))&(X62!=X56|r2_hidden(X62,X60)|X60!=k6_enumset1(X52,X53,X54,X55,X56,X57,X58,X59)))&(X62!=X57|r2_hidden(X62,X60)|X60!=k6_enumset1(X52,X53,X54,X55,X56,X57,X58,X59)))&(X62!=X58|r2_hidden(X62,X60)|X60!=k6_enumset1(X52,X53,X54,X55,X56,X57,X58,X59)))&(X62!=X59|r2_hidden(X62,X60)|X60!=k6_enumset1(X52,X53,X54,X55,X56,X57,X58,X59))))&(((((((((esk1_9(X63,X64,X65,X66,X67,X68,X69,X70,X71)!=X63|~r2_hidden(esk1_9(X63,X64,X65,X66,X67,X68,X69,X70,X71),X71)|X71=k6_enumset1(X63,X64,X65,X66,X67,X68,X69,X70))&(esk1_9(X63,X64,X65,X66,X67,X68,X69,X70,X71)!=X64|~r2_hidden(esk1_9(X63,X64,X65,X66,X67,X68,X69,X70,X71),X71)|X71=k6_enumset1(X63,X64,X65,X66,X67,X68,X69,X70)))&(esk1_9(X63,X64,X65,X66,X67,X68,X69,X70,X71)!=X65|~r2_hidden(esk1_9(X63,X64,X65,X66,X67,X68,X69,X70,X71),X71)|X71=k6_enumset1(X63,X64,X65,X66,X67,X68,X69,X70)))&(esk1_9(X63,X64,X65,X66,X67,X68,X69,X70,X71)!=X66|~r2_hidden(esk1_9(X63,X64,X65,X66,X67,X68,X69,X70,X71),X71)|X71=k6_enumset1(X63,X64,X65,X66,X67,X68,X69,X70)))&(esk1_9(X63,X64,X65,X66,X67,X68,X69,X70,X71)!=X67|~r2_hidden(esk1_9(X63,X64,X65,X66,X67,X68,X69,X70,X71),X71)|X71=k6_enumset1(X63,X64,X65,X66,X67,X68,X69,X70)))&(esk1_9(X63,X64,X65,X66,X67,X68,X69,X70,X71)!=X68|~r2_hidden(esk1_9(X63,X64,X65,X66,X67,X68,X69,X70,X71),X71)|X71=k6_enumset1(X63,X64,X65,X66,X67,X68,X69,X70)))&(esk1_9(X63,X64,X65,X66,X67,X68,X69,X70,X71)!=X69|~r2_hidden(esk1_9(X63,X64,X65,X66,X67,X68,X69,X70,X71),X71)|X71=k6_enumset1(X63,X64,X65,X66,X67,X68,X69,X70)))&(esk1_9(X63,X64,X65,X66,X67,X68,X69,X70,X71)!=X70|~r2_hidden(esk1_9(X63,X64,X65,X66,X67,X68,X69,X70,X71),X71)|X71=k6_enumset1(X63,X64,X65,X66,X67,X68,X69,X70)))&(r2_hidden(esk1_9(X63,X64,X65,X66,X67,X68,X69,X70,X71),X71)|(esk1_9(X63,X64,X65,X66,X67,X68,X69,X70,X71)=X63|esk1_9(X63,X64,X65,X66,X67,X68,X69,X70,X71)=X64|esk1_9(X63,X64,X65,X66,X67,X68,X69,X70,X71)=X65|esk1_9(X63,X64,X65,X66,X67,X68,X69,X70,X71)=X66|esk1_9(X63,X64,X65,X66,X67,X68,X69,X70,X71)=X67|esk1_9(X63,X64,X65,X66,X67,X68,X69,X70,X71)=X68|esk1_9(X63,X64,X65,X66,X67,X68,X69,X70,X71)=X69|esk1_9(X63,X64,X65,X66,X67,X68,X69,X70,X71)=X70)|X71=k6_enumset1(X63,X64,X65,X66,X67,X68,X69,X70)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_enumset1])])])])])])).
% 0.68/0.88  cnf(c_0_91, plain, (r2_hidden(k7_setfam_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1)))|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_78])).
% 0.68/0.88  cnf(c_0_92, plain, (m1_subset_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_zfmisc_1(X2))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79, c_0_48]), c_0_34]), c_0_49]), c_0_50]), c_0_51]), c_0_52]), c_0_53])).
% 0.68/0.88  cnf(c_0_93, plain, (k1_zfmisc_1(k1_xboole_0)=k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80, c_0_48]), c_0_34]), c_0_49]), c_0_50]), c_0_51]), c_0_52]), c_0_53])).
% 0.68/0.88  cnf(c_0_94, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_81, c_0_82])).
% 0.68/0.88  cnf(c_0_95, negated_conjecture, (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)=esk3_0|~r2_hidden(X1,esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_85])).
% 0.68/0.88  cnf(c_0_96, plain, (r2_hidden(k3_subset_1(X1,X2),X3)|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r2_hidden(X2,k7_setfam_1(X1,X3))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_77])).
% 0.68/0.88  cnf(c_0_97, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.68/0.88  cnf(c_0_98, plain, (X1=k3_subset_1(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_88, c_0_89]), c_0_82])).
% 0.68/0.88  cnf(c_0_99, plain, (r2_hidden(X2,X3)|~r2_hidden(k3_subset_1(X1,X2),k7_setfam_1(X1,X3))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.68/0.88  cnf(c_0_100, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k6_enumset1(X4,X5,X6,X7,X8,X9,X10,X2)), inference(split_conjunct,[status(thm)],[c_0_90])).
% 0.68/0.88  fof(c_0_101, plain, ![X90, X91, X92]:(~m1_subset_1(X91,k1_zfmisc_1(k1_zfmisc_1(X90)))|(~m1_subset_1(X92,k1_zfmisc_1(k1_zfmisc_1(X90)))|(~r1_tarski(k7_setfam_1(X90,X91),k7_setfam_1(X90,X92))|r1_tarski(X91,X92)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t51_setfam_1])])])).
% 0.68/0.88  cnf(c_0_102, plain, (r2_hidden(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_87]), c_0_77])).
% 0.68/0.88  cnf(c_0_103, plain, (m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(X1))|~r2_hidden(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_92, c_0_93])).
% 0.68/0.88  cnf(c_0_104, plain, (r2_hidden(k1_xboole_0,k1_zfmisc_1(X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_94]), c_0_78])).
% 0.68/0.88  cnf(c_0_105, negated_conjecture, (r1_tarski(esk3_0,X1)|~r2_hidden(X2,esk3_0)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_84, c_0_95])).
% 0.68/0.88  cnf(c_0_106, negated_conjecture, (r2_hidden(k3_subset_1(esk2_0,X1),esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(esk2_0))|~r2_hidden(X1,k7_setfam_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_96, c_0_97])).
% 0.68/0.88  cnf(c_0_107, plain, (r2_hidden(X1,k7_setfam_1(X1,X2))|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))|~r2_hidden(k1_xboole_0,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_98]), c_0_94])])).
% 0.68/0.88  cnf(c_0_108, plain, (r2_hidden(X1,k7_setfam_1(X2,X3))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(k3_subset_1(X2,X1),X3)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_87]), c_0_77])).
% 0.68/0.88  cnf(c_0_109, plain, (r2_hidden(X1,k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_100])])).
% 0.68/0.88  cnf(c_0_110, plain, (r1_tarski(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))|~r1_tarski(k7_setfam_1(X2,X1),k7_setfam_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_101])).
% 0.68/0.88  cnf(c_0_111, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.68/0.88  cnf(c_0_112, plain, (r2_hidden(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_103]), c_0_104])])).
% 0.68/0.88  cnf(c_0_113, negated_conjecture, (r1_tarski(esk3_0,X1)|~m1_subset_1(X2,k1_zfmisc_1(esk2_0))|~r2_hidden(X2,k7_setfam_1(esk2_0,esk3_0))|~r2_hidden(k3_subset_1(esk2_0,X2),X1)), inference(spm,[status(thm)],[c_0_105, c_0_106])).
% 0.68/0.88  cnf(c_0_114, plain, (r2_hidden(X1,k7_setfam_1(X1,k1_zfmisc_1(k1_xboole_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_103]), c_0_104]), c_0_104])])).
% 0.68/0.88  cnf(c_0_115, negated_conjecture, (r2_hidden(X1,k7_setfam_1(esk2_0,esk3_0))|~m1_subset_1(X1,k1_zfmisc_1(esk2_0))|~r2_hidden(k3_subset_1(esk2_0,X1),esk3_0)), inference(spm,[status(thm)],[c_0_108, c_0_97])).
% 0.68/0.88  cnf(c_0_116, negated_conjecture, (r2_hidden(esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_109, c_0_67])).
% 0.68/0.88  cnf(c_0_117, negated_conjecture, (k7_setfam_1(esk2_0,esk3_0)!=k1_tarski(k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.68/0.88  fof(c_0_118, plain, ![X85, X86]:(~m1_subset_1(X86,k1_zfmisc_1(k1_zfmisc_1(X85)))|(X86=k1_xboole_0|k7_setfam_1(X85,X86)!=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t46_setfam_1])])).
% 0.68/0.88  cnf(c_0_119, plain, (X1=k1_zfmisc_1(k1_xboole_0)|X1=k1_xboole_0|~r1_tarski(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_66, c_0_93])).
% 0.68/0.88  cnf(c_0_120, plain, (r1_tarski(k7_setfam_1(X1,X2),X3)|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))|~r1_tarski(X2,k7_setfam_1(X1,X3))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_87]), c_0_77])).
% 0.68/0.88  cnf(c_0_121, plain, (m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_112]), c_0_78])).
% 0.68/0.88  cnf(c_0_122, negated_conjecture, (r1_tarski(esk3_0,k7_setfam_1(k3_subset_1(esk2_0,X1),k1_zfmisc_1(k1_xboole_0)))|~m1_subset_1(X1,k1_zfmisc_1(esk2_0))|~r2_hidden(X1,k7_setfam_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_113, c_0_114])).
% 0.68/0.88  cnf(c_0_123, negated_conjecture, (r2_hidden(k1_xboole_0,k7_setfam_1(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_98]), c_0_94]), c_0_116])])).
% 0.68/0.88  cnf(c_0_124, negated_conjecture, (k7_setfam_1(esk2_0,esk3_0)!=k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_117, c_0_48]), c_0_34]), c_0_49]), c_0_50]), c_0_51]), c_0_52]), c_0_53])).
% 0.68/0.88  cnf(c_0_125, plain, (X1=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))|k7_setfam_1(X2,X1)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_118])).
% 0.68/0.88  cnf(c_0_126, negated_conjecture, (esk3_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_85, c_0_67])).
% 0.68/0.88  cnf(c_0_127, plain, (k7_setfam_1(X1,X2)=k1_zfmisc_1(k1_xboole_0)|k7_setfam_1(X1,X2)=k1_xboole_0|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))|~r1_tarski(X2,k7_setfam_1(X1,k1_zfmisc_1(k1_xboole_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119, c_0_120]), c_0_121])])).
% 0.68/0.88  cnf(c_0_128, negated_conjecture, (r1_tarski(esk3_0,k7_setfam_1(esk2_0,k1_zfmisc_1(k1_xboole_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122, c_0_98]), c_0_94]), c_0_123])])).
% 0.68/0.88  cnf(c_0_129, negated_conjecture, (k7_setfam_1(esk2_0,esk3_0)!=k1_zfmisc_1(k1_xboole_0)), inference(rw,[status(thm)],[c_0_124, c_0_93])).
% 0.68/0.88  cnf(c_0_130, negated_conjecture, (k7_setfam_1(esk2_0,esk3_0)!=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_125, c_0_97]), c_0_126])).
% 0.68/0.88  cnf(c_0_131, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127, c_0_128]), c_0_97])]), c_0_129]), c_0_130]), ['proof']).
% 0.68/0.88  # SZS output end CNFRefutation
% 0.68/0.88  # Proof object total steps             : 132
% 0.68/0.88  # Proof object clause steps            : 74
% 0.68/0.88  # Proof object formula steps           : 58
% 0.68/0.88  # Proof object conjectures             : 22
% 0.68/0.88  # Proof object clause conjectures      : 19
% 0.68/0.88  # Proof object formula conjectures     : 3
% 0.68/0.88  # Proof object initial clauses used    : 33
% 0.68/0.88  # Proof object initial formulas used   : 29
% 0.68/0.88  # Proof object generating inferences   : 26
% 0.68/0.88  # Proof object simplifying inferences  : 142
% 0.68/0.88  # Training examples: 0 positive, 0 negative
% 0.68/0.88  # Parsed axioms                        : 29
% 0.68/0.88  # Removed by relevancy pruning/SinE    : 0
% 0.68/0.88  # Initial clauses                      : 56
% 0.68/0.88  # Removed in clause preprocessing      : 11
% 0.68/0.88  # Initial clauses in saturation        : 45
% 0.68/0.88  # Processed clauses                    : 2393
% 0.68/0.88  # ...of these trivial                  : 8
% 0.68/0.88  # ...subsumed                          : 1747
% 0.68/0.88  # ...remaining for further processing  : 638
% 0.68/0.88  # Other redundant clauses eliminated   : 1817
% 0.68/0.88  # Clauses deleted for lack of memory   : 0
% 0.68/0.88  # Backward-subsumed                    : 38
% 0.68/0.88  # Backward-rewritten                   : 6
% 0.68/0.88  # Generated clauses                    : 11948
% 0.68/0.88  # ...of the previous two non-trivial   : 6984
% 0.68/0.88  # Contextual simplify-reflections      : 36
% 0.68/0.88  # Paramodulations                      : 4809
% 0.68/0.88  # Factorizations                       : 5330
% 0.68/0.88  # Equation resolutions                 : 1817
% 0.68/0.88  # Propositional unsat checks           : 0
% 0.68/0.88  #    Propositional check models        : 0
% 0.68/0.88  #    Propositional check unsatisfiable : 0
% 0.68/0.88  #    Propositional clauses             : 0
% 0.68/0.88  #    Propositional clauses after purity: 0
% 0.68/0.88  #    Propositional unsat core size     : 0
% 0.68/0.88  #    Propositional preprocessing time  : 0.000
% 0.68/0.88  #    Propositional encoding time       : 0.000
% 0.68/0.88  #    Propositional solver time         : 0.000
% 0.68/0.88  #    Success case prop preproc time    : 0.000
% 0.68/0.88  #    Success case prop encoding time   : 0.000
% 0.68/0.88  #    Success case prop solver time     : 0.000
% 0.68/0.88  # Current number of processed clauses  : 537
% 0.68/0.88  #    Positive orientable unit clauses  : 37
% 0.68/0.88  #    Positive unorientable unit clauses: 0
% 0.68/0.88  #    Negative unit clauses             : 11
% 0.68/0.88  #    Non-unit-clauses                  : 489
% 0.68/0.88  # Current number of unprocessed clauses: 4616
% 0.68/0.88  # ...number of literals in the above   : 36123
% 0.68/0.88  # Current number of archived formulas  : 0
% 0.68/0.88  # Current number of archived clauses   : 100
% 0.68/0.88  # Clause-clause subsumption calls (NU) : 72880
% 0.68/0.88  # Rec. Clause-clause subsumption calls : 20456
% 0.68/0.88  # Non-unit clause-clause subsumptions  : 1663
% 0.68/0.88  # Unit Clause-clause subsumption calls : 336
% 0.68/0.88  # Rewrite failures with RHS unbound    : 0
% 0.68/0.88  # BW rewrite match attempts            : 73
% 0.68/0.88  # BW rewrite match successes           : 6
% 0.68/0.88  # Condensation attempts                : 0
% 0.68/0.88  # Condensation successes               : 0
% 0.68/0.88  # Termbank termtop insertions          : 129447
% 0.68/0.88  
% 0.68/0.88  # -------------------------------------------------
% 0.68/0.88  # User time                : 0.522 s
% 0.68/0.88  # System time              : 0.013 s
% 0.68/0.88  # Total time               : 0.535 s
% 0.68/0.88  # Maximum resident set size: 1604 pages
%------------------------------------------------------------------------------
