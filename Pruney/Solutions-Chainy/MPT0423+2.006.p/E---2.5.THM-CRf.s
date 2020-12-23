%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:47:45 EST 2020

% Result     : Theorem 0.88s
% Output     : CNFRefutation 0.88s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 640 expanded)
%              Number of clauses        :   63 ( 244 expanded)
%              Number of leaves         :   29 ( 198 expanded)
%              Depth                    :   12
%              Number of atoms          :  294 ( 867 expanded)
%              Number of equality atoms :  161 ( 653 expanded)
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

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(t51_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
         => ( r1_tarski(k7_setfam_1(X1,X2),k7_setfam_1(X1,X3))
           => r1_tarski(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_setfam_1)).

fof(involutiveness_k7_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => k7_setfam_1(X1,k7_setfam_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

fof(dt_k7_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => m1_subset_1(k7_setfam_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_setfam_1)).

fof(t63_subset_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(dt_k1_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_subset_1)).

fof(d3_subset_1,axiom,(
    ! [X1] : k1_subset_1(X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

fof(t46_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ~ ( X2 != k1_xboole_0
          & k7_setfam_1(X1,X2) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_setfam_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(t49_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( r2_hidden(k3_subset_1(X1,X3),k7_setfam_1(X1,X2))
          <=> r2_hidden(X3,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_setfam_1)).

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

fof(t1_zfmisc_1,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).

fof(t37_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_zfmisc_1)).

fof(t22_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = k3_subset_1(X1,k1_subset_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(c_0_29,plain,(
    ! [X81,X82] : k1_setfam_1(k2_tarski(X81,X82)) = k3_xboole_0(X81,X82) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_30,plain,(
    ! [X16,X17] : k1_enumset1(X16,X16,X17) = k2_tarski(X16,X17) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_31,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
       => ( X2 = k1_tarski(X1)
         => k7_setfam_1(X1,X2) = k1_tarski(k1_xboole_0) ) ) ),
    inference(assume_negation,[status(cth)],[t55_setfam_1])).

fof(c_0_32,plain,(
    ! [X12,X13] : k4_xboole_0(X12,X13) = k5_xboole_0(X12,k3_xboole_0(X12,X13)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_33,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_34,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_35,plain,(
    ! [X47,X48] :
      ( ( ~ r1_tarski(X47,k1_tarski(X48))
        | X47 = k1_xboole_0
        | X47 = k1_tarski(X48) )
      & ( X47 != k1_xboole_0
        | r1_tarski(X47,k1_tarski(X48)) )
      & ( X47 != k1_tarski(X48)
        | r1_tarski(X47,k1_tarski(X48)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t39_zfmisc_1])])])).

fof(c_0_36,plain,(
    ! [X15] : k2_tarski(X15,X15) = k1_tarski(X15) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_37,plain,(
    ! [X18,X19,X20] : k2_enumset1(X18,X18,X19,X20) = k1_enumset1(X18,X19,X20) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_38,plain,(
    ! [X21,X22,X23,X24] : k3_enumset1(X21,X21,X22,X23,X24) = k2_enumset1(X21,X22,X23,X24) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_39,plain,(
    ! [X25,X26,X27,X28,X29] : k4_enumset1(X25,X25,X26,X27,X28,X29) = k3_enumset1(X25,X26,X27,X28,X29) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_40,plain,(
    ! [X30,X31,X32,X33,X34,X35] : k5_enumset1(X30,X30,X31,X32,X33,X34,X35) = k4_enumset1(X30,X31,X32,X33,X34,X35) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_41,plain,(
    ! [X36,X37,X38,X39,X40,X41,X42] : k6_enumset1(X36,X36,X37,X38,X39,X40,X41,X42) = k5_enumset1(X36,X37,X38,X39,X40,X41,X42) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_42,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))
    & esk3_0 = k1_tarski(esk2_0)
    & k7_setfam_1(esk2_0,esk3_0) != k1_tarski(k1_xboole_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_31])])])).

fof(c_0_43,plain,(
    ! [X43,X44] :
      ( ( k4_xboole_0(k1_tarski(X43),k1_tarski(X44)) != k1_tarski(X43)
        | X43 != X44 )
      & ( X43 = X44
        | k4_xboole_0(k1_tarski(X43),k1_tarski(X44)) = k1_tarski(X43) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_zfmisc_1])])).

cnf(c_0_44,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_45,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_33,c_0_34])).

fof(c_0_46,plain,(
    ! [X11] : k3_xboole_0(X11,X11) = X11 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

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
    ! [X90,X91,X92] :
      ( ~ m1_subset_1(X91,k1_zfmisc_1(k1_zfmisc_1(X90)))
      | ~ m1_subset_1(X92,k1_zfmisc_1(k1_zfmisc_1(X90)))
      | ~ r1_tarski(k7_setfam_1(X90,X91),k7_setfam_1(X90,X92))
      | r1_tarski(X91,X92) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t51_setfam_1])])])).

fof(c_0_56,plain,(
    ! [X79,X80] :
      ( ~ m1_subset_1(X80,k1_zfmisc_1(k1_zfmisc_1(X79)))
      | k7_setfam_1(X79,k7_setfam_1(X79,X80)) = X80 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k7_setfam_1])])).

fof(c_0_57,plain,(
    ! [X77,X78] :
      ( ~ m1_subset_1(X78,k1_zfmisc_1(k1_zfmisc_1(X77)))
      | m1_subset_1(k7_setfam_1(X77,X78),k1_zfmisc_1(k1_zfmisc_1(X77))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_setfam_1])])).

fof(c_0_58,plain,(
    ! [X75,X76] :
      ( ~ r2_hidden(X75,X76)
      | m1_subset_1(k1_tarski(X75),k1_zfmisc_1(X76)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_subset_1])])).

cnf(c_0_59,plain,
    ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) != k1_tarski(X1)
    | X1 != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_60,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_61,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

fof(c_0_62,plain,(
    ! [X14] : k5_xboole_0(X14,X14) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

fof(c_0_63,plain,(
    ! [X72] : m1_subset_1(k1_subset_1(X72),k1_zfmisc_1(X72)) ),
    inference(variable_rename,[status(thm)],[dt_k1_subset_1])).

fof(c_0_64,plain,(
    ! [X49] : k1_subset_1(X49) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[d3_subset_1])).

cnf(c_0_65,plain,
    ( X1 = k1_xboole_0
    | X1 = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)
    | ~ r1_tarski(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_48]),c_0_48]),c_0_34]),c_0_34]),c_0_49]),c_0_49]),c_0_50]),c_0_50]),c_0_51]),c_0_51]),c_0_52]),c_0_52]),c_0_53]),c_0_53])).

cnf(c_0_66,negated_conjecture,
    ( esk3_0 = k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_48]),c_0_34]),c_0_49]),c_0_50]),c_0_51]),c_0_52]),c_0_53])).

cnf(c_0_67,plain,
    ( r1_tarski(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ r1_tarski(k7_setfam_1(X2,X1),k7_setfam_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_68,plain,
    ( k7_setfam_1(X2,k7_setfam_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_69,plain,
    ( m1_subset_1(k7_setfam_1(X2,X1),k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

fof(c_0_70,plain,(
    ! [X85,X86] :
      ( ~ m1_subset_1(X86,k1_zfmisc_1(k1_zfmisc_1(X85)))
      | X86 = k1_xboole_0
      | k7_setfam_1(X85,X86) != k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t46_setfam_1])])).

cnf(c_0_71,plain,
    ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_72,plain,
    ( X1 != X2
    | k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)))) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_48]),c_0_48]),c_0_48]),c_0_34]),c_0_34]),c_0_34]),c_0_60]),c_0_49]),c_0_49]),c_0_49]),c_0_49]),c_0_49]),c_0_49]),c_0_50]),c_0_50]),c_0_50]),c_0_50]),c_0_50]),c_0_50]),c_0_50]),c_0_51]),c_0_51]),c_0_51]),c_0_51]),c_0_51]),c_0_51]),c_0_51]),c_0_51]),c_0_52]),c_0_52]),c_0_52]),c_0_52]),c_0_52]),c_0_52]),c_0_52]),c_0_52]),c_0_52]),c_0_53]),c_0_53]),c_0_53]),c_0_53]),c_0_53]),c_0_53]),c_0_53]),c_0_53]),c_0_53]),c_0_53])).

cnf(c_0_73,plain,
    ( k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_45]),c_0_49]),c_0_50]),c_0_51]),c_0_52]),c_0_53])).

cnf(c_0_74,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

fof(c_0_75,plain,(
    ! [X83,X84] :
      ( ~ m1_subset_1(X83,X84)
      | v1_xboole_0(X84)
      | r2_hidden(X83,X84) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_76,plain,
    ( m1_subset_1(k1_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_77,plain,
    ( k1_subset_1(X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

fof(c_0_78,plain,(
    ! [X73] : ~ v1_xboole_0(k1_zfmisc_1(X73)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

fof(c_0_79,plain,(
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

fof(c_0_80,plain,(
    ! [X51,X52,X53,X54,X55,X56,X57,X58,X59,X60,X61,X62,X63,X64,X65,X66,X67,X68,X69,X70] :
      ( ( ~ r2_hidden(X60,X59)
        | X60 = X51
        | X60 = X52
        | X60 = X53
        | X60 = X54
        | X60 = X55
        | X60 = X56
        | X60 = X57
        | X60 = X58
        | X59 != k6_enumset1(X51,X52,X53,X54,X55,X56,X57,X58) )
      & ( X61 != X51
        | r2_hidden(X61,X59)
        | X59 != k6_enumset1(X51,X52,X53,X54,X55,X56,X57,X58) )
      & ( X61 != X52
        | r2_hidden(X61,X59)
        | X59 != k6_enumset1(X51,X52,X53,X54,X55,X56,X57,X58) )
      & ( X61 != X53
        | r2_hidden(X61,X59)
        | X59 != k6_enumset1(X51,X52,X53,X54,X55,X56,X57,X58) )
      & ( X61 != X54
        | r2_hidden(X61,X59)
        | X59 != k6_enumset1(X51,X52,X53,X54,X55,X56,X57,X58) )
      & ( X61 != X55
        | r2_hidden(X61,X59)
        | X59 != k6_enumset1(X51,X52,X53,X54,X55,X56,X57,X58) )
      & ( X61 != X56
        | r2_hidden(X61,X59)
        | X59 != k6_enumset1(X51,X52,X53,X54,X55,X56,X57,X58) )
      & ( X61 != X57
        | r2_hidden(X61,X59)
        | X59 != k6_enumset1(X51,X52,X53,X54,X55,X56,X57,X58) )
      & ( X61 != X58
        | r2_hidden(X61,X59)
        | X59 != k6_enumset1(X51,X52,X53,X54,X55,X56,X57,X58) )
      & ( esk1_9(X62,X63,X64,X65,X66,X67,X68,X69,X70) != X62
        | ~ r2_hidden(esk1_9(X62,X63,X64,X65,X66,X67,X68,X69,X70),X70)
        | X70 = k6_enumset1(X62,X63,X64,X65,X66,X67,X68,X69) )
      & ( esk1_9(X62,X63,X64,X65,X66,X67,X68,X69,X70) != X63
        | ~ r2_hidden(esk1_9(X62,X63,X64,X65,X66,X67,X68,X69,X70),X70)
        | X70 = k6_enumset1(X62,X63,X64,X65,X66,X67,X68,X69) )
      & ( esk1_9(X62,X63,X64,X65,X66,X67,X68,X69,X70) != X64
        | ~ r2_hidden(esk1_9(X62,X63,X64,X65,X66,X67,X68,X69,X70),X70)
        | X70 = k6_enumset1(X62,X63,X64,X65,X66,X67,X68,X69) )
      & ( esk1_9(X62,X63,X64,X65,X66,X67,X68,X69,X70) != X65
        | ~ r2_hidden(esk1_9(X62,X63,X64,X65,X66,X67,X68,X69,X70),X70)
        | X70 = k6_enumset1(X62,X63,X64,X65,X66,X67,X68,X69) )
      & ( esk1_9(X62,X63,X64,X65,X66,X67,X68,X69,X70) != X66
        | ~ r2_hidden(esk1_9(X62,X63,X64,X65,X66,X67,X68,X69,X70),X70)
        | X70 = k6_enumset1(X62,X63,X64,X65,X66,X67,X68,X69) )
      & ( esk1_9(X62,X63,X64,X65,X66,X67,X68,X69,X70) != X67
        | ~ r2_hidden(esk1_9(X62,X63,X64,X65,X66,X67,X68,X69,X70),X70)
        | X70 = k6_enumset1(X62,X63,X64,X65,X66,X67,X68,X69) )
      & ( esk1_9(X62,X63,X64,X65,X66,X67,X68,X69,X70) != X68
        | ~ r2_hidden(esk1_9(X62,X63,X64,X65,X66,X67,X68,X69,X70),X70)
        | X70 = k6_enumset1(X62,X63,X64,X65,X66,X67,X68,X69) )
      & ( esk1_9(X62,X63,X64,X65,X66,X67,X68,X69,X70) != X69
        | ~ r2_hidden(esk1_9(X62,X63,X64,X65,X66,X67,X68,X69,X70),X70)
        | X70 = k6_enumset1(X62,X63,X64,X65,X66,X67,X68,X69) )
      & ( r2_hidden(esk1_9(X62,X63,X64,X65,X66,X67,X68,X69,X70),X70)
        | esk1_9(X62,X63,X64,X65,X66,X67,X68,X69,X70) = X62
        | esk1_9(X62,X63,X64,X65,X66,X67,X68,X69,X70) = X63
        | esk1_9(X62,X63,X64,X65,X66,X67,X68,X69,X70) = X64
        | esk1_9(X62,X63,X64,X65,X66,X67,X68,X69,X70) = X65
        | esk1_9(X62,X63,X64,X65,X66,X67,X68,X69,X70) = X66
        | esk1_9(X62,X63,X64,X65,X66,X67,X68,X69,X70) = X67
        | esk1_9(X62,X63,X64,X65,X66,X67,X68,X69,X70) = X68
        | esk1_9(X62,X63,X64,X65,X66,X67,X68,X69,X70) = X69
        | X70 = k6_enumset1(X62,X63,X64,X65,X66,X67,X68,X69) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_enumset1])])])])])])).

cnf(c_0_81,negated_conjecture,
    ( X1 = k1_xboole_0
    | X1 = esk3_0
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_82,plain,
    ( r1_tarski(k7_setfam_1(X1,X2),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ r1_tarski(X2,k7_setfam_1(X1,X3)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_69])).

cnf(c_0_83,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[t1_zfmisc_1])).

cnf(c_0_84,plain,
    ( X1 = k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | k7_setfam_1(X2,X1) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_85,plain,
    ( m1_subset_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_48]),c_0_34]),c_0_49]),c_0_50]),c_0_51]),c_0_52]),c_0_53])).

cnf(c_0_86,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_72]),c_0_73]),c_0_74])).

cnf(c_0_87,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_88,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_89,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

fof(c_0_90,plain,(
    ! [X45,X46] :
      ( ( ~ r1_tarski(k1_tarski(X45),X46)
        | r2_hidden(X45,X46) )
      & ( ~ r2_hidden(X45,X46)
        | r1_tarski(k1_tarski(X45),X46) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_zfmisc_1])])).

cnf(c_0_91,plain,
    ( r2_hidden(X2,X3)
    | ~ r2_hidden(k3_subset_1(X1,X2),k7_setfam_1(X1,X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

fof(c_0_92,plain,(
    ! [X74] : k2_subset_1(X74) = k3_subset_1(X74,k1_subset_1(X74)) ),
    inference(variable_rename,[status(thm)],[t22_subset_1])).

fof(c_0_93,plain,(
    ! [X50] : k2_subset_1(X50) = X50 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

cnf(c_0_94,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k6_enumset1(X4,X5,X6,X7,X8,X9,X10,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_95,negated_conjecture,
    ( k7_setfam_1(X1,X2) = esk3_0
    | k7_setfam_1(X1,X2) = k1_xboole_0
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ r1_tarski(X2,k7_setfam_1(X1,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_96,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_97,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_83,c_0_48]),c_0_34]),c_0_49]),c_0_50]),c_0_51]),c_0_52]),c_0_53])).

cnf(c_0_98,plain,
    ( k7_setfam_1(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) != k1_xboole_0
    | ~ r2_hidden(X2,k1_zfmisc_1(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_86])).

cnf(c_0_99,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_89])).

cnf(c_0_100,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_90])).

cnf(c_0_101,plain,
    ( r2_hidden(X1,k7_setfam_1(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(k3_subset_1(X2,X1),X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_68]),c_0_69])).

cnf(c_0_102,plain,
    ( k2_subset_1(X1) = k3_subset_1(X1,k1_subset_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_92])).

cnf(c_0_103,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_93])).

cnf(c_0_104,plain,
    ( r2_hidden(X1,k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_94])])).

cnf(c_0_105,negated_conjecture,
    ( k7_setfam_1(esk2_0,X1) = k1_xboole_0
    | k7_setfam_1(esk2_0,X1) = esk3_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))
    | ~ r1_tarski(X1,k7_setfam_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_95,c_0_96])).

cnf(c_0_106,plain,
    ( m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(X1))
    | ~ r2_hidden(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_85,c_0_97])).

cnf(c_0_107,plain,
    ( k7_setfam_1(X1,k1_zfmisc_1(k1_xboole_0)) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_97]),c_0_99])])).

cnf(c_0_108,plain,
    ( r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_100,c_0_48]),c_0_34]),c_0_49]),c_0_50]),c_0_51]),c_0_52]),c_0_53])).

cnf(c_0_109,negated_conjecture,
    ( r2_hidden(X1,k7_setfam_1(esk2_0,esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk2_0))
    | ~ r2_hidden(k3_subset_1(esk2_0,X1),esk3_0) ),
    inference(spm,[status(thm)],[c_0_101,c_0_96])).

cnf(c_0_110,plain,
    ( X1 = k3_subset_1(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_102,c_0_103]),c_0_77])).

cnf(c_0_111,negated_conjecture,
    ( r2_hidden(esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_104,c_0_66])).

cnf(c_0_112,negated_conjecture,
    ( k7_setfam_1(esk2_0,esk3_0) != k1_tarski(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_113,negated_conjecture,
    ( k7_setfam_1(esk2_0,k1_zfmisc_1(k1_xboole_0)) = esk3_0
    | ~ r1_tarski(k1_zfmisc_1(k1_xboole_0),k7_setfam_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_106]),c_0_99])]),c_0_107])).

cnf(c_0_114,plain,
    ( r1_tarski(k1_zfmisc_1(k1_xboole_0),X1)
    | ~ r2_hidden(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_108,c_0_97])).

cnf(c_0_115,negated_conjecture,
    ( r2_hidden(k1_xboole_0,k7_setfam_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_110]),c_0_88]),c_0_111])])).

cnf(c_0_116,negated_conjecture,
    ( k7_setfam_1(esk2_0,esk3_0) != k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_112,c_0_48]),c_0_34]),c_0_49]),c_0_50]),c_0_51]),c_0_52]),c_0_53])).

cnf(c_0_117,negated_conjecture,
    ( k7_setfam_1(esk2_0,k1_zfmisc_1(k1_xboole_0)) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_114]),c_0_115])])).

cnf(c_0_118,negated_conjecture,
    ( k7_setfam_1(esk2_0,esk3_0) != k1_zfmisc_1(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_116,c_0_97])).

cnf(c_0_119,negated_conjecture,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(esk2_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_117]),c_0_118])).

cnf(c_0_120,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_106]),c_0_99])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:56:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.88/1.08  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.88/1.08  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.88/1.08  #
% 0.88/1.08  # Preprocessing time       : 0.029 s
% 0.88/1.08  # Presaturation interreduction done
% 0.88/1.08  
% 0.88/1.08  # Proof found!
% 0.88/1.08  # SZS status Theorem
% 0.88/1.08  # SZS output start CNFRefutation
% 0.88/1.08  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.88/1.08  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.88/1.08  fof(t55_setfam_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(X2=k1_tarski(X1)=>k7_setfam_1(X1,X2)=k1_tarski(k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_setfam_1)).
% 0.88/1.08  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.88/1.08  fof(t39_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,k1_tarski(X2))<=>(X1=k1_xboole_0|X1=k1_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_zfmisc_1)).
% 0.88/1.08  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.88/1.08  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.88/1.08  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.88/1.08  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.88/1.08  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.88/1.08  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.88/1.08  fof(t20_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)<=>X1!=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 0.88/1.08  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.88/1.08  fof(t51_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(r1_tarski(k7_setfam_1(X1,X2),k7_setfam_1(X1,X3))=>r1_tarski(X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_setfam_1)).
% 0.88/1.08  fof(involutiveness_k7_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>k7_setfam_1(X1,k7_setfam_1(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k7_setfam_1)).
% 0.88/1.08  fof(dt_k7_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>m1_subset_1(k7_setfam_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_setfam_1)).
% 0.88/1.08  fof(t63_subset_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 0.88/1.08  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 0.88/1.08  fof(dt_k1_subset_1, axiom, ![X1]:m1_subset_1(k1_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_subset_1)).
% 0.88/1.08  fof(d3_subset_1, axiom, ![X1]:k1_subset_1(X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 0.88/1.08  fof(t46_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>~((X2!=k1_xboole_0&k7_setfam_1(X1,X2)=k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_setfam_1)).
% 0.88/1.08  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 0.88/1.08  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 0.88/1.08  fof(t49_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r2_hidden(k3_subset_1(X1,X3),k7_setfam_1(X1,X2))<=>r2_hidden(X3,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_setfam_1)).
% 0.88/1.08  fof(d6_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:(X9=k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)<=>![X10]:(r2_hidden(X10,X9)<=>~((((((((X10!=X1&X10!=X2)&X10!=X3)&X10!=X4)&X10!=X5)&X10!=X6)&X10!=X7)&X10!=X8)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_enumset1)).
% 0.88/1.08  fof(t1_zfmisc_1, axiom, k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_zfmisc_1)).
% 0.88/1.08  fof(t37_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_zfmisc_1)).
% 0.88/1.08  fof(t22_subset_1, axiom, ![X1]:k2_subset_1(X1)=k3_subset_1(X1,k1_subset_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_subset_1)).
% 0.88/1.08  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 0.88/1.08  fof(c_0_29, plain, ![X81, X82]:k1_setfam_1(k2_tarski(X81,X82))=k3_xboole_0(X81,X82), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.88/1.08  fof(c_0_30, plain, ![X16, X17]:k1_enumset1(X16,X16,X17)=k2_tarski(X16,X17), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.88/1.08  fof(c_0_31, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(X2=k1_tarski(X1)=>k7_setfam_1(X1,X2)=k1_tarski(k1_xboole_0)))), inference(assume_negation,[status(cth)],[t55_setfam_1])).
% 0.88/1.08  fof(c_0_32, plain, ![X12, X13]:k4_xboole_0(X12,X13)=k5_xboole_0(X12,k3_xboole_0(X12,X13)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.88/1.08  cnf(c_0_33, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.88/1.08  cnf(c_0_34, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.88/1.08  fof(c_0_35, plain, ![X47, X48]:((~r1_tarski(X47,k1_tarski(X48))|(X47=k1_xboole_0|X47=k1_tarski(X48)))&((X47!=k1_xboole_0|r1_tarski(X47,k1_tarski(X48)))&(X47!=k1_tarski(X48)|r1_tarski(X47,k1_tarski(X48))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t39_zfmisc_1])])])).
% 0.88/1.08  fof(c_0_36, plain, ![X15]:k2_tarski(X15,X15)=k1_tarski(X15), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.88/1.08  fof(c_0_37, plain, ![X18, X19, X20]:k2_enumset1(X18,X18,X19,X20)=k1_enumset1(X18,X19,X20), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.88/1.08  fof(c_0_38, plain, ![X21, X22, X23, X24]:k3_enumset1(X21,X21,X22,X23,X24)=k2_enumset1(X21,X22,X23,X24), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.88/1.08  fof(c_0_39, plain, ![X25, X26, X27, X28, X29]:k4_enumset1(X25,X25,X26,X27,X28,X29)=k3_enumset1(X25,X26,X27,X28,X29), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.88/1.08  fof(c_0_40, plain, ![X30, X31, X32, X33, X34, X35]:k5_enumset1(X30,X30,X31,X32,X33,X34,X35)=k4_enumset1(X30,X31,X32,X33,X34,X35), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.88/1.08  fof(c_0_41, plain, ![X36, X37, X38, X39, X40, X41, X42]:k6_enumset1(X36,X36,X37,X38,X39,X40,X41,X42)=k5_enumset1(X36,X37,X38,X39,X40,X41,X42), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.88/1.08  fof(c_0_42, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))&(esk3_0=k1_tarski(esk2_0)&k7_setfam_1(esk2_0,esk3_0)!=k1_tarski(k1_xboole_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_31])])])).
% 0.88/1.08  fof(c_0_43, plain, ![X43, X44]:((k4_xboole_0(k1_tarski(X43),k1_tarski(X44))!=k1_tarski(X43)|X43!=X44)&(X43=X44|k4_xboole_0(k1_tarski(X43),k1_tarski(X44))=k1_tarski(X43))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_zfmisc_1])])).
% 0.88/1.08  cnf(c_0_44, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.88/1.08  cnf(c_0_45, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_33, c_0_34])).
% 0.88/1.08  fof(c_0_46, plain, ![X11]:k3_xboole_0(X11,X11)=X11, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.88/1.08  cnf(c_0_47, plain, (X1=k1_xboole_0|X1=k1_tarski(X2)|~r1_tarski(X1,k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.88/1.08  cnf(c_0_48, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.88/1.08  cnf(c_0_49, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.88/1.08  cnf(c_0_50, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.88/1.08  cnf(c_0_51, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.88/1.08  cnf(c_0_52, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.88/1.08  cnf(c_0_53, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.88/1.08  cnf(c_0_54, negated_conjecture, (esk3_0=k1_tarski(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.88/1.08  fof(c_0_55, plain, ![X90, X91, X92]:(~m1_subset_1(X91,k1_zfmisc_1(k1_zfmisc_1(X90)))|(~m1_subset_1(X92,k1_zfmisc_1(k1_zfmisc_1(X90)))|(~r1_tarski(k7_setfam_1(X90,X91),k7_setfam_1(X90,X92))|r1_tarski(X91,X92)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t51_setfam_1])])])).
% 0.88/1.08  fof(c_0_56, plain, ![X79, X80]:(~m1_subset_1(X80,k1_zfmisc_1(k1_zfmisc_1(X79)))|k7_setfam_1(X79,k7_setfam_1(X79,X80))=X80), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k7_setfam_1])])).
% 0.88/1.08  fof(c_0_57, plain, ![X77, X78]:(~m1_subset_1(X78,k1_zfmisc_1(k1_zfmisc_1(X77)))|m1_subset_1(k7_setfam_1(X77,X78),k1_zfmisc_1(k1_zfmisc_1(X77)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_setfam_1])])).
% 0.88/1.08  fof(c_0_58, plain, ![X75, X76]:(~r2_hidden(X75,X76)|m1_subset_1(k1_tarski(X75),k1_zfmisc_1(X76))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_subset_1])])).
% 0.88/1.08  cnf(c_0_59, plain, (k4_xboole_0(k1_tarski(X1),k1_tarski(X2))!=k1_tarski(X1)|X1!=X2), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.88/1.08  cnf(c_0_60, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))), inference(rw,[status(thm)],[c_0_44, c_0_45])).
% 0.88/1.08  cnf(c_0_61, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.88/1.08  fof(c_0_62, plain, ![X14]:k5_xboole_0(X14,X14)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 0.88/1.08  fof(c_0_63, plain, ![X72]:m1_subset_1(k1_subset_1(X72),k1_zfmisc_1(X72)), inference(variable_rename,[status(thm)],[dt_k1_subset_1])).
% 0.88/1.08  fof(c_0_64, plain, ![X49]:k1_subset_1(X49)=k1_xboole_0, inference(variable_rename,[status(thm)],[d3_subset_1])).
% 0.88/1.08  cnf(c_0_65, plain, (X1=k1_xboole_0|X1=k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)|~r1_tarski(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_48]), c_0_48]), c_0_34]), c_0_34]), c_0_49]), c_0_49]), c_0_50]), c_0_50]), c_0_51]), c_0_51]), c_0_52]), c_0_52]), c_0_53]), c_0_53])).
% 0.88/1.08  cnf(c_0_66, negated_conjecture, (esk3_0=k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_48]), c_0_34]), c_0_49]), c_0_50]), c_0_51]), c_0_52]), c_0_53])).
% 0.88/1.08  cnf(c_0_67, plain, (r1_tarski(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))|~r1_tarski(k7_setfam_1(X2,X1),k7_setfam_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.88/1.08  cnf(c_0_68, plain, (k7_setfam_1(X2,k7_setfam_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.88/1.08  cnf(c_0_69, plain, (m1_subset_1(k7_setfam_1(X2,X1),k1_zfmisc_1(k1_zfmisc_1(X2)))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.88/1.08  fof(c_0_70, plain, ![X85, X86]:(~m1_subset_1(X86,k1_zfmisc_1(k1_zfmisc_1(X85)))|(X86=k1_xboole_0|k7_setfam_1(X85,X86)!=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t46_setfam_1])])).
% 0.88/1.08  cnf(c_0_71, plain, (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.88/1.08  cnf(c_0_72, plain, (X1!=X2|k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))))!=k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_48]), c_0_48]), c_0_48]), c_0_34]), c_0_34]), c_0_34]), c_0_60]), c_0_49]), c_0_49]), c_0_49]), c_0_49]), c_0_49]), c_0_49]), c_0_50]), c_0_50]), c_0_50]), c_0_50]), c_0_50]), c_0_50]), c_0_50]), c_0_51]), c_0_51]), c_0_51]), c_0_51]), c_0_51]), c_0_51]), c_0_51]), c_0_51]), c_0_52]), c_0_52]), c_0_52]), c_0_52]), c_0_52]), c_0_52]), c_0_52]), c_0_52]), c_0_52]), c_0_53]), c_0_53]), c_0_53]), c_0_53]), c_0_53]), c_0_53]), c_0_53]), c_0_53]), c_0_53]), c_0_53])).
% 0.88/1.08  cnf(c_0_73, plain, (k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_45]), c_0_49]), c_0_50]), c_0_51]), c_0_52]), c_0_53])).
% 0.88/1.08  cnf(c_0_74, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.88/1.08  fof(c_0_75, plain, ![X83, X84]:(~m1_subset_1(X83,X84)|(v1_xboole_0(X84)|r2_hidden(X83,X84))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.88/1.08  cnf(c_0_76, plain, (m1_subset_1(k1_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.88/1.08  cnf(c_0_77, plain, (k1_subset_1(X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.88/1.08  fof(c_0_78, plain, ![X73]:~v1_xboole_0(k1_zfmisc_1(X73)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 0.88/1.08  fof(c_0_79, plain, ![X87, X88, X89]:((~r2_hidden(k3_subset_1(X87,X89),k7_setfam_1(X87,X88))|r2_hidden(X89,X88)|~m1_subset_1(X89,k1_zfmisc_1(X87))|~m1_subset_1(X88,k1_zfmisc_1(k1_zfmisc_1(X87))))&(~r2_hidden(X89,X88)|r2_hidden(k3_subset_1(X87,X89),k7_setfam_1(X87,X88))|~m1_subset_1(X89,k1_zfmisc_1(X87))|~m1_subset_1(X88,k1_zfmisc_1(k1_zfmisc_1(X87))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t49_setfam_1])])])])).
% 0.88/1.08  fof(c_0_80, plain, ![X51, X52, X53, X54, X55, X56, X57, X58, X59, X60, X61, X62, X63, X64, X65, X66, X67, X68, X69, X70]:(((~r2_hidden(X60,X59)|(X60=X51|X60=X52|X60=X53|X60=X54|X60=X55|X60=X56|X60=X57|X60=X58)|X59!=k6_enumset1(X51,X52,X53,X54,X55,X56,X57,X58))&((((((((X61!=X51|r2_hidden(X61,X59)|X59!=k6_enumset1(X51,X52,X53,X54,X55,X56,X57,X58))&(X61!=X52|r2_hidden(X61,X59)|X59!=k6_enumset1(X51,X52,X53,X54,X55,X56,X57,X58)))&(X61!=X53|r2_hidden(X61,X59)|X59!=k6_enumset1(X51,X52,X53,X54,X55,X56,X57,X58)))&(X61!=X54|r2_hidden(X61,X59)|X59!=k6_enumset1(X51,X52,X53,X54,X55,X56,X57,X58)))&(X61!=X55|r2_hidden(X61,X59)|X59!=k6_enumset1(X51,X52,X53,X54,X55,X56,X57,X58)))&(X61!=X56|r2_hidden(X61,X59)|X59!=k6_enumset1(X51,X52,X53,X54,X55,X56,X57,X58)))&(X61!=X57|r2_hidden(X61,X59)|X59!=k6_enumset1(X51,X52,X53,X54,X55,X56,X57,X58)))&(X61!=X58|r2_hidden(X61,X59)|X59!=k6_enumset1(X51,X52,X53,X54,X55,X56,X57,X58))))&(((((((((esk1_9(X62,X63,X64,X65,X66,X67,X68,X69,X70)!=X62|~r2_hidden(esk1_9(X62,X63,X64,X65,X66,X67,X68,X69,X70),X70)|X70=k6_enumset1(X62,X63,X64,X65,X66,X67,X68,X69))&(esk1_9(X62,X63,X64,X65,X66,X67,X68,X69,X70)!=X63|~r2_hidden(esk1_9(X62,X63,X64,X65,X66,X67,X68,X69,X70),X70)|X70=k6_enumset1(X62,X63,X64,X65,X66,X67,X68,X69)))&(esk1_9(X62,X63,X64,X65,X66,X67,X68,X69,X70)!=X64|~r2_hidden(esk1_9(X62,X63,X64,X65,X66,X67,X68,X69,X70),X70)|X70=k6_enumset1(X62,X63,X64,X65,X66,X67,X68,X69)))&(esk1_9(X62,X63,X64,X65,X66,X67,X68,X69,X70)!=X65|~r2_hidden(esk1_9(X62,X63,X64,X65,X66,X67,X68,X69,X70),X70)|X70=k6_enumset1(X62,X63,X64,X65,X66,X67,X68,X69)))&(esk1_9(X62,X63,X64,X65,X66,X67,X68,X69,X70)!=X66|~r2_hidden(esk1_9(X62,X63,X64,X65,X66,X67,X68,X69,X70),X70)|X70=k6_enumset1(X62,X63,X64,X65,X66,X67,X68,X69)))&(esk1_9(X62,X63,X64,X65,X66,X67,X68,X69,X70)!=X67|~r2_hidden(esk1_9(X62,X63,X64,X65,X66,X67,X68,X69,X70),X70)|X70=k6_enumset1(X62,X63,X64,X65,X66,X67,X68,X69)))&(esk1_9(X62,X63,X64,X65,X66,X67,X68,X69,X70)!=X68|~r2_hidden(esk1_9(X62,X63,X64,X65,X66,X67,X68,X69,X70),X70)|X70=k6_enumset1(X62,X63,X64,X65,X66,X67,X68,X69)))&(esk1_9(X62,X63,X64,X65,X66,X67,X68,X69,X70)!=X69|~r2_hidden(esk1_9(X62,X63,X64,X65,X66,X67,X68,X69,X70),X70)|X70=k6_enumset1(X62,X63,X64,X65,X66,X67,X68,X69)))&(r2_hidden(esk1_9(X62,X63,X64,X65,X66,X67,X68,X69,X70),X70)|(esk1_9(X62,X63,X64,X65,X66,X67,X68,X69,X70)=X62|esk1_9(X62,X63,X64,X65,X66,X67,X68,X69,X70)=X63|esk1_9(X62,X63,X64,X65,X66,X67,X68,X69,X70)=X64|esk1_9(X62,X63,X64,X65,X66,X67,X68,X69,X70)=X65|esk1_9(X62,X63,X64,X65,X66,X67,X68,X69,X70)=X66|esk1_9(X62,X63,X64,X65,X66,X67,X68,X69,X70)=X67|esk1_9(X62,X63,X64,X65,X66,X67,X68,X69,X70)=X68|esk1_9(X62,X63,X64,X65,X66,X67,X68,X69,X70)=X69)|X70=k6_enumset1(X62,X63,X64,X65,X66,X67,X68,X69)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_enumset1])])])])])])).
% 0.88/1.08  cnf(c_0_81, negated_conjecture, (X1=k1_xboole_0|X1=esk3_0|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.88/1.08  cnf(c_0_82, plain, (r1_tarski(k7_setfam_1(X1,X2),X3)|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))|~r1_tarski(X2,k7_setfam_1(X1,X3))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_69])).
% 0.88/1.08  cnf(c_0_83, plain, (k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(split_conjunct,[status(thm)],[t1_zfmisc_1])).
% 0.88/1.08  cnf(c_0_84, plain, (X1=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))|k7_setfam_1(X2,X1)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.88/1.08  cnf(c_0_85, plain, (m1_subset_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_zfmisc_1(X2))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71, c_0_48]), c_0_34]), c_0_49]), c_0_50]), c_0_51]), c_0_52]), c_0_53])).
% 0.88/1.08  cnf(c_0_86, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_72]), c_0_73]), c_0_74])).
% 0.88/1.08  cnf(c_0_87, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.88/1.08  cnf(c_0_88, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_76, c_0_77])).
% 0.88/1.08  cnf(c_0_89, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_78])).
% 0.88/1.08  fof(c_0_90, plain, ![X45, X46]:((~r1_tarski(k1_tarski(X45),X46)|r2_hidden(X45,X46))&(~r2_hidden(X45,X46)|r1_tarski(k1_tarski(X45),X46))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_zfmisc_1])])).
% 0.88/1.08  cnf(c_0_91, plain, (r2_hidden(X2,X3)|~r2_hidden(k3_subset_1(X1,X2),k7_setfam_1(X1,X3))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_79])).
% 0.88/1.08  fof(c_0_92, plain, ![X74]:k2_subset_1(X74)=k3_subset_1(X74,k1_subset_1(X74)), inference(variable_rename,[status(thm)],[t22_subset_1])).
% 0.88/1.08  fof(c_0_93, plain, ![X50]:k2_subset_1(X50)=X50, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.88/1.08  cnf(c_0_94, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k6_enumset1(X4,X5,X6,X7,X8,X9,X10,X2)), inference(split_conjunct,[status(thm)],[c_0_80])).
% 0.88/1.08  cnf(c_0_95, negated_conjecture, (k7_setfam_1(X1,X2)=esk3_0|k7_setfam_1(X1,X2)=k1_xboole_0|~m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(X1)))|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))|~r1_tarski(X2,k7_setfam_1(X1,esk3_0))), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 0.88/1.08  cnf(c_0_96, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.88/1.08  cnf(c_0_97, plain, (k1_zfmisc_1(k1_xboole_0)=k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_83, c_0_48]), c_0_34]), c_0_49]), c_0_50]), c_0_51]), c_0_52]), c_0_53])).
% 0.88/1.08  cnf(c_0_98, plain, (k7_setfam_1(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))!=k1_xboole_0|~r2_hidden(X2,k1_zfmisc_1(X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_86])).
% 0.88/1.08  cnf(c_0_99, plain, (r2_hidden(k1_xboole_0,k1_zfmisc_1(X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_89])).
% 0.88/1.08  cnf(c_0_100, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_90])).
% 0.88/1.08  cnf(c_0_101, plain, (r2_hidden(X1,k7_setfam_1(X2,X3))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(k3_subset_1(X2,X1),X3)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_68]), c_0_69])).
% 0.88/1.08  cnf(c_0_102, plain, (k2_subset_1(X1)=k3_subset_1(X1,k1_subset_1(X1))), inference(split_conjunct,[status(thm)],[c_0_92])).
% 0.88/1.08  cnf(c_0_103, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_93])).
% 0.88/1.08  cnf(c_0_104, plain, (r2_hidden(X1,k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_94])])).
% 0.88/1.08  cnf(c_0_105, negated_conjecture, (k7_setfam_1(esk2_0,X1)=k1_xboole_0|k7_setfam_1(esk2_0,X1)=esk3_0|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))|~r1_tarski(X1,k7_setfam_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_95, c_0_96])).
% 0.88/1.08  cnf(c_0_106, plain, (m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(X1))|~r2_hidden(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_85, c_0_97])).
% 0.88/1.08  cnf(c_0_107, plain, (k7_setfam_1(X1,k1_zfmisc_1(k1_xboole_0))!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_97]), c_0_99])])).
% 0.88/1.08  cnf(c_0_108, plain, (r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_100, c_0_48]), c_0_34]), c_0_49]), c_0_50]), c_0_51]), c_0_52]), c_0_53])).
% 0.88/1.08  cnf(c_0_109, negated_conjecture, (r2_hidden(X1,k7_setfam_1(esk2_0,esk3_0))|~m1_subset_1(X1,k1_zfmisc_1(esk2_0))|~r2_hidden(k3_subset_1(esk2_0,X1),esk3_0)), inference(spm,[status(thm)],[c_0_101, c_0_96])).
% 0.88/1.08  cnf(c_0_110, plain, (X1=k3_subset_1(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_102, c_0_103]), c_0_77])).
% 0.88/1.08  cnf(c_0_111, negated_conjecture, (r2_hidden(esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_104, c_0_66])).
% 0.88/1.08  cnf(c_0_112, negated_conjecture, (k7_setfam_1(esk2_0,esk3_0)!=k1_tarski(k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.88/1.08  cnf(c_0_113, negated_conjecture, (k7_setfam_1(esk2_0,k1_zfmisc_1(k1_xboole_0))=esk3_0|~r1_tarski(k1_zfmisc_1(k1_xboole_0),k7_setfam_1(esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_106]), c_0_99])]), c_0_107])).
% 0.88/1.08  cnf(c_0_114, plain, (r1_tarski(k1_zfmisc_1(k1_xboole_0),X1)|~r2_hidden(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_108, c_0_97])).
% 0.88/1.08  cnf(c_0_115, negated_conjecture, (r2_hidden(k1_xboole_0,k7_setfam_1(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_110]), c_0_88]), c_0_111])])).
% 0.88/1.08  cnf(c_0_116, negated_conjecture, (k7_setfam_1(esk2_0,esk3_0)!=k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_112, c_0_48]), c_0_34]), c_0_49]), c_0_50]), c_0_51]), c_0_52]), c_0_53])).
% 0.88/1.08  cnf(c_0_117, negated_conjecture, (k7_setfam_1(esk2_0,k1_zfmisc_1(k1_xboole_0))=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_114]), c_0_115])])).
% 0.88/1.08  cnf(c_0_118, negated_conjecture, (k7_setfam_1(esk2_0,esk3_0)!=k1_zfmisc_1(k1_xboole_0)), inference(rw,[status(thm)],[c_0_116, c_0_97])).
% 0.88/1.08  cnf(c_0_119, negated_conjecture, (~m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(esk2_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_117]), c_0_118])).
% 0.88/1.08  cnf(c_0_120, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119, c_0_106]), c_0_99])]), ['proof']).
% 0.88/1.08  # SZS output end CNFRefutation
% 0.88/1.08  # Proof object total steps             : 121
% 0.88/1.08  # Proof object clause steps            : 63
% 0.88/1.08  # Proof object formula steps           : 58
% 0.88/1.08  # Proof object conjectures             : 19
% 0.88/1.08  # Proof object clause conjectures      : 16
% 0.88/1.08  # Proof object formula conjectures     : 3
% 0.88/1.08  # Proof object initial clauses used    : 31
% 0.88/1.08  # Proof object initial formulas used   : 29
% 0.88/1.08  # Proof object generating inferences   : 17
% 0.88/1.08  # Proof object simplifying inferences  : 130
% 0.88/1.08  # Training examples: 0 positive, 0 negative
% 0.88/1.08  # Parsed axioms                        : 29
% 0.88/1.08  # Removed by relevancy pruning/SinE    : 0
% 0.88/1.08  # Initial clauses                      : 53
% 0.88/1.08  # Removed in clause preprocessing      : 11
% 0.88/1.08  # Initial clauses in saturation        : 42
% 0.88/1.08  # Processed clauses                    : 3786
% 0.88/1.08  # ...of these trivial                  : 9
% 0.88/1.08  # ...subsumed                          : 2993
% 0.88/1.08  # ...remaining for further processing  : 784
% 0.88/1.08  # Other redundant clauses eliminated   : 2867
% 0.88/1.08  # Clauses deleted for lack of memory   : 0
% 0.88/1.08  # Backward-subsumed                    : 36
% 0.88/1.08  # Backward-rewritten                   : 29
% 0.88/1.08  # Generated clauses                    : 19930
% 0.88/1.08  # ...of the previous two non-trivial   : 11932
% 0.88/1.08  # Contextual simplify-reflections      : 23
% 0.88/1.08  # Paramodulations                      : 8629
% 0.88/1.08  # Factorizations                       : 8442
% 0.88/1.08  # Equation resolutions                 : 2867
% 0.88/1.08  # Propositional unsat checks           : 0
% 0.88/1.08  #    Propositional check models        : 0
% 0.88/1.08  #    Propositional check unsatisfiable : 0
% 0.88/1.08  #    Propositional clauses             : 0
% 0.88/1.08  #    Propositional clauses after purity: 0
% 0.88/1.08  #    Propositional unsat core size     : 0
% 0.88/1.08  #    Propositional preprocessing time  : 0.000
% 0.88/1.08  #    Propositional encoding time       : 0.000
% 0.88/1.08  #    Propositional solver time         : 0.000
% 0.88/1.08  #    Success case prop preproc time    : 0.000
% 0.88/1.08  #    Success case prop encoding time   : 0.000
% 0.88/1.08  #    Success case prop solver time     : 0.000
% 0.88/1.08  # Current number of processed clauses  : 665
% 0.88/1.08  #    Positive orientable unit clauses  : 34
% 0.88/1.08  #    Positive unorientable unit clauses: 0
% 0.88/1.08  #    Negative unit clauses             : 18
% 0.88/1.08  #    Non-unit-clauses                  : 613
% 0.88/1.08  # Current number of unprocessed clauses: 8168
% 0.88/1.08  # ...number of literals in the above   : 63539
% 0.88/1.08  # Current number of archived formulas  : 0
% 0.88/1.08  # Current number of archived clauses   : 118
% 0.88/1.08  # Clause-clause subsumption calls (NU) : 130148
% 0.88/1.08  # Rec. Clause-clause subsumption calls : 27251
% 0.88/1.08  # Non-unit clause-clause subsumptions  : 2784
% 0.88/1.08  # Unit Clause-clause subsumption calls : 1718
% 0.88/1.08  # Rewrite failures with RHS unbound    : 0
% 0.88/1.08  # BW rewrite match attempts            : 79
% 0.88/1.08  # BW rewrite match successes           : 7
% 0.88/1.08  # Condensation attempts                : 0
% 0.88/1.08  # Condensation successes               : 0
% 0.88/1.08  # Termbank termtop insertions          : 242628
% 0.88/1.08  
% 0.88/1.08  # -------------------------------------------------
% 0.88/1.08  # User time                : 0.722 s
% 0.88/1.08  # System time              : 0.010 s
% 0.88/1.08  # Total time               : 0.732 s
% 0.88/1.08  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
