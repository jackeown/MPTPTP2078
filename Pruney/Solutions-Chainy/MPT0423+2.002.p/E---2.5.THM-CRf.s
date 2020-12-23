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
% DateTime   : Thu Dec  3 10:47:45 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :  139 (1236 expanded)
%              Number of clauses        :   75 ( 472 expanded)
%              Number of leaves         :   32 ( 382 expanded)
%              Depth                    :   15
%              Number of atoms          :  294 (1551 expanded)
%              Number of equality atoms :  141 (1228 expanded)
%              Maximal formula depth    :   14 (   3 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

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

fof(t38_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( r1_tarski(X2,k3_subset_1(X1,X2))
      <=> X2 = k1_subset_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).

fof(d3_subset_1,axiom,(
    ! [X1] : k1_subset_1(X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

fof(t22_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = k3_subset_1(X1,k1_subset_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(dt_k1_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_subset_1)).

fof(t55_setfam_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( X2 = k1_tarski(X1)
       => k7_setfam_1(X1,X2) = k1_tarski(k1_xboole_0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_setfam_1)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(d8_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
         => ( X3 = k7_setfam_1(X1,X2)
          <=> ! [X4] :
                ( m1_subset_1(X4,k1_zfmisc_1(X1))
               => ( r2_hidden(X4,X3)
                <=> r2_hidden(k3_subset_1(X1,X4),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_setfam_1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(dt_k7_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => m1_subset_1(k7_setfam_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_setfam_1)).

fof(involutiveness_k7_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => k7_setfam_1(X1,k7_setfam_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(t63_subset_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(t1_zfmisc_1,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).

fof(t51_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
         => ( r1_tarski(k7_setfam_1(X1,X2),k7_setfam_1(X1,X3))
           => r1_tarski(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_setfam_1)).

fof(l3_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,k1_tarski(X2))
    <=> ( X1 = k1_xboole_0
        | X1 = k1_tarski(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t46_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ~ ( X2 != k1_xboole_0
          & k7_setfam_1(X1,X2) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_setfam_1)).

fof(c_0_32,plain,(
    ! [X81,X82] : k1_setfam_1(k2_tarski(X81,X82)) = k3_xboole_0(X81,X82) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_33,plain,(
    ! [X22,X23] : k1_enumset1(X22,X22,X23) = k2_tarski(X22,X23) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_34,plain,(
    ! [X11,X12] : k4_xboole_0(X11,X12) = k5_xboole_0(X11,k3_xboole_0(X11,X12)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_35,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_36,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_37,plain,(
    ! [X14,X15,X16,X17,X18,X19] :
      ( ( ~ r2_hidden(X16,X15)
        | X16 = X14
        | X15 != k1_tarski(X14) )
      & ( X17 != X14
        | r2_hidden(X17,X15)
        | X15 != k1_tarski(X14) )
      & ( ~ r2_hidden(esk2_2(X18,X19),X19)
        | esk2_2(X18,X19) != X18
        | X19 = k1_tarski(X18) )
      & ( r2_hidden(esk2_2(X18,X19),X19)
        | esk2_2(X18,X19) = X18
        | X19 = k1_tarski(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_38,plain,(
    ! [X21] : k2_tarski(X21,X21) = k1_tarski(X21) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_39,plain,(
    ! [X24,X25,X26] : k2_enumset1(X24,X24,X25,X26) = k1_enumset1(X24,X25,X26) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_40,plain,(
    ! [X27,X28,X29,X30] : k3_enumset1(X27,X27,X28,X29,X30) = k2_enumset1(X27,X28,X29,X30) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_41,plain,(
    ! [X31,X32,X33,X34,X35] : k4_enumset1(X31,X31,X32,X33,X34,X35) = k3_enumset1(X31,X32,X33,X34,X35) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_42,plain,(
    ! [X36,X37,X38,X39,X40,X41] : k5_enumset1(X36,X36,X37,X38,X39,X40,X41) = k4_enumset1(X36,X37,X38,X39,X40,X41) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_43,plain,(
    ! [X42,X43,X44,X45,X46,X47,X48] : k6_enumset1(X42,X42,X43,X44,X45,X46,X47,X48) = k5_enumset1(X42,X43,X44,X45,X46,X47,X48) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_44,plain,(
    ! [X58,X59] :
      ( ( k4_xboole_0(k1_tarski(X58),k1_tarski(X59)) != k1_tarski(X58)
        | X58 != X59 )
      & ( X58 = X59
        | k4_xboole_0(k1_tarski(X58),k1_tarski(X59)) = k1_tarski(X58) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_zfmisc_1])])).

cnf(c_0_45,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_46,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_35,c_0_36])).

fof(c_0_47,plain,(
    ! [X8] : k3_xboole_0(X8,X8) = X8 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

fof(c_0_48,plain,(
    ! [X66,X67] :
      ( ( ~ r1_tarski(X67,k3_subset_1(X66,X67))
        | X67 = k1_subset_1(X66)
        | ~ m1_subset_1(X67,k1_zfmisc_1(X66)) )
      & ( X67 != k1_subset_1(X66)
        | r1_tarski(X67,k3_subset_1(X66,X67))
        | ~ m1_subset_1(X67,k1_zfmisc_1(X66)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_subset_1])])])).

fof(c_0_49,plain,(
    ! [X60] : k1_subset_1(X60) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[d3_subset_1])).

fof(c_0_50,plain,(
    ! [X65] : k2_subset_1(X65) = k3_subset_1(X65,k1_subset_1(X65)) ),
    inference(variable_rename,[status(thm)],[t22_subset_1])).

fof(c_0_51,plain,(
    ! [X61] : k2_subset_1(X61) = X61 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

fof(c_0_52,plain,(
    ! [X62] : m1_subset_1(k1_subset_1(X62),k1_zfmisc_1(X62)) ),
    inference(variable_rename,[status(thm)],[dt_k1_subset_1])).

fof(c_0_53,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
       => ( X2 = k1_tarski(X1)
         => k7_setfam_1(X1,X2) = k1_tarski(k1_xboole_0) ) ) ),
    inference(assume_negation,[status(cth)],[t55_setfam_1])).

cnf(c_0_54,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_55,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_56,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_57,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_58,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_59,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_60,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_61,plain,
    ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) != k1_tarski(X1)
    | X1 != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_62,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_63,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

fof(c_0_64,plain,(
    ! [X13] : k5_xboole_0(X13,X13) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

fof(c_0_65,plain,(
    ! [X49,X50,X51,X52,X53,X54] :
      ( ( ~ r2_hidden(X51,X50)
        | r1_tarski(X51,X49)
        | X50 != k1_zfmisc_1(X49) )
      & ( ~ r1_tarski(X52,X49)
        | r2_hidden(X52,X50)
        | X50 != k1_zfmisc_1(X49) )
      & ( ~ r2_hidden(esk3_2(X53,X54),X54)
        | ~ r1_tarski(esk3_2(X53,X54),X53)
        | X54 = k1_zfmisc_1(X53) )
      & ( r2_hidden(esk3_2(X53,X54),X54)
        | r1_tarski(esk3_2(X53,X54),X53)
        | X54 = k1_zfmisc_1(X53) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

cnf(c_0_66,plain,
    ( r1_tarski(X1,k3_subset_1(X2,X1))
    | X1 != k1_subset_1(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_67,plain,
    ( k1_subset_1(X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_68,plain,
    ( k2_subset_1(X1) = k3_subset_1(X1,k1_subset_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_69,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_70,plain,
    ( m1_subset_1(k1_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

fof(c_0_71,plain,(
    ! [X72,X73,X74,X75] :
      ( ( ~ r2_hidden(X75,X74)
        | r2_hidden(k3_subset_1(X72,X75),X73)
        | ~ m1_subset_1(X75,k1_zfmisc_1(X72))
        | X74 != k7_setfam_1(X72,X73)
        | ~ m1_subset_1(X74,k1_zfmisc_1(k1_zfmisc_1(X72)))
        | ~ m1_subset_1(X73,k1_zfmisc_1(k1_zfmisc_1(X72))) )
      & ( ~ r2_hidden(k3_subset_1(X72,X75),X73)
        | r2_hidden(X75,X74)
        | ~ m1_subset_1(X75,k1_zfmisc_1(X72))
        | X74 != k7_setfam_1(X72,X73)
        | ~ m1_subset_1(X74,k1_zfmisc_1(k1_zfmisc_1(X72)))
        | ~ m1_subset_1(X73,k1_zfmisc_1(k1_zfmisc_1(X72))) )
      & ( m1_subset_1(esk4_3(X72,X73,X74),k1_zfmisc_1(X72))
        | X74 = k7_setfam_1(X72,X73)
        | ~ m1_subset_1(X74,k1_zfmisc_1(k1_zfmisc_1(X72)))
        | ~ m1_subset_1(X73,k1_zfmisc_1(k1_zfmisc_1(X72))) )
      & ( ~ r2_hidden(esk4_3(X72,X73,X74),X74)
        | ~ r2_hidden(k3_subset_1(X72,esk4_3(X72,X73,X74)),X73)
        | X74 = k7_setfam_1(X72,X73)
        | ~ m1_subset_1(X74,k1_zfmisc_1(k1_zfmisc_1(X72)))
        | ~ m1_subset_1(X73,k1_zfmisc_1(k1_zfmisc_1(X72))) )
      & ( r2_hidden(esk4_3(X72,X73,X74),X74)
        | r2_hidden(k3_subset_1(X72,esk4_3(X72,X73,X74)),X73)
        | X74 = k7_setfam_1(X72,X73)
        | ~ m1_subset_1(X74,k1_zfmisc_1(k1_zfmisc_1(X72)))
        | ~ m1_subset_1(X73,k1_zfmisc_1(k1_zfmisc_1(X72))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_setfam_1])])])])])).

fof(c_0_72,plain,(
    ! [X89,X90,X91] :
      ( ~ r2_hidden(X89,X90)
      | ~ m1_subset_1(X90,k1_zfmisc_1(X91))
      | m1_subset_1(X89,X91) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_73,plain,(
    ! [X77,X78] :
      ( ~ m1_subset_1(X78,k1_zfmisc_1(k1_zfmisc_1(X77)))
      | m1_subset_1(k7_setfam_1(X77,X78),k1_zfmisc_1(k1_zfmisc_1(X77))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_setfam_1])])).

fof(c_0_74,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k1_zfmisc_1(esk5_0)))
    & esk6_0 = k1_tarski(esk5_0)
    & k7_setfam_1(esk5_0,esk6_0) != k1_tarski(k1_xboole_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_53])])])).

fof(c_0_75,plain,(
    ! [X79,X80] :
      ( ~ m1_subset_1(X80,k1_zfmisc_1(k1_zfmisc_1(X79)))
      | k7_setfam_1(X79,k7_setfam_1(X79,X80)) = X80 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k7_setfam_1])])).

cnf(c_0_76,plain,
    ( X1 = X3
    | X2 != k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_55]),c_0_36]),c_0_56]),c_0_57]),c_0_58]),c_0_59]),c_0_60])).

fof(c_0_77,plain,(
    ! [X9] :
      ( X9 = k1_xboole_0
      | r2_hidden(esk1_1(X9),X9) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_78,plain,
    ( X1 != X2
    | k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)))) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_55]),c_0_55]),c_0_55]),c_0_36]),c_0_36]),c_0_36]),c_0_62]),c_0_56]),c_0_56]),c_0_56]),c_0_56]),c_0_56]),c_0_56]),c_0_57]),c_0_57]),c_0_57]),c_0_57]),c_0_57]),c_0_57]),c_0_57]),c_0_58]),c_0_58]),c_0_58]),c_0_58]),c_0_58]),c_0_58]),c_0_58]),c_0_58]),c_0_59]),c_0_59]),c_0_59]),c_0_59]),c_0_59]),c_0_59]),c_0_59]),c_0_59]),c_0_59]),c_0_60]),c_0_60]),c_0_60]),c_0_60]),c_0_60]),c_0_60]),c_0_60]),c_0_60]),c_0_60]),c_0_60])).

cnf(c_0_79,plain,
    ( k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_46]),c_0_56]),c_0_57]),c_0_58]),c_0_59]),c_0_60])).

cnf(c_0_80,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

fof(c_0_81,plain,(
    ! [X70,X71] :
      ( ~ r2_hidden(X70,X71)
      | m1_subset_1(k1_tarski(X70),k1_zfmisc_1(X71)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_subset_1])])).

cnf(c_0_82,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_83,plain,
    ( r1_tarski(X1,k3_subset_1(X2,X1))
    | X1 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_84,plain,
    ( X1 = k3_subset_1(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_69]),c_0_67])).

cnf(c_0_85,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_70,c_0_67])).

cnf(c_0_86,plain,
    ( r2_hidden(k3_subset_1(X3,X1),X4)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | X2 != k7_setfam_1(X3,X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_87,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_88,plain,
    ( m1_subset_1(k7_setfam_1(X2,X1),k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_89,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k1_zfmisc_1(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_90,plain,
    ( k7_setfam_1(X2,k7_setfam_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_91,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_76])).

cnf(c_0_92,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_93,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_78]),c_0_79]),c_0_80])).

cnf(c_0_94,negated_conjecture,
    ( esk6_0 = k1_tarski(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

fof(c_0_95,plain,(
    ! [X63,X64] :
      ( ~ m1_subset_1(X64,k1_zfmisc_1(X63))
      | k3_subset_1(X63,k3_subset_1(X63,X64)) = X64 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

cnf(c_0_96,plain,
    ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_97,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_82])).

cnf(c_0_98,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_83]),c_0_84]),c_0_85])])).

cnf(c_0_99,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[t1_zfmisc_1])).

cnf(c_0_100,plain,
    ( r2_hidden(k3_subset_1(X1,X2),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ r2_hidden(X2,k7_setfam_1(X1,X3)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_86,c_0_87])]),c_0_88])).

cnf(c_0_101,negated_conjecture,
    ( m1_subset_1(k7_setfam_1(esk5_0,esk6_0),k1_zfmisc_1(k1_zfmisc_1(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_102,negated_conjecture,
    ( k7_setfam_1(esk5_0,k7_setfam_1(esk5_0,esk6_0)) = esk6_0 ),
    inference(spm,[status(thm)],[c_0_90,c_0_89])).

cnf(c_0_103,plain,
    ( esk1_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = X1 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_93])).

cnf(c_0_104,negated_conjecture,
    ( esk6_0 = k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_94,c_0_55]),c_0_36]),c_0_56]),c_0_57]),c_0_58]),c_0_59]),c_0_60])).

cnf(c_0_105,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_95])).

fof(c_0_106,plain,(
    ! [X92,X93,X94] :
      ( ~ m1_subset_1(X93,k1_zfmisc_1(k1_zfmisc_1(X92)))
      | ~ m1_subset_1(X94,k1_zfmisc_1(k1_zfmisc_1(X92)))
      | ~ r1_tarski(k7_setfam_1(X92,X93),k7_setfam_1(X92,X94))
      | r1_tarski(X93,X94) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t51_setfam_1])])])).

cnf(c_0_107,plain,
    ( m1_subset_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_96,c_0_55]),c_0_36]),c_0_56]),c_0_57]),c_0_58]),c_0_59]),c_0_60])).

cnf(c_0_108,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_97,c_0_98])).

cnf(c_0_109,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_99,c_0_55]),c_0_36]),c_0_56]),c_0_57]),c_0_58]),c_0_59]),c_0_60])).

cnf(c_0_110,negated_conjecture,
    ( r2_hidden(k3_subset_1(esk5_0,X1),k7_setfam_1(esk5_0,esk6_0))
    | ~ r2_hidden(X1,esk6_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_101]),c_0_102])).

cnf(c_0_111,negated_conjecture,
    ( esk1_1(esk6_0) = esk5_0 ),
    inference(spm,[status(thm)],[c_0_103,c_0_104])).

cnf(c_0_112,plain,
    ( k3_subset_1(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_85]),c_0_84])).

cnf(c_0_113,negated_conjecture,
    ( esk6_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_93,c_0_104])).

fof(c_0_114,plain,(
    ! [X56,X57] :
      ( ( ~ r1_tarski(X56,k1_tarski(X57))
        | X56 = k1_xboole_0
        | X56 = k1_tarski(X57) )
      & ( X56 != k1_xboole_0
        | r1_tarski(X56,k1_tarski(X57)) )
      & ( X56 != k1_tarski(X57)
        | r1_tarski(X56,k1_tarski(X57)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).

cnf(c_0_115,plain,
    ( r1_tarski(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ r1_tarski(k7_setfam_1(X2,X1),k7_setfam_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_106])).

cnf(c_0_116,plain,
    ( m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_108]),c_0_109])).

fof(c_0_117,plain,(
    ! [X85,X86] :
      ( ( ~ m1_subset_1(X85,k1_zfmisc_1(X86))
        | r1_tarski(X85,X86) )
      & ( ~ r1_tarski(X85,X86)
        | m1_subset_1(X85,k1_zfmisc_1(X86)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_118,negated_conjecture,
    ( r2_hidden(k1_xboole_0,k7_setfam_1(esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_92]),c_0_111]),c_0_112]),c_0_113])).

cnf(c_0_119,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_tarski(X2)
    | ~ r1_tarski(X1,k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_114])).

cnf(c_0_120,negated_conjecture,
    ( r1_tarski(X1,esk6_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(esk5_0)))
    | ~ r1_tarski(k7_setfam_1(esk5_0,X1),k7_setfam_1(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_115,c_0_89])).

cnf(c_0_121,plain,
    ( m1_subset_1(k7_setfam_1(X1,k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_88,c_0_116])).

cnf(c_0_122,plain,
    ( k7_setfam_1(X1,k7_setfam_1(X1,k1_zfmisc_1(k1_xboole_0))) = k1_zfmisc_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_90,c_0_116])).

cnf(c_0_123,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_117])).

cnf(c_0_124,negated_conjecture,
    ( m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k7_setfam_1(esk5_0,esk6_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_118]),c_0_109])).

cnf(c_0_125,plain,
    ( X1 = k1_xboole_0
    | X1 = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)
    | ~ r1_tarski(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_119,c_0_55]),c_0_55]),c_0_36]),c_0_36]),c_0_56]),c_0_56]),c_0_57]),c_0_57]),c_0_58]),c_0_58]),c_0_59]),c_0_59]),c_0_60]),c_0_60])).

cnf(c_0_126,negated_conjecture,
    ( r1_tarski(k7_setfam_1(esk5_0,k1_zfmisc_1(k1_xboole_0)),esk6_0)
    | ~ r1_tarski(k1_zfmisc_1(k1_xboole_0),k7_setfam_1(esk5_0,esk6_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_121]),c_0_122])).

cnf(c_0_127,negated_conjecture,
    ( r1_tarski(k1_zfmisc_1(k1_xboole_0),k7_setfam_1(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_123,c_0_124])).

cnf(c_0_128,negated_conjecture,
    ( k7_setfam_1(esk5_0,esk6_0) != k1_tarski(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_129,negated_conjecture,
    ( X1 = k1_xboole_0
    | X1 = esk6_0
    | ~ r1_tarski(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_125,c_0_104])).

cnf(c_0_130,negated_conjecture,
    ( r1_tarski(k7_setfam_1(esk5_0,k1_zfmisc_1(k1_xboole_0)),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_126,c_0_127])])).

cnf(c_0_131,negated_conjecture,
    ( k7_setfam_1(esk5_0,esk6_0) != k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_128,c_0_55]),c_0_36]),c_0_56]),c_0_57]),c_0_58]),c_0_59]),c_0_60])).

fof(c_0_132,plain,(
    ! [X87,X88] :
      ( ~ m1_subset_1(X88,k1_zfmisc_1(k1_zfmisc_1(X87)))
      | X88 = k1_xboole_0
      | k7_setfam_1(X87,X88) != k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t46_setfam_1])])).

cnf(c_0_133,negated_conjecture,
    ( k7_setfam_1(esk5_0,k1_zfmisc_1(k1_xboole_0)) = esk6_0
    | k7_setfam_1(esk5_0,k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_129,c_0_130])).

cnf(c_0_134,negated_conjecture,
    ( k7_setfam_1(esk5_0,esk6_0) != k1_zfmisc_1(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_131,c_0_109])).

cnf(c_0_135,plain,
    ( X1 = k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | k7_setfam_1(X2,X1) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_132])).

cnf(c_0_136,negated_conjecture,
    ( k7_setfam_1(esk5_0,k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_122,c_0_133]),c_0_134])).

cnf(c_0_137,plain,
    ( k1_zfmisc_1(k1_xboole_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_93,c_0_109])).

cnf(c_0_138,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_136]),c_0_116])]),c_0_137]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:34:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_S2mI
% 0.12/0.39  # and selection function SelectCQArNTNpEqFirst.
% 0.12/0.39  #
% 0.12/0.39  # Preprocessing time       : 0.029 s
% 0.12/0.39  # Presaturation interreduction done
% 0.12/0.39  
% 0.12/0.39  # Proof found!
% 0.12/0.39  # SZS status Theorem
% 0.12/0.39  # SZS output start CNFRefutation
% 0.12/0.39  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.12/0.39  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.12/0.39  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.12/0.39  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 0.12/0.39  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.12/0.39  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.12/0.39  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.12/0.39  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.12/0.39  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.12/0.39  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.12/0.39  fof(t20_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)<=>X1!=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 0.12/0.39  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.12/0.39  fof(t38_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(r1_tarski(X2,k3_subset_1(X1,X2))<=>X2=k1_subset_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_subset_1)).
% 0.12/0.39  fof(d3_subset_1, axiom, ![X1]:k1_subset_1(X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 0.12/0.39  fof(t22_subset_1, axiom, ![X1]:k2_subset_1(X1)=k3_subset_1(X1,k1_subset_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_subset_1)).
% 0.12/0.39  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 0.12/0.39  fof(dt_k1_subset_1, axiom, ![X1]:m1_subset_1(k1_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_subset_1)).
% 0.12/0.39  fof(t55_setfam_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(X2=k1_tarski(X1)=>k7_setfam_1(X1,X2)=k1_tarski(k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_setfam_1)).
% 0.12/0.39  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 0.12/0.39  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.12/0.39  fof(d8_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(X3=k7_setfam_1(X1,X2)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(X1))=>(r2_hidden(X4,X3)<=>r2_hidden(k3_subset_1(X1,X4),X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_setfam_1)).
% 0.12/0.39  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 0.12/0.39  fof(dt_k7_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>m1_subset_1(k7_setfam_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_setfam_1)).
% 0.12/0.39  fof(involutiveness_k7_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>k7_setfam_1(X1,k7_setfam_1(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k7_setfam_1)).
% 0.12/0.39  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.12/0.39  fof(t63_subset_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 0.12/0.39  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 0.12/0.39  fof(t1_zfmisc_1, axiom, k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_zfmisc_1)).
% 0.12/0.39  fof(t51_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(r1_tarski(k7_setfam_1(X1,X2),k7_setfam_1(X1,X3))=>r1_tarski(X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_setfam_1)).
% 0.12/0.39  fof(l3_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,k1_tarski(X2))<=>(X1=k1_xboole_0|X1=k1_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 0.12/0.39  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.12/0.39  fof(t46_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>~((X2!=k1_xboole_0&k7_setfam_1(X1,X2)=k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_setfam_1)).
% 0.12/0.39  fof(c_0_32, plain, ![X81, X82]:k1_setfam_1(k2_tarski(X81,X82))=k3_xboole_0(X81,X82), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.12/0.39  fof(c_0_33, plain, ![X22, X23]:k1_enumset1(X22,X22,X23)=k2_tarski(X22,X23), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.12/0.39  fof(c_0_34, plain, ![X11, X12]:k4_xboole_0(X11,X12)=k5_xboole_0(X11,k3_xboole_0(X11,X12)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.12/0.39  cnf(c_0_35, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.12/0.39  cnf(c_0_36, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.12/0.39  fof(c_0_37, plain, ![X14, X15, X16, X17, X18, X19]:(((~r2_hidden(X16,X15)|X16=X14|X15!=k1_tarski(X14))&(X17!=X14|r2_hidden(X17,X15)|X15!=k1_tarski(X14)))&((~r2_hidden(esk2_2(X18,X19),X19)|esk2_2(X18,X19)!=X18|X19=k1_tarski(X18))&(r2_hidden(esk2_2(X18,X19),X19)|esk2_2(X18,X19)=X18|X19=k1_tarski(X18)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.12/0.39  fof(c_0_38, plain, ![X21]:k2_tarski(X21,X21)=k1_tarski(X21), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.12/0.39  fof(c_0_39, plain, ![X24, X25, X26]:k2_enumset1(X24,X24,X25,X26)=k1_enumset1(X24,X25,X26), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.12/0.39  fof(c_0_40, plain, ![X27, X28, X29, X30]:k3_enumset1(X27,X27,X28,X29,X30)=k2_enumset1(X27,X28,X29,X30), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.12/0.39  fof(c_0_41, plain, ![X31, X32, X33, X34, X35]:k4_enumset1(X31,X31,X32,X33,X34,X35)=k3_enumset1(X31,X32,X33,X34,X35), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.12/0.39  fof(c_0_42, plain, ![X36, X37, X38, X39, X40, X41]:k5_enumset1(X36,X36,X37,X38,X39,X40,X41)=k4_enumset1(X36,X37,X38,X39,X40,X41), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.12/0.39  fof(c_0_43, plain, ![X42, X43, X44, X45, X46, X47, X48]:k6_enumset1(X42,X42,X43,X44,X45,X46,X47,X48)=k5_enumset1(X42,X43,X44,X45,X46,X47,X48), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.12/0.39  fof(c_0_44, plain, ![X58, X59]:((k4_xboole_0(k1_tarski(X58),k1_tarski(X59))!=k1_tarski(X58)|X58!=X59)&(X58=X59|k4_xboole_0(k1_tarski(X58),k1_tarski(X59))=k1_tarski(X58))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_zfmisc_1])])).
% 0.12/0.39  cnf(c_0_45, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.12/0.39  cnf(c_0_46, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_35, c_0_36])).
% 0.12/0.39  fof(c_0_47, plain, ![X8]:k3_xboole_0(X8,X8)=X8, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.12/0.39  fof(c_0_48, plain, ![X66, X67]:((~r1_tarski(X67,k3_subset_1(X66,X67))|X67=k1_subset_1(X66)|~m1_subset_1(X67,k1_zfmisc_1(X66)))&(X67!=k1_subset_1(X66)|r1_tarski(X67,k3_subset_1(X66,X67))|~m1_subset_1(X67,k1_zfmisc_1(X66)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_subset_1])])])).
% 0.12/0.39  fof(c_0_49, plain, ![X60]:k1_subset_1(X60)=k1_xboole_0, inference(variable_rename,[status(thm)],[d3_subset_1])).
% 0.12/0.39  fof(c_0_50, plain, ![X65]:k2_subset_1(X65)=k3_subset_1(X65,k1_subset_1(X65)), inference(variable_rename,[status(thm)],[t22_subset_1])).
% 0.12/0.39  fof(c_0_51, plain, ![X61]:k2_subset_1(X61)=X61, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.12/0.39  fof(c_0_52, plain, ![X62]:m1_subset_1(k1_subset_1(X62),k1_zfmisc_1(X62)), inference(variable_rename,[status(thm)],[dt_k1_subset_1])).
% 0.12/0.39  fof(c_0_53, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(X2=k1_tarski(X1)=>k7_setfam_1(X1,X2)=k1_tarski(k1_xboole_0)))), inference(assume_negation,[status(cth)],[t55_setfam_1])).
% 0.12/0.39  cnf(c_0_54, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.12/0.39  cnf(c_0_55, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.12/0.39  cnf(c_0_56, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.12/0.39  cnf(c_0_57, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.12/0.39  cnf(c_0_58, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.12/0.39  cnf(c_0_59, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.12/0.39  cnf(c_0_60, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.12/0.39  cnf(c_0_61, plain, (k4_xboole_0(k1_tarski(X1),k1_tarski(X2))!=k1_tarski(X1)|X1!=X2), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.12/0.39  cnf(c_0_62, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))), inference(rw,[status(thm)],[c_0_45, c_0_46])).
% 0.12/0.39  cnf(c_0_63, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.12/0.39  fof(c_0_64, plain, ![X13]:k5_xboole_0(X13,X13)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 0.12/0.39  fof(c_0_65, plain, ![X49, X50, X51, X52, X53, X54]:(((~r2_hidden(X51,X50)|r1_tarski(X51,X49)|X50!=k1_zfmisc_1(X49))&(~r1_tarski(X52,X49)|r2_hidden(X52,X50)|X50!=k1_zfmisc_1(X49)))&((~r2_hidden(esk3_2(X53,X54),X54)|~r1_tarski(esk3_2(X53,X54),X53)|X54=k1_zfmisc_1(X53))&(r2_hidden(esk3_2(X53,X54),X54)|r1_tarski(esk3_2(X53,X54),X53)|X54=k1_zfmisc_1(X53)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.12/0.39  cnf(c_0_66, plain, (r1_tarski(X1,k3_subset_1(X2,X1))|X1!=k1_subset_1(X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.12/0.39  cnf(c_0_67, plain, (k1_subset_1(X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.12/0.39  cnf(c_0_68, plain, (k2_subset_1(X1)=k3_subset_1(X1,k1_subset_1(X1))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.12/0.39  cnf(c_0_69, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.12/0.39  cnf(c_0_70, plain, (m1_subset_1(k1_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.12/0.39  fof(c_0_71, plain, ![X72, X73, X74, X75]:(((~r2_hidden(X75,X74)|r2_hidden(k3_subset_1(X72,X75),X73)|~m1_subset_1(X75,k1_zfmisc_1(X72))|X74!=k7_setfam_1(X72,X73)|~m1_subset_1(X74,k1_zfmisc_1(k1_zfmisc_1(X72)))|~m1_subset_1(X73,k1_zfmisc_1(k1_zfmisc_1(X72))))&(~r2_hidden(k3_subset_1(X72,X75),X73)|r2_hidden(X75,X74)|~m1_subset_1(X75,k1_zfmisc_1(X72))|X74!=k7_setfam_1(X72,X73)|~m1_subset_1(X74,k1_zfmisc_1(k1_zfmisc_1(X72)))|~m1_subset_1(X73,k1_zfmisc_1(k1_zfmisc_1(X72)))))&((m1_subset_1(esk4_3(X72,X73,X74),k1_zfmisc_1(X72))|X74=k7_setfam_1(X72,X73)|~m1_subset_1(X74,k1_zfmisc_1(k1_zfmisc_1(X72)))|~m1_subset_1(X73,k1_zfmisc_1(k1_zfmisc_1(X72))))&((~r2_hidden(esk4_3(X72,X73,X74),X74)|~r2_hidden(k3_subset_1(X72,esk4_3(X72,X73,X74)),X73)|X74=k7_setfam_1(X72,X73)|~m1_subset_1(X74,k1_zfmisc_1(k1_zfmisc_1(X72)))|~m1_subset_1(X73,k1_zfmisc_1(k1_zfmisc_1(X72))))&(r2_hidden(esk4_3(X72,X73,X74),X74)|r2_hidden(k3_subset_1(X72,esk4_3(X72,X73,X74)),X73)|X74=k7_setfam_1(X72,X73)|~m1_subset_1(X74,k1_zfmisc_1(k1_zfmisc_1(X72)))|~m1_subset_1(X73,k1_zfmisc_1(k1_zfmisc_1(X72))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_setfam_1])])])])])).
% 0.12/0.39  fof(c_0_72, plain, ![X89, X90, X91]:(~r2_hidden(X89,X90)|~m1_subset_1(X90,k1_zfmisc_1(X91))|m1_subset_1(X89,X91)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.12/0.39  fof(c_0_73, plain, ![X77, X78]:(~m1_subset_1(X78,k1_zfmisc_1(k1_zfmisc_1(X77)))|m1_subset_1(k7_setfam_1(X77,X78),k1_zfmisc_1(k1_zfmisc_1(X77)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_setfam_1])])).
% 0.12/0.39  fof(c_0_74, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k1_zfmisc_1(esk5_0)))&(esk6_0=k1_tarski(esk5_0)&k7_setfam_1(esk5_0,esk6_0)!=k1_tarski(k1_xboole_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_53])])])).
% 0.12/0.39  fof(c_0_75, plain, ![X79, X80]:(~m1_subset_1(X80,k1_zfmisc_1(k1_zfmisc_1(X79)))|k7_setfam_1(X79,k7_setfam_1(X79,X80))=X80), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k7_setfam_1])])).
% 0.12/0.39  cnf(c_0_76, plain, (X1=X3|X2!=k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_55]), c_0_36]), c_0_56]), c_0_57]), c_0_58]), c_0_59]), c_0_60])).
% 0.12/0.39  fof(c_0_77, plain, ![X9]:(X9=k1_xboole_0|r2_hidden(esk1_1(X9),X9)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.12/0.39  cnf(c_0_78, plain, (X1!=X2|k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))))!=k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_55]), c_0_55]), c_0_55]), c_0_36]), c_0_36]), c_0_36]), c_0_62]), c_0_56]), c_0_56]), c_0_56]), c_0_56]), c_0_56]), c_0_56]), c_0_57]), c_0_57]), c_0_57]), c_0_57]), c_0_57]), c_0_57]), c_0_57]), c_0_58]), c_0_58]), c_0_58]), c_0_58]), c_0_58]), c_0_58]), c_0_58]), c_0_58]), c_0_59]), c_0_59]), c_0_59]), c_0_59]), c_0_59]), c_0_59]), c_0_59]), c_0_59]), c_0_59]), c_0_60]), c_0_60]), c_0_60]), c_0_60]), c_0_60]), c_0_60]), c_0_60]), c_0_60]), c_0_60]), c_0_60])).
% 0.12/0.39  cnf(c_0_79, plain, (k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_46]), c_0_56]), c_0_57]), c_0_58]), c_0_59]), c_0_60])).
% 0.12/0.39  cnf(c_0_80, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.12/0.39  fof(c_0_81, plain, ![X70, X71]:(~r2_hidden(X70,X71)|m1_subset_1(k1_tarski(X70),k1_zfmisc_1(X71))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_subset_1])])).
% 0.12/0.39  cnf(c_0_82, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.12/0.39  cnf(c_0_83, plain, (r1_tarski(X1,k3_subset_1(X2,X1))|X1!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_66, c_0_67])).
% 0.12/0.39  cnf(c_0_84, plain, (X1=k3_subset_1(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68, c_0_69]), c_0_67])).
% 0.12/0.39  cnf(c_0_85, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_70, c_0_67])).
% 0.12/0.39  cnf(c_0_86, plain, (r2_hidden(k3_subset_1(X3,X1),X4)|~r2_hidden(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X3))|X2!=k7_setfam_1(X3,X4)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X3)))|~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X3)))), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.12/0.39  cnf(c_0_87, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.12/0.39  cnf(c_0_88, plain, (m1_subset_1(k7_setfam_1(X2,X1),k1_zfmisc_1(k1_zfmisc_1(X2)))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.12/0.39  cnf(c_0_89, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k1_zfmisc_1(esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.12/0.39  cnf(c_0_90, plain, (k7_setfam_1(X2,k7_setfam_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.12/0.39  cnf(c_0_91, plain, (X1=X2|~r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_76])).
% 0.12/0.39  cnf(c_0_92, plain, (X1=k1_xboole_0|r2_hidden(esk1_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_77])).
% 0.12/0.39  cnf(c_0_93, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_78]), c_0_79]), c_0_80])).
% 0.12/0.39  cnf(c_0_94, negated_conjecture, (esk6_0=k1_tarski(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.12/0.39  fof(c_0_95, plain, ![X63, X64]:(~m1_subset_1(X64,k1_zfmisc_1(X63))|k3_subset_1(X63,k3_subset_1(X63,X64))=X64), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 0.12/0.39  cnf(c_0_96, plain, (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_81])).
% 0.12/0.39  cnf(c_0_97, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_82])).
% 0.12/0.39  cnf(c_0_98, plain, (r1_tarski(k1_xboole_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_83]), c_0_84]), c_0_85])])).
% 0.12/0.39  cnf(c_0_99, plain, (k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(split_conjunct,[status(thm)],[t1_zfmisc_1])).
% 0.12/0.39  cnf(c_0_100, plain, (r2_hidden(k3_subset_1(X1,X2),X3)|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))|~r2_hidden(X2,k7_setfam_1(X1,X3))), inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_86, c_0_87])]), c_0_88])).
% 0.12/0.39  cnf(c_0_101, negated_conjecture, (m1_subset_1(k7_setfam_1(esk5_0,esk6_0),k1_zfmisc_1(k1_zfmisc_1(esk5_0)))), inference(spm,[status(thm)],[c_0_88, c_0_89])).
% 0.12/0.39  cnf(c_0_102, negated_conjecture, (k7_setfam_1(esk5_0,k7_setfam_1(esk5_0,esk6_0))=esk6_0), inference(spm,[status(thm)],[c_0_90, c_0_89])).
% 0.12/0.39  cnf(c_0_103, plain, (esk1_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))=X1), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_93])).
% 0.12/0.39  cnf(c_0_104, negated_conjecture, (esk6_0=k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_94, c_0_55]), c_0_36]), c_0_56]), c_0_57]), c_0_58]), c_0_59]), c_0_60])).
% 0.12/0.39  cnf(c_0_105, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_95])).
% 0.12/0.39  fof(c_0_106, plain, ![X92, X93, X94]:(~m1_subset_1(X93,k1_zfmisc_1(k1_zfmisc_1(X92)))|(~m1_subset_1(X94,k1_zfmisc_1(k1_zfmisc_1(X92)))|(~r1_tarski(k7_setfam_1(X92,X93),k7_setfam_1(X92,X94))|r1_tarski(X93,X94)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t51_setfam_1])])])).
% 0.12/0.39  cnf(c_0_107, plain, (m1_subset_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_zfmisc_1(X2))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_96, c_0_55]), c_0_36]), c_0_56]), c_0_57]), c_0_58]), c_0_59]), c_0_60])).
% 0.12/0.39  cnf(c_0_108, plain, (r2_hidden(k1_xboole_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_97, c_0_98])).
% 0.12/0.39  cnf(c_0_109, plain, (k1_zfmisc_1(k1_xboole_0)=k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_99, c_0_55]), c_0_36]), c_0_56]), c_0_57]), c_0_58]), c_0_59]), c_0_60])).
% 0.12/0.39  cnf(c_0_110, negated_conjecture, (r2_hidden(k3_subset_1(esk5_0,X1),k7_setfam_1(esk5_0,esk6_0))|~r2_hidden(X1,esk6_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_101]), c_0_102])).
% 0.12/0.39  cnf(c_0_111, negated_conjecture, (esk1_1(esk6_0)=esk5_0), inference(spm,[status(thm)],[c_0_103, c_0_104])).
% 0.12/0.39  cnf(c_0_112, plain, (k3_subset_1(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_85]), c_0_84])).
% 0.12/0.39  cnf(c_0_113, negated_conjecture, (esk6_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_93, c_0_104])).
% 0.12/0.39  fof(c_0_114, plain, ![X56, X57]:((~r1_tarski(X56,k1_tarski(X57))|(X56=k1_xboole_0|X56=k1_tarski(X57)))&((X56!=k1_xboole_0|r1_tarski(X56,k1_tarski(X57)))&(X56!=k1_tarski(X57)|r1_tarski(X56,k1_tarski(X57))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).
% 0.12/0.39  cnf(c_0_115, plain, (r1_tarski(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))|~r1_tarski(k7_setfam_1(X2,X1),k7_setfam_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_106])).
% 0.12/0.39  cnf(c_0_116, plain, (m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_108]), c_0_109])).
% 0.12/0.39  fof(c_0_117, plain, ![X85, X86]:((~m1_subset_1(X85,k1_zfmisc_1(X86))|r1_tarski(X85,X86))&(~r1_tarski(X85,X86)|m1_subset_1(X85,k1_zfmisc_1(X86)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.12/0.39  cnf(c_0_118, negated_conjecture, (r2_hidden(k1_xboole_0,k7_setfam_1(esk5_0,esk6_0))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_92]), c_0_111]), c_0_112]), c_0_113])).
% 0.12/0.39  cnf(c_0_119, plain, (X1=k1_xboole_0|X1=k1_tarski(X2)|~r1_tarski(X1,k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_114])).
% 0.12/0.39  cnf(c_0_120, negated_conjecture, (r1_tarski(X1,esk6_0)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(esk5_0)))|~r1_tarski(k7_setfam_1(esk5_0,X1),k7_setfam_1(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_115, c_0_89])).
% 0.12/0.39  cnf(c_0_121, plain, (m1_subset_1(k7_setfam_1(X1,k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(spm,[status(thm)],[c_0_88, c_0_116])).
% 0.12/0.39  cnf(c_0_122, plain, (k7_setfam_1(X1,k7_setfam_1(X1,k1_zfmisc_1(k1_xboole_0)))=k1_zfmisc_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_90, c_0_116])).
% 0.12/0.39  cnf(c_0_123, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_117])).
% 0.12/0.39  cnf(c_0_124, negated_conjecture, (m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k7_setfam_1(esk5_0,esk6_0)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_118]), c_0_109])).
% 0.12/0.39  cnf(c_0_125, plain, (X1=k1_xboole_0|X1=k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)|~r1_tarski(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_119, c_0_55]), c_0_55]), c_0_36]), c_0_36]), c_0_56]), c_0_56]), c_0_57]), c_0_57]), c_0_58]), c_0_58]), c_0_59]), c_0_59]), c_0_60]), c_0_60])).
% 0.12/0.39  cnf(c_0_126, negated_conjecture, (r1_tarski(k7_setfam_1(esk5_0,k1_zfmisc_1(k1_xboole_0)),esk6_0)|~r1_tarski(k1_zfmisc_1(k1_xboole_0),k7_setfam_1(esk5_0,esk6_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120, c_0_121]), c_0_122])).
% 0.12/0.39  cnf(c_0_127, negated_conjecture, (r1_tarski(k1_zfmisc_1(k1_xboole_0),k7_setfam_1(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_123, c_0_124])).
% 0.12/0.39  cnf(c_0_128, negated_conjecture, (k7_setfam_1(esk5_0,esk6_0)!=k1_tarski(k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.12/0.39  cnf(c_0_129, negated_conjecture, (X1=k1_xboole_0|X1=esk6_0|~r1_tarski(X1,esk6_0)), inference(spm,[status(thm)],[c_0_125, c_0_104])).
% 0.12/0.39  cnf(c_0_130, negated_conjecture, (r1_tarski(k7_setfam_1(esk5_0,k1_zfmisc_1(k1_xboole_0)),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_126, c_0_127])])).
% 0.12/0.39  cnf(c_0_131, negated_conjecture, (k7_setfam_1(esk5_0,esk6_0)!=k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_128, c_0_55]), c_0_36]), c_0_56]), c_0_57]), c_0_58]), c_0_59]), c_0_60])).
% 0.12/0.39  fof(c_0_132, plain, ![X87, X88]:(~m1_subset_1(X88,k1_zfmisc_1(k1_zfmisc_1(X87)))|(X88=k1_xboole_0|k7_setfam_1(X87,X88)!=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t46_setfam_1])])).
% 0.12/0.39  cnf(c_0_133, negated_conjecture, (k7_setfam_1(esk5_0,k1_zfmisc_1(k1_xboole_0))=esk6_0|k7_setfam_1(esk5_0,k1_zfmisc_1(k1_xboole_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_129, c_0_130])).
% 0.12/0.39  cnf(c_0_134, negated_conjecture, (k7_setfam_1(esk5_0,esk6_0)!=k1_zfmisc_1(k1_xboole_0)), inference(rw,[status(thm)],[c_0_131, c_0_109])).
% 0.12/0.39  cnf(c_0_135, plain, (X1=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))|k7_setfam_1(X2,X1)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_132])).
% 0.12/0.39  cnf(c_0_136, negated_conjecture, (k7_setfam_1(esk5_0,k1_zfmisc_1(k1_xboole_0))=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_122, c_0_133]), c_0_134])).
% 0.12/0.39  cnf(c_0_137, plain, (k1_zfmisc_1(k1_xboole_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_93, c_0_109])).
% 0.12/0.39  cnf(c_0_138, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_135, c_0_136]), c_0_116])]), c_0_137]), ['proof']).
% 0.12/0.39  # SZS output end CNFRefutation
% 0.12/0.39  # Proof object total steps             : 139
% 0.12/0.39  # Proof object clause steps            : 75
% 0.12/0.39  # Proof object formula steps           : 64
% 0.12/0.39  # Proof object conjectures             : 24
% 0.12/0.39  # Proof object clause conjectures      : 21
% 0.12/0.39  # Proof object formula conjectures     : 3
% 0.12/0.39  # Proof object initial clauses used    : 34
% 0.12/0.39  # Proof object initial formulas used   : 32
% 0.12/0.39  # Proof object generating inferences   : 21
% 0.12/0.39  # Proof object simplifying inferences  : 136
% 0.12/0.39  # Training examples: 0 positive, 0 negative
% 0.12/0.39  # Parsed axioms                        : 35
% 0.12/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.39  # Initial clauses                      : 52
% 0.12/0.39  # Removed in clause preprocessing      : 11
% 0.12/0.39  # Initial clauses in saturation        : 41
% 0.12/0.39  # Processed clauses                    : 386
% 0.12/0.39  # ...of these trivial                  : 19
% 0.12/0.39  # ...subsumed                          : 84
% 0.12/0.39  # ...remaining for further processing  : 283
% 0.12/0.39  # Other redundant clauses eliminated   : 14
% 0.12/0.39  # Clauses deleted for lack of memory   : 0
% 0.12/0.39  # Backward-subsumed                    : 3
% 0.12/0.39  # Backward-rewritten                   : 31
% 0.12/0.39  # Generated clauses                    : 926
% 0.12/0.39  # ...of the previous two non-trivial   : 725
% 0.12/0.39  # Contextual simplify-reflections      : 3
% 0.12/0.39  # Paramodulations                      : 902
% 0.12/0.39  # Factorizations                       : 10
% 0.12/0.39  # Equation resolutions                 : 15
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
% 0.12/0.39  # Current number of processed clauses  : 199
% 0.12/0.39  #    Positive orientable unit clauses  : 78
% 0.12/0.39  #    Positive unorientable unit clauses: 0
% 0.12/0.39  #    Negative unit clauses             : 18
% 0.12/0.39  #    Non-unit-clauses                  : 103
% 0.12/0.39  # Current number of unprocessed clauses: 399
% 0.12/0.39  # ...number of literals in the above   : 1194
% 0.12/0.39  # Current number of archived formulas  : 0
% 0.12/0.39  # Current number of archived clauses   : 85
% 0.12/0.39  # Clause-clause subsumption calls (NU) : 2090
% 0.12/0.39  # Rec. Clause-clause subsumption calls : 1443
% 0.12/0.39  # Non-unit clause-clause subsumptions  : 56
% 0.12/0.39  # Unit Clause-clause subsumption calls : 200
% 0.12/0.39  # Rewrite failures with RHS unbound    : 0
% 0.12/0.39  # BW rewrite match attempts            : 26
% 0.12/0.39  # BW rewrite match successes           : 16
% 0.12/0.39  # Condensation attempts                : 0
% 0.12/0.39  # Condensation successes               : 0
% 0.12/0.39  # Termbank termtop insertions          : 22971
% 0.12/0.39  
% 0.12/0.39  # -------------------------------------------------
% 0.12/0.39  # User time                : 0.057 s
% 0.12/0.39  # System time              : 0.004 s
% 0.12/0.39  # Total time               : 0.061 s
% 0.12/0.39  # Maximum resident set size: 1608 pages
%------------------------------------------------------------------------------
