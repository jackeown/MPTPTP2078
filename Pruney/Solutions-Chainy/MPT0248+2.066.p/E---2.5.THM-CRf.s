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
% DateTime   : Thu Dec  3 10:39:47 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  139 (3372 expanded)
%              Number of clauses        :   88 (1335 expanded)
%              Number of leaves         :   25 (1003 expanded)
%              Depth                    :   25
%              Number of atoms          :  280 (5108 expanded)
%              Number of equality atoms :  137 (3691 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t43_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ~ ( k1_tarski(X1) = k2_xboole_0(X2,X3)
        & ~ ( X2 = k1_tarski(X1)
            & X3 = k1_tarski(X1) )
        & ~ ( X2 = k1_xboole_0
            & X3 = k1_tarski(X1) )
        & ~ ( X2 = k1_tarski(X1)
            & X3 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

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

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t95_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(l1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(t66_xboole_1,axiom,(
    ! [X1] :
      ( ~ ( ~ r1_xboole_0(X1,X1)
          & X1 = k1_xboole_0 )
      & ~ ( X1 != k1_xboole_0
          & r1_xboole_0(X1,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(commutativity_k5_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(c_0_25,plain,(
    ! [X88,X89] : k3_tarski(k2_tarski(X88,X89)) = k2_xboole_0(X88,X89) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_26,plain,(
    ! [X59,X60] : k1_enumset1(X59,X59,X60) = k2_tarski(X59,X60) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_27,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( k1_tarski(X1) = k2_xboole_0(X2,X3)
          & ~ ( X2 = k1_tarski(X1)
              & X3 = k1_tarski(X1) )
          & ~ ( X2 = k1_xboole_0
              & X3 = k1_tarski(X1) )
          & ~ ( X2 = k1_tarski(X1)
              & X3 = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t43_zfmisc_1])).

fof(c_0_28,plain,(
    ! [X43,X44] : r1_tarski(X43,k2_xboole_0(X43,X44)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_29,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_31,plain,(
    ! [X61,X62,X63] : k2_enumset1(X61,X61,X62,X63) = k1_enumset1(X61,X62,X63) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_32,plain,(
    ! [X64,X65,X66,X67] : k3_enumset1(X64,X64,X65,X66,X67) = k2_enumset1(X64,X65,X66,X67) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_33,plain,(
    ! [X68,X69,X70,X71,X72] : k4_enumset1(X68,X68,X69,X70,X71,X72) = k3_enumset1(X68,X69,X70,X71,X72) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_34,plain,(
    ! [X73,X74,X75,X76,X77,X78] : k5_enumset1(X73,X73,X74,X75,X76,X77,X78) = k4_enumset1(X73,X74,X75,X76,X77,X78) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_35,plain,(
    ! [X79,X80,X81,X82,X83,X84,X85] : k6_enumset1(X79,X79,X80,X81,X82,X83,X84,X85) = k5_enumset1(X79,X80,X81,X82,X83,X84,X85) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_36,negated_conjecture,
    ( k1_tarski(esk6_0) = k2_xboole_0(esk7_0,esk8_0)
    & ( esk7_0 != k1_tarski(esk6_0)
      | esk8_0 != k1_tarski(esk6_0) )
    & ( esk7_0 != k1_xboole_0
      | esk8_0 != k1_tarski(esk6_0) )
    & ( esk7_0 != k1_tarski(esk6_0)
      | esk8_0 != k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_27])])])).

fof(c_0_37,plain,(
    ! [X58] : k2_tarski(X58,X58) = k1_tarski(X58) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_39,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_40,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_41,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_42,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_43,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_44,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_45,negated_conjecture,
    ( k1_tarski(esk6_0) = k2_xboole_0(esk7_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_46,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_47,plain,(
    ! [X51,X52,X53,X54,X55,X56] :
      ( ( ~ r2_hidden(X53,X52)
        | X53 = X51
        | X52 != k1_tarski(X51) )
      & ( X54 != X51
        | r2_hidden(X54,X52)
        | X52 != k1_tarski(X51) )
      & ( ~ r2_hidden(esk5_2(X55,X56),X56)
        | esk5_2(X55,X56) != X55
        | X56 = k1_tarski(X55) )
      & ( r2_hidden(esk5_2(X55,X56),X56)
        | esk5_2(X55,X56) = X55
        | X56 = k1_tarski(X55) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_48,plain,(
    ! [X14,X15,X16,X17,X18] :
      ( ( ~ r1_tarski(X14,X15)
        | ~ r2_hidden(X16,X14)
        | r2_hidden(X16,X15) )
      & ( r2_hidden(esk2_2(X17,X18),X17)
        | r1_tarski(X17,X18) )
      & ( ~ r2_hidden(esk2_2(X17,X18),X18)
        | r1_tarski(X17,X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_49,plain,
    ( r1_tarski(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_39]),c_0_40]),c_0_41]),c_0_42]),c_0_43]),c_0_44])).

cnf(c_0_50,negated_conjecture,
    ( k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0) = k3_tarski(k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk8_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_46]),c_0_30]),c_0_39]),c_0_40]),c_0_40]),c_0_41]),c_0_41]),c_0_42]),c_0_42]),c_0_43]),c_0_43]),c_0_44]),c_0_44])).

cnf(c_0_51,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_52,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(esk7_0,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

fof(c_0_54,plain,(
    ! [X10,X11,X12] :
      ( ( ~ v1_xboole_0(X10)
        | ~ r2_hidden(X11,X10) )
      & ( r2_hidden(esk1_1(X12),X12)
        | v1_xboole_0(X12) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_55,plain,
    ( X1 = X3
    | X2 != k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_46]),c_0_30]),c_0_40]),c_0_41]),c_0_42]),c_0_43]),c_0_44])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(X1,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_57,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_58,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_55])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(esk1_1(esk7_0),k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))
    | v1_xboole_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_60,negated_conjecture,
    ( esk1_1(esk7_0) = esk6_0
    | v1_xboole_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

fof(c_0_61,plain,(
    ! [X49,X50] : k3_xboole_0(X49,X50) = k5_xboole_0(k5_xboole_0(X49,X50),k2_xboole_0(X49,X50)) ),
    inference(variable_rename,[status(thm)],[t95_xboole_1])).

cnf(c_0_62,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(esk6_0,esk7_0)
    | v1_xboole_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_60])).

fof(c_0_64,plain,(
    ! [X24,X25,X27,X28,X29] :
      ( ( r2_hidden(esk3_2(X24,X25),X24)
        | r1_xboole_0(X24,X25) )
      & ( r2_hidden(esk3_2(X24,X25),X25)
        | r1_xboole_0(X24,X25) )
      & ( ~ r2_hidden(X29,X27)
        | ~ r2_hidden(X29,X28)
        | ~ r1_xboole_0(X27,X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_65,plain,(
    ! [X40,X41] : r1_tarski(k3_xboole_0(X40,X41),X40) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_66,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

fof(c_0_67,plain,(
    ! [X86,X87] :
      ( ( ~ r1_tarski(k1_tarski(X86),X87)
        | r2_hidden(X86,X87) )
      & ( ~ r2_hidden(X86,X87)
        | r1_tarski(k1_tarski(X86),X87) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).

fof(c_0_68,plain,(
    ! [X42] :
      ( ( r1_xboole_0(X42,X42)
        | X42 != k1_xboole_0 )
      & ( X42 = k1_xboole_0
        | ~ r1_xboole_0(X42,X42) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t66_xboole_1])])])).

cnf(c_0_69,negated_conjecture,
    ( r2_hidden(esk6_0,esk7_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_70,plain,
    ( r2_hidden(esk3_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

fof(c_0_71,plain,(
    ! [X23] : k3_xboole_0(X23,X23) = X23 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

fof(c_0_72,plain,(
    ! [X22] : k2_xboole_0(X22,X22) = X22 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

cnf(c_0_73,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_74,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_39]),c_0_40]),c_0_41])).

fof(c_0_75,plain,(
    ! [X45,X46,X47] : k5_xboole_0(k5_xboole_0(X45,X46),X47) = k5_xboole_0(X45,k5_xboole_0(X46,X47)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_76,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_77,plain,
    ( X1 = k1_xboole_0
    | ~ r1_xboole_0(X1,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_78,negated_conjecture,
    ( r1_xboole_0(X1,esk7_0)
    | r2_hidden(esk6_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_79,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

fof(c_0_80,plain,(
    ! [X48] : k5_xboole_0(X48,X48) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

cnf(c_0_81,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_82,plain,
    ( r1_tarski(k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_74]),c_0_42]),c_0_43]),c_0_44])).

cnf(c_0_83,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

fof(c_0_84,plain,(
    ! [X36,X37] :
      ( ( r1_tarski(X36,X37)
        | X36 != X37 )
      & ( r1_tarski(X37,X36)
        | X36 != X37 )
      & ( ~ r1_tarski(X36,X37)
        | ~ r1_tarski(X37,X36)
        | X36 = X37 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_85,plain,
    ( r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_46]),c_0_30]),c_0_40]),c_0_41]),c_0_42]),c_0_43]),c_0_44])).

cnf(c_0_86,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r2_hidden(esk6_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_87,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X1),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_74]),c_0_42]),c_0_43]),c_0_44])).

cnf(c_0_88,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_89,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_39]),c_0_40]),c_0_41]),c_0_42]),c_0_43]),c_0_44])).

cnf(c_0_90,negated_conjecture,
    ( r1_xboole_0(X1,esk7_0)
    | r2_hidden(esk3_2(X1,esk7_0),k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_70])).

cnf(c_0_91,plain,
    ( r1_tarski(k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),X1) ),
    inference(rw,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_92,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_93,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r1_tarski(k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

fof(c_0_94,plain,(
    ! [X8,X9] : k5_xboole_0(X8,X9) = k5_xboole_0(X9,X8) ),
    inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).

cnf(c_0_95,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_87,c_0_88]),c_0_89])).

cnf(c_0_96,plain,
    ( r2_hidden(esk3_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_97,negated_conjecture,
    ( esk3_2(X1,esk7_0) = esk6_0
    | r1_xboole_0(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_90])).

cnf(c_0_98,negated_conjecture,
    ( r1_tarski(k5_xboole_0(esk7_0,k5_xboole_0(esk8_0,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))),esk7_0) ),
    inference(spm,[status(thm)],[c_0_91,c_0_50])).

cnf(c_0_99,negated_conjecture,
    ( k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0) = esk7_0
    | esk7_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_53])])).

cnf(c_0_100,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_94])).

cnf(c_0_101,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_88]),c_0_95])).

cnf(c_0_102,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_103,negated_conjecture,
    ( r1_xboole_0(X1,esk7_0)
    | r2_hidden(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_96,c_0_97])).

cnf(c_0_104,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r1_tarski(esk8_0,esk7_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_100]),c_0_101])).

cnf(c_0_105,negated_conjecture,
    ( r2_hidden(esk6_0,X1)
    | ~ r2_hidden(X2,esk7_0)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_102,c_0_103])).

cnf(c_0_106,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r2_hidden(X1,esk7_0)
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_104])).

cnf(c_0_107,negated_conjecture,
    ( r2_hidden(esk6_0,X1)
    | v1_xboole_0(X1)
    | ~ r2_hidden(esk1_1(X1),esk7_0) ),
    inference(spm,[status(thm)],[c_0_105,c_0_57])).

cnf(c_0_108,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r2_hidden(esk1_1(esk8_0),esk7_0)
    | v1_xboole_0(esk8_0) ),
    inference(spm,[status(thm)],[c_0_106,c_0_57])).

cnf(c_0_109,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_110,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r2_hidden(esk6_0,esk8_0)
    | v1_xboole_0(esk8_0) ),
    inference(spm,[status(thm)],[c_0_107,c_0_108])).

cnf(c_0_111,negated_conjecture,
    ( esk7_0 != k1_tarski(esk6_0)
    | esk8_0 != k1_tarski(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_112,negated_conjecture,
    ( r1_tarski(esk7_0,X1)
    | r2_hidden(esk2_2(esk7_0,X1),k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_109])).

cnf(c_0_113,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r2_hidden(esk6_0,esk8_0)
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_110])).

cnf(c_0_114,negated_conjecture,
    ( esk7_0 != k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)
    | esk8_0 != k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_111,c_0_46]),c_0_46]),c_0_30]),c_0_30]),c_0_40]),c_0_40]),c_0_41]),c_0_41]),c_0_42]),c_0_42]),c_0_43]),c_0_43]),c_0_44]),c_0_44])).

fof(c_0_115,plain,(
    ! [X38,X39] :
      ( ~ r1_tarski(X38,X39)
      | k2_xboole_0(X38,X39) = X39 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_116,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk2_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_117,negated_conjecture,
    ( esk2_2(esk7_0,X1) = esk6_0
    | r1_tarski(esk7_0,X1) ),
    inference(spm,[status(thm)],[c_0_58,c_0_112])).

cnf(c_0_118,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r1_xboole_0(X1,esk8_0)
    | r2_hidden(esk6_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_113,c_0_70])).

cnf(c_0_119,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | esk8_0 != esk7_0 ),
    inference(spm,[status(thm)],[c_0_114,c_0_99])).

cnf(c_0_120,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_115])).

cnf(c_0_121,negated_conjecture,
    ( esk7_0 != k1_tarski(esk6_0)
    | esk8_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_122,negated_conjecture,
    ( r1_tarski(esk7_0,X1)
    | ~ r2_hidden(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_116,c_0_117])).

cnf(c_0_123,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | esk8_0 = k1_xboole_0
    | r2_hidden(esk6_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_77,c_0_118])).

cnf(c_0_124,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | ~ r1_tarski(esk7_0,esk8_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_104]),c_0_119])).

cnf(c_0_125,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_120,c_0_39]),c_0_40]),c_0_41]),c_0_42]),c_0_43]),c_0_44])).

cnf(c_0_126,negated_conjecture,
    ( r1_tarski(esk7_0,X1)
    | r2_hidden(esk6_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_109])).

cnf(c_0_127,plain,
    ( r1_xboole_0(X1,X1)
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_128,negated_conjecture,
    ( esk7_0 != k1_xboole_0
    | esk8_0 != k1_tarski(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_129,negated_conjecture,
    ( esk8_0 != k1_xboole_0
    | esk7_0 != k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_121,c_0_46]),c_0_30]),c_0_40]),c_0_41]),c_0_42]),c_0_43]),c_0_44])).

cnf(c_0_130,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_122,c_0_123]),c_0_124])).

cnf(c_0_131,negated_conjecture,
    ( k3_tarski(k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,X1)) = X1
    | r2_hidden(esk6_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_125,c_0_126])).

cnf(c_0_132,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(er,[status(thm)],[c_0_127])).

cnf(c_0_133,negated_conjecture,
    ( esk7_0 != k1_xboole_0
    | esk8_0 != k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_128,c_0_46]),c_0_30]),c_0_40]),c_0_41]),c_0_42]),c_0_43]),c_0_44])).

cnf(c_0_134,negated_conjecture,
    ( esk7_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_129,c_0_130]),c_0_99])).

cnf(c_0_135,negated_conjecture,
    ( k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0) = esk8_0
    | r2_hidden(esk6_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_131])).

cnf(c_0_136,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_102,c_0_132])).

cnf(c_0_137,negated_conjecture,
    ( k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0) != esk8_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_133,c_0_134])])).

cnf(c_0_138,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_135,c_0_134]),c_0_136]),c_0_137]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:03:50 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  # Version: 2.5pre002
% 0.14/0.36  # No SInE strategy applied
% 0.14/0.36  # Trying AutoSched0 for 299 seconds
% 0.21/0.42  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S054N
% 0.21/0.42  # and selection function GSelectMinInfpos.
% 0.21/0.42  #
% 0.21/0.42  # Preprocessing time       : 0.028 s
% 0.21/0.42  # Presaturation interreduction done
% 0.21/0.42  
% 0.21/0.42  # Proof found!
% 0.21/0.42  # SZS status Theorem
% 0.21/0.42  # SZS output start CNFRefutation
% 0.21/0.42  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.21/0.42  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.21/0.42  fof(t43_zfmisc_1, conjecture, ![X1, X2, X3]:~((((k1_tarski(X1)=k2_xboole_0(X2,X3)&~((X2=k1_tarski(X1)&X3=k1_tarski(X1))))&~((X2=k1_xboole_0&X3=k1_tarski(X1))))&~((X2=k1_tarski(X1)&X3=k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 0.21/0.42  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.21/0.42  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.21/0.42  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.21/0.42  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.21/0.42  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.21/0.42  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.21/0.42  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.21/0.42  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 0.21/0.42  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.21/0.42  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.21/0.42  fof(t95_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 0.21/0.42  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.21/0.42  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.21/0.42  fof(l1_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 0.21/0.42  fof(t66_xboole_1, axiom, ![X1]:(~((~(r1_xboole_0(X1,X1))&X1=k1_xboole_0))&~((X1!=k1_xboole_0&r1_xboole_0(X1,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 0.21/0.42  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.21/0.42  fof(idempotence_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 0.21/0.42  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.21/0.42  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 0.21/0.42  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.21/0.42  fof(commutativity_k5_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 0.21/0.42  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.21/0.42  fof(c_0_25, plain, ![X88, X89]:k3_tarski(k2_tarski(X88,X89))=k2_xboole_0(X88,X89), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.21/0.42  fof(c_0_26, plain, ![X59, X60]:k1_enumset1(X59,X59,X60)=k2_tarski(X59,X60), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.21/0.42  fof(c_0_27, negated_conjecture, ~(![X1, X2, X3]:~((((k1_tarski(X1)=k2_xboole_0(X2,X3)&~((X2=k1_tarski(X1)&X3=k1_tarski(X1))))&~((X2=k1_xboole_0&X3=k1_tarski(X1))))&~((X2=k1_tarski(X1)&X3=k1_xboole_0))))), inference(assume_negation,[status(cth)],[t43_zfmisc_1])).
% 0.21/0.42  fof(c_0_28, plain, ![X43, X44]:r1_tarski(X43,k2_xboole_0(X43,X44)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.21/0.42  cnf(c_0_29, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.42  cnf(c_0_30, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.21/0.42  fof(c_0_31, plain, ![X61, X62, X63]:k2_enumset1(X61,X61,X62,X63)=k1_enumset1(X61,X62,X63), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.21/0.42  fof(c_0_32, plain, ![X64, X65, X66, X67]:k3_enumset1(X64,X64,X65,X66,X67)=k2_enumset1(X64,X65,X66,X67), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.21/0.42  fof(c_0_33, plain, ![X68, X69, X70, X71, X72]:k4_enumset1(X68,X68,X69,X70,X71,X72)=k3_enumset1(X68,X69,X70,X71,X72), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.21/0.42  fof(c_0_34, plain, ![X73, X74, X75, X76, X77, X78]:k5_enumset1(X73,X73,X74,X75,X76,X77,X78)=k4_enumset1(X73,X74,X75,X76,X77,X78), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.21/0.42  fof(c_0_35, plain, ![X79, X80, X81, X82, X83, X84, X85]:k6_enumset1(X79,X79,X80,X81,X82,X83,X84,X85)=k5_enumset1(X79,X80,X81,X82,X83,X84,X85), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.21/0.42  fof(c_0_36, negated_conjecture, (((k1_tarski(esk6_0)=k2_xboole_0(esk7_0,esk8_0)&(esk7_0!=k1_tarski(esk6_0)|esk8_0!=k1_tarski(esk6_0)))&(esk7_0!=k1_xboole_0|esk8_0!=k1_tarski(esk6_0)))&(esk7_0!=k1_tarski(esk6_0)|esk8_0!=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_27])])])).
% 0.21/0.42  fof(c_0_37, plain, ![X58]:k2_tarski(X58,X58)=k1_tarski(X58), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.21/0.42  cnf(c_0_38, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.21/0.42  cnf(c_0_39, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_29, c_0_30])).
% 0.21/0.42  cnf(c_0_40, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.21/0.42  cnf(c_0_41, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.21/0.42  cnf(c_0_42, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.21/0.42  cnf(c_0_43, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.21/0.42  cnf(c_0_44, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.21/0.42  cnf(c_0_45, negated_conjecture, (k1_tarski(esk6_0)=k2_xboole_0(esk7_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.21/0.42  cnf(c_0_46, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.21/0.42  fof(c_0_47, plain, ![X51, X52, X53, X54, X55, X56]:(((~r2_hidden(X53,X52)|X53=X51|X52!=k1_tarski(X51))&(X54!=X51|r2_hidden(X54,X52)|X52!=k1_tarski(X51)))&((~r2_hidden(esk5_2(X55,X56),X56)|esk5_2(X55,X56)!=X55|X56=k1_tarski(X55))&(r2_hidden(esk5_2(X55,X56),X56)|esk5_2(X55,X56)=X55|X56=k1_tarski(X55)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.21/0.42  fof(c_0_48, plain, ![X14, X15, X16, X17, X18]:((~r1_tarski(X14,X15)|(~r2_hidden(X16,X14)|r2_hidden(X16,X15)))&((r2_hidden(esk2_2(X17,X18),X17)|r1_tarski(X17,X18))&(~r2_hidden(esk2_2(X17,X18),X18)|r1_tarski(X17,X18)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.21/0.42  cnf(c_0_49, plain, (r1_tarski(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_39]), c_0_40]), c_0_41]), c_0_42]), c_0_43]), c_0_44])).
% 0.21/0.42  cnf(c_0_50, negated_conjecture, (k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)=k3_tarski(k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk8_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_46]), c_0_30]), c_0_39]), c_0_40]), c_0_40]), c_0_41]), c_0_41]), c_0_42]), c_0_42]), c_0_43]), c_0_43]), c_0_44]), c_0_44])).
% 0.21/0.42  cnf(c_0_51, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.21/0.42  cnf(c_0_52, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.21/0.42  cnf(c_0_53, negated_conjecture, (r1_tarski(esk7_0,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.21/0.42  fof(c_0_54, plain, ![X10, X11, X12]:((~v1_xboole_0(X10)|~r2_hidden(X11,X10))&(r2_hidden(esk1_1(X12),X12)|v1_xboole_0(X12))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.21/0.42  cnf(c_0_55, plain, (X1=X3|X2!=k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_46]), c_0_30]), c_0_40]), c_0_41]), c_0_42]), c_0_43]), c_0_44])).
% 0.21/0.42  cnf(c_0_56, negated_conjecture, (r2_hidden(X1,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.21/0.42  cnf(c_0_57, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.21/0.42  cnf(c_0_58, plain, (X1=X2|~r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_55])).
% 0.21/0.42  cnf(c_0_59, negated_conjecture, (r2_hidden(esk1_1(esk7_0),k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))|v1_xboole_0(esk7_0)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.21/0.42  cnf(c_0_60, negated_conjecture, (esk1_1(esk7_0)=esk6_0|v1_xboole_0(esk7_0)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.21/0.42  fof(c_0_61, plain, ![X49, X50]:k3_xboole_0(X49,X50)=k5_xboole_0(k5_xboole_0(X49,X50),k2_xboole_0(X49,X50)), inference(variable_rename,[status(thm)],[t95_xboole_1])).
% 0.21/0.42  cnf(c_0_62, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.21/0.42  cnf(c_0_63, negated_conjecture, (r2_hidden(esk6_0,esk7_0)|v1_xboole_0(esk7_0)), inference(spm,[status(thm)],[c_0_57, c_0_60])).
% 0.21/0.42  fof(c_0_64, plain, ![X24, X25, X27, X28, X29]:(((r2_hidden(esk3_2(X24,X25),X24)|r1_xboole_0(X24,X25))&(r2_hidden(esk3_2(X24,X25),X25)|r1_xboole_0(X24,X25)))&(~r2_hidden(X29,X27)|~r2_hidden(X29,X28)|~r1_xboole_0(X27,X28))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.21/0.42  fof(c_0_65, plain, ![X40, X41]:r1_tarski(k3_xboole_0(X40,X41),X40), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.21/0.42  cnf(c_0_66, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.21/0.42  fof(c_0_67, plain, ![X86, X87]:((~r1_tarski(k1_tarski(X86),X87)|r2_hidden(X86,X87))&(~r2_hidden(X86,X87)|r1_tarski(k1_tarski(X86),X87))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).
% 0.21/0.42  fof(c_0_68, plain, ![X42]:((r1_xboole_0(X42,X42)|X42!=k1_xboole_0)&(X42=k1_xboole_0|~r1_xboole_0(X42,X42))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t66_xboole_1])])])).
% 0.21/0.42  cnf(c_0_69, negated_conjecture, (r2_hidden(esk6_0,esk7_0)|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.21/0.42  cnf(c_0_70, plain, (r2_hidden(esk3_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.21/0.42  fof(c_0_71, plain, ![X23]:k3_xboole_0(X23,X23)=X23, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.21/0.42  fof(c_0_72, plain, ![X22]:k2_xboole_0(X22,X22)=X22, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).
% 0.21/0.42  cnf(c_0_73, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.21/0.42  cnf(c_0_74, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_39]), c_0_40]), c_0_41])).
% 0.21/0.42  fof(c_0_75, plain, ![X45, X46, X47]:k5_xboole_0(k5_xboole_0(X45,X46),X47)=k5_xboole_0(X45,k5_xboole_0(X46,X47)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.21/0.42  cnf(c_0_76, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.21/0.42  cnf(c_0_77, plain, (X1=k1_xboole_0|~r1_xboole_0(X1,X1)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.21/0.42  cnf(c_0_78, negated_conjecture, (r1_xboole_0(X1,esk7_0)|r2_hidden(esk6_0,esk7_0)), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.21/0.42  cnf(c_0_79, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.21/0.42  fof(c_0_80, plain, ![X48]:k5_xboole_0(X48,X48)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 0.21/0.42  cnf(c_0_81, plain, (k2_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.21/0.42  cnf(c_0_82, plain, (r1_tarski(k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73, c_0_74]), c_0_42]), c_0_43]), c_0_44])).
% 0.21/0.42  cnf(c_0_83, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.21/0.42  fof(c_0_84, plain, ![X36, X37]:(((r1_tarski(X36,X37)|X36!=X37)&(r1_tarski(X37,X36)|X36!=X37))&(~r1_tarski(X36,X37)|~r1_tarski(X37,X36)|X36=X37)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.21/0.42  cnf(c_0_85, plain, (r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76, c_0_46]), c_0_30]), c_0_40]), c_0_41]), c_0_42]), c_0_43]), c_0_44])).
% 0.21/0.42  cnf(c_0_86, negated_conjecture, (esk7_0=k1_xboole_0|r2_hidden(esk6_0,esk7_0)), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 0.21/0.42  cnf(c_0_87, plain, (k5_xboole_0(k5_xboole_0(X1,X1),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79, c_0_74]), c_0_42]), c_0_43]), c_0_44])).
% 0.21/0.42  cnf(c_0_88, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_80])).
% 0.21/0.42  cnf(c_0_89, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81, c_0_39]), c_0_40]), c_0_41]), c_0_42]), c_0_43]), c_0_44])).
% 0.21/0.42  cnf(c_0_90, negated_conjecture, (r1_xboole_0(X1,esk7_0)|r2_hidden(esk3_2(X1,esk7_0),k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))), inference(spm,[status(thm)],[c_0_56, c_0_70])).
% 0.21/0.42  cnf(c_0_91, plain, (r1_tarski(k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),X1)), inference(rw,[status(thm)],[c_0_82, c_0_83])).
% 0.21/0.42  cnf(c_0_92, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_84])).
% 0.21/0.42  cnf(c_0_93, negated_conjecture, (esk7_0=k1_xboole_0|r1_tarski(k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),esk7_0)), inference(spm,[status(thm)],[c_0_85, c_0_86])).
% 0.21/0.42  fof(c_0_94, plain, ![X8, X9]:k5_xboole_0(X8,X9)=k5_xboole_0(X9,X8), inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).
% 0.21/0.42  cnf(c_0_95, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_87, c_0_88]), c_0_89])).
% 0.21/0.42  cnf(c_0_96, plain, (r2_hidden(esk3_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.21/0.42  cnf(c_0_97, negated_conjecture, (esk3_2(X1,esk7_0)=esk6_0|r1_xboole_0(X1,esk7_0)), inference(spm,[status(thm)],[c_0_58, c_0_90])).
% 0.21/0.42  cnf(c_0_98, negated_conjecture, (r1_tarski(k5_xboole_0(esk7_0,k5_xboole_0(esk8_0,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))),esk7_0)), inference(spm,[status(thm)],[c_0_91, c_0_50])).
% 0.21/0.42  cnf(c_0_99, negated_conjecture, (k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)=esk7_0|esk7_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_53])])).
% 0.21/0.42  cnf(c_0_100, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_94])).
% 0.21/0.42  cnf(c_0_101, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_88]), c_0_95])).
% 0.21/0.42  cnf(c_0_102, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.21/0.42  cnf(c_0_103, negated_conjecture, (r1_xboole_0(X1,esk7_0)|r2_hidden(esk6_0,X1)), inference(spm,[status(thm)],[c_0_96, c_0_97])).
% 0.21/0.42  cnf(c_0_104, negated_conjecture, (esk7_0=k1_xboole_0|r1_tarski(esk8_0,esk7_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_99]), c_0_100]), c_0_101])).
% 0.21/0.42  cnf(c_0_105, negated_conjecture, (r2_hidden(esk6_0,X1)|~r2_hidden(X2,esk7_0)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_102, c_0_103])).
% 0.21/0.42  cnf(c_0_106, negated_conjecture, (esk7_0=k1_xboole_0|r2_hidden(X1,esk7_0)|~r2_hidden(X1,esk8_0)), inference(spm,[status(thm)],[c_0_52, c_0_104])).
% 0.21/0.42  cnf(c_0_107, negated_conjecture, (r2_hidden(esk6_0,X1)|v1_xboole_0(X1)|~r2_hidden(esk1_1(X1),esk7_0)), inference(spm,[status(thm)],[c_0_105, c_0_57])).
% 0.21/0.42  cnf(c_0_108, negated_conjecture, (esk7_0=k1_xboole_0|r2_hidden(esk1_1(esk8_0),esk7_0)|v1_xboole_0(esk8_0)), inference(spm,[status(thm)],[c_0_106, c_0_57])).
% 0.21/0.42  cnf(c_0_109, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.21/0.42  cnf(c_0_110, negated_conjecture, (esk7_0=k1_xboole_0|r2_hidden(esk6_0,esk8_0)|v1_xboole_0(esk8_0)), inference(spm,[status(thm)],[c_0_107, c_0_108])).
% 0.21/0.42  cnf(c_0_111, negated_conjecture, (esk7_0!=k1_tarski(esk6_0)|esk8_0!=k1_tarski(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.21/0.42  cnf(c_0_112, negated_conjecture, (r1_tarski(esk7_0,X1)|r2_hidden(esk2_2(esk7_0,X1),k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))), inference(spm,[status(thm)],[c_0_56, c_0_109])).
% 0.21/0.42  cnf(c_0_113, negated_conjecture, (esk7_0=k1_xboole_0|r2_hidden(esk6_0,esk8_0)|~r2_hidden(X1,esk8_0)), inference(spm,[status(thm)],[c_0_62, c_0_110])).
% 0.21/0.42  cnf(c_0_114, negated_conjecture, (esk7_0!=k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)|esk8_0!=k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_111, c_0_46]), c_0_46]), c_0_30]), c_0_30]), c_0_40]), c_0_40]), c_0_41]), c_0_41]), c_0_42]), c_0_42]), c_0_43]), c_0_43]), c_0_44]), c_0_44])).
% 0.21/0.42  fof(c_0_115, plain, ![X38, X39]:(~r1_tarski(X38,X39)|k2_xboole_0(X38,X39)=X39), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.21/0.42  cnf(c_0_116, plain, (r1_tarski(X1,X2)|~r2_hidden(esk2_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.21/0.42  cnf(c_0_117, negated_conjecture, (esk2_2(esk7_0,X1)=esk6_0|r1_tarski(esk7_0,X1)), inference(spm,[status(thm)],[c_0_58, c_0_112])).
% 0.21/0.42  cnf(c_0_118, negated_conjecture, (esk7_0=k1_xboole_0|r1_xboole_0(X1,esk8_0)|r2_hidden(esk6_0,esk8_0)), inference(spm,[status(thm)],[c_0_113, c_0_70])).
% 0.21/0.42  cnf(c_0_119, negated_conjecture, (esk7_0=k1_xboole_0|esk8_0!=esk7_0), inference(spm,[status(thm)],[c_0_114, c_0_99])).
% 0.21/0.42  cnf(c_0_120, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_115])).
% 0.21/0.42  cnf(c_0_121, negated_conjecture, (esk7_0!=k1_tarski(esk6_0)|esk8_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.21/0.42  cnf(c_0_122, negated_conjecture, (r1_tarski(esk7_0,X1)|~r2_hidden(esk6_0,X1)), inference(spm,[status(thm)],[c_0_116, c_0_117])).
% 0.21/0.42  cnf(c_0_123, negated_conjecture, (esk7_0=k1_xboole_0|esk8_0=k1_xboole_0|r2_hidden(esk6_0,esk8_0)), inference(spm,[status(thm)],[c_0_77, c_0_118])).
% 0.21/0.42  cnf(c_0_124, negated_conjecture, (esk7_0=k1_xboole_0|~r1_tarski(esk7_0,esk8_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_104]), c_0_119])).
% 0.21/0.42  cnf(c_0_125, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))=X2|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_120, c_0_39]), c_0_40]), c_0_41]), c_0_42]), c_0_43]), c_0_44])).
% 0.21/0.42  cnf(c_0_126, negated_conjecture, (r1_tarski(esk7_0,X1)|r2_hidden(esk6_0,esk7_0)), inference(spm,[status(thm)],[c_0_69, c_0_109])).
% 0.21/0.42  cnf(c_0_127, plain, (r1_xboole_0(X1,X1)|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.21/0.42  cnf(c_0_128, negated_conjecture, (esk7_0!=k1_xboole_0|esk8_0!=k1_tarski(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.21/0.42  cnf(c_0_129, negated_conjecture, (esk8_0!=k1_xboole_0|esk7_0!=k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_121, c_0_46]), c_0_30]), c_0_40]), c_0_41]), c_0_42]), c_0_43]), c_0_44])).
% 0.21/0.42  cnf(c_0_130, negated_conjecture, (esk8_0=k1_xboole_0|esk7_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_122, c_0_123]), c_0_124])).
% 0.21/0.42  cnf(c_0_131, negated_conjecture, (k3_tarski(k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,X1))=X1|r2_hidden(esk6_0,esk7_0)), inference(spm,[status(thm)],[c_0_125, c_0_126])).
% 0.21/0.42  cnf(c_0_132, plain, (r1_xboole_0(k1_xboole_0,k1_xboole_0)), inference(er,[status(thm)],[c_0_127])).
% 0.21/0.42  cnf(c_0_133, negated_conjecture, (esk7_0!=k1_xboole_0|esk8_0!=k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_128, c_0_46]), c_0_30]), c_0_40]), c_0_41]), c_0_42]), c_0_43]), c_0_44])).
% 0.21/0.42  cnf(c_0_134, negated_conjecture, (esk7_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_129, c_0_130]), c_0_99])).
% 0.21/0.42  cnf(c_0_135, negated_conjecture, (k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)=esk8_0|r2_hidden(esk6_0,esk7_0)), inference(spm,[status(thm)],[c_0_50, c_0_131])).
% 0.21/0.42  cnf(c_0_136, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_102, c_0_132])).
% 0.21/0.42  cnf(c_0_137, negated_conjecture, (k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)!=esk8_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_133, c_0_134])])).
% 0.21/0.42  cnf(c_0_138, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_135, c_0_134]), c_0_136]), c_0_137]), ['proof']).
% 0.21/0.42  # SZS output end CNFRefutation
% 0.21/0.42  # Proof object total steps             : 139
% 0.21/0.42  # Proof object clause steps            : 88
% 0.21/0.42  # Proof object formula steps           : 51
% 0.21/0.42  # Proof object conjectures             : 46
% 0.21/0.42  # Proof object clause conjectures      : 43
% 0.21/0.42  # Proof object formula conjectures     : 3
% 0.21/0.42  # Proof object initial clauses used    : 34
% 0.21/0.42  # Proof object initial formulas used   : 25
% 0.21/0.42  # Proof object generating inferences   : 35
% 0.21/0.42  # Proof object simplifying inferences  : 103
% 0.21/0.42  # Training examples: 0 positive, 0 negative
% 0.21/0.42  # Parsed axioms                        : 27
% 0.21/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.42  # Initial clauses                      : 44
% 0.21/0.42  # Removed in clause preprocessing      : 9
% 0.21/0.42  # Initial clauses in saturation        : 35
% 0.21/0.42  # Processed clauses                    : 466
% 0.21/0.42  # ...of these trivial                  : 6
% 0.21/0.42  # ...subsumed                          : 224
% 0.21/0.42  # ...remaining for further processing  : 235
% 0.21/0.42  # Other redundant clauses eliminated   : 11
% 0.21/0.42  # Clauses deleted for lack of memory   : 0
% 0.21/0.42  # Backward-subsumed                    : 12
% 0.21/0.42  # Backward-rewritten                   : 119
% 0.21/0.42  # Generated clauses                    : 1538
% 0.21/0.42  # ...of the previous two non-trivial   : 1265
% 0.21/0.42  # Contextual simplify-reflections      : 3
% 0.21/0.42  # Paramodulations                      : 1528
% 0.21/0.42  # Factorizations                       : 0
% 0.21/0.42  # Equation resolutions                 : 11
% 0.21/0.42  # Propositional unsat checks           : 0
% 0.21/0.42  #    Propositional check models        : 0
% 0.21/0.42  #    Propositional check unsatisfiable : 0
% 0.21/0.42  #    Propositional clauses             : 0
% 0.21/0.42  #    Propositional clauses after purity: 0
% 0.21/0.42  #    Propositional unsat core size     : 0
% 0.21/0.42  #    Propositional preprocessing time  : 0.000
% 0.21/0.42  #    Propositional encoding time       : 0.000
% 0.21/0.42  #    Propositional solver time         : 0.000
% 0.21/0.42  #    Success case prop preproc time    : 0.000
% 0.21/0.42  #    Success case prop encoding time   : 0.000
% 0.21/0.42  #    Success case prop solver time     : 0.000
% 0.21/0.42  # Current number of processed clauses  : 65
% 0.21/0.42  #    Positive orientable unit clauses  : 26
% 0.21/0.42  #    Positive unorientable unit clauses: 3
% 0.21/0.42  #    Negative unit clauses             : 5
% 0.21/0.42  #    Non-unit-clauses                  : 31
% 0.21/0.42  # Current number of unprocessed clauses: 858
% 0.21/0.42  # ...number of literals in the above   : 2131
% 0.21/0.42  # Current number of archived formulas  : 0
% 0.21/0.42  # Current number of archived clauses   : 174
% 0.21/0.42  # Clause-clause subsumption calls (NU) : 2388
% 0.21/0.42  # Rec. Clause-clause subsumption calls : 1234
% 0.21/0.42  # Non-unit clause-clause subsumptions  : 192
% 0.21/0.42  # Unit Clause-clause subsumption calls : 18
% 0.21/0.42  # Rewrite failures with RHS unbound    : 0
% 0.21/0.42  # BW rewrite match attempts            : 70
% 0.21/0.42  # BW rewrite match successes           : 50
% 0.21/0.42  # Condensation attempts                : 0
% 0.21/0.42  # Condensation successes               : 0
% 0.21/0.42  # Termbank termtop insertions          : 22516
% 0.21/0.43  
% 0.21/0.43  # -------------------------------------------------
% 0.21/0.43  # User time                : 0.066 s
% 0.21/0.43  # System time              : 0.005 s
% 0.21/0.43  # Total time               : 0.070 s
% 0.21/0.43  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
