%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:39:51 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  123 (18144 expanded)
%              Number of clauses        :   74 (7042 expanded)
%              Number of leaves         :   24 (5459 expanded)
%              Depth                    :   22
%              Number of atoms          :  261 (26669 expanded)
%              Number of equality atoms :  161 (21741 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t43_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ~ ( k1_tarski(X1) = k2_xboole_0(X2,X3)
        & ~ ( X2 = k1_tarski(X1)
            & X3 = k1_tarski(X1) )
        & ~ ( X2 = k1_xboole_0
            & X3 = k1_tarski(X1) )
        & ~ ( X2 = k1_tarski(X1)
            & X3 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(l1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t95_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(t20_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
    <=> X1 != X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(c_0_24,plain,(
    ! [X89,X90] : k3_tarski(k2_tarski(X89,X90)) = k2_xboole_0(X89,X90) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_25,plain,(
    ! [X60,X61] : k1_enumset1(X60,X60,X61) = k2_tarski(X60,X61) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_26,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( k1_tarski(X1) = k2_xboole_0(X2,X3)
          & ~ ( X2 = k1_tarski(X1)
              & X3 = k1_tarski(X1) )
          & ~ ( X2 = k1_xboole_0
              & X3 = k1_tarski(X1) )
          & ~ ( X2 = k1_tarski(X1)
              & X3 = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t43_zfmisc_1])).

fof(c_0_27,plain,(
    ! [X36,X37] : r1_tarski(X36,k2_xboole_0(X36,X37)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_28,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_29,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_30,plain,(
    ! [X62,X63,X64] : k2_enumset1(X62,X62,X63,X64) = k1_enumset1(X62,X63,X64) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_31,plain,(
    ! [X65,X66,X67,X68] : k3_enumset1(X65,X65,X66,X67,X68) = k2_enumset1(X65,X66,X67,X68) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_32,plain,(
    ! [X69,X70,X71,X72,X73] : k4_enumset1(X69,X69,X70,X71,X72,X73) = k3_enumset1(X69,X70,X71,X72,X73) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_33,plain,(
    ! [X74,X75,X76,X77,X78,X79] : k5_enumset1(X74,X74,X75,X76,X77,X78,X79) = k4_enumset1(X74,X75,X76,X77,X78,X79) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_34,plain,(
    ! [X80,X81,X82,X83,X84,X85,X86] : k6_enumset1(X80,X80,X81,X82,X83,X84,X85,X86) = k5_enumset1(X80,X81,X82,X83,X84,X85,X86) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_35,negated_conjecture,
    ( k1_tarski(esk5_0) = k2_xboole_0(esk6_0,esk7_0)
    & ( esk6_0 != k1_tarski(esk5_0)
      | esk7_0 != k1_tarski(esk5_0) )
    & ( esk6_0 != k1_xboole_0
      | esk7_0 != k1_tarski(esk5_0) )
    & ( esk6_0 != k1_tarski(esk5_0)
      | esk7_0 != k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_26])])])).

fof(c_0_36,plain,(
    ! [X59] : k2_tarski(X59,X59) = k1_tarski(X59) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_37,plain,(
    ! [X44,X45,X46,X47,X48,X49] :
      ( ( ~ r2_hidden(X46,X45)
        | X46 = X44
        | X45 != k1_tarski(X44) )
      & ( X47 != X44
        | r2_hidden(X47,X45)
        | X45 != k1_tarski(X44) )
      & ( ~ r2_hidden(esk4_2(X48,X49),X49)
        | esk4_2(X48,X49) != X48
        | X49 = k1_tarski(X48) )
      & ( r2_hidden(esk4_2(X48,X49),X49)
        | esk4_2(X48,X49) = X48
        | X49 = k1_tarski(X48) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_38,plain,(
    ! [X9,X10,X11,X12,X13] :
      ( ( ~ r1_tarski(X9,X10)
        | ~ r2_hidden(X11,X9)
        | r2_hidden(X11,X10) )
      & ( r2_hidden(esk1_2(X12,X13),X12)
        | r1_tarski(X12,X13) )
      & ( ~ r2_hidden(esk1_2(X12,X13),X13)
        | r1_tarski(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_39,plain,(
    ! [X25] :
      ( X25 = k1_xboole_0
      | r2_hidden(esk3_1(X25),X25) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_41,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_42,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_43,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_44,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_45,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_46,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_47,negated_conjecture,
    ( k1_tarski(esk5_0) = k2_xboole_0(esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_48,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_49,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_50,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_51,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk3_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_52,plain,
    ( r1_tarski(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_41]),c_0_42]),c_0_43]),c_0_44]),c_0_45]),c_0_46])).

cnf(c_0_53,negated_conjecture,
    ( k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) = k3_tarski(k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk7_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_48]),c_0_29]),c_0_41]),c_0_42]),c_0_42]),c_0_43]),c_0_43]),c_0_44]),c_0_44]),c_0_45]),c_0_45]),c_0_46]),c_0_46])).

cnf(c_0_54,plain,
    ( X1 = X3
    | X2 != k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_48]),c_0_29]),c_0_42]),c_0_43]),c_0_44]),c_0_45]),c_0_46])).

cnf(c_0_55,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk3_1(X1),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_56,negated_conjecture,
    ( r1_tarski(esk6_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

fof(c_0_57,plain,(
    ! [X87,X88] :
      ( ( ~ r1_tarski(k1_tarski(X87),X88)
        | r2_hidden(X87,X88) )
      & ( ~ r2_hidden(X87,X88)
        | r1_tarski(k1_tarski(X87),X88) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).

cnf(c_0_58,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_54])).

cnf(c_0_59,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r2_hidden(esk3_1(esk6_0),k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

fof(c_0_60,plain,(
    ! [X15,X16,X17,X18,X19,X20,X21,X22] :
      ( ( ~ r2_hidden(X18,X17)
        | r2_hidden(X18,X15)
        | r2_hidden(X18,X16)
        | X17 != k2_xboole_0(X15,X16) )
      & ( ~ r2_hidden(X19,X15)
        | r2_hidden(X19,X17)
        | X17 != k2_xboole_0(X15,X16) )
      & ( ~ r2_hidden(X19,X16)
        | r2_hidden(X19,X17)
        | X17 != k2_xboole_0(X15,X16) )
      & ( ~ r2_hidden(esk2_3(X20,X21,X22),X20)
        | ~ r2_hidden(esk2_3(X20,X21,X22),X22)
        | X22 = k2_xboole_0(X20,X21) )
      & ( ~ r2_hidden(esk2_3(X20,X21,X22),X21)
        | ~ r2_hidden(esk2_3(X20,X21,X22),X22)
        | X22 = k2_xboole_0(X20,X21) )
      & ( r2_hidden(esk2_3(X20,X21,X22),X22)
        | r2_hidden(esk2_3(X20,X21,X22),X20)
        | r2_hidden(esk2_3(X20,X21,X22),X21)
        | X22 = k2_xboole_0(X20,X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

cnf(c_0_61,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_62,negated_conjecture,
    ( esk3_1(esk6_0) = esk5_0
    | esk6_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_63,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

fof(c_0_64,plain,(
    ! [X27,X28] :
      ( ( r1_tarski(X27,X28)
        | X27 != X28 )
      & ( r1_tarski(X28,X27)
        | X27 != X28 )
      & ( ~ r1_tarski(X27,X28)
        | ~ r1_tarski(X28,X27)
        | X27 = X28 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_65,plain,
    ( r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_48]),c_0_29]),c_0_42]),c_0_43]),c_0_44]),c_0_45]),c_0_46])).

cnf(c_0_66,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r2_hidden(esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_62])).

cnf(c_0_67,plain,
    ( r2_hidden(X1,X3)
    | X3 != k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X2))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_41]),c_0_42]),c_0_43]),c_0_44]),c_0_45]),c_0_46])).

cnf(c_0_68,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_69,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r1_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_70,plain,
    ( r2_hidden(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_67])).

cnf(c_0_71,negated_conjecture,
    ( k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) = esk6_0
    | esk6_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_56])])).

cnf(c_0_72,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk3_1(X1),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
    inference(spm,[status(thm)],[c_0_70,c_0_51])).

cnf(c_0_73,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | X1 = esk5_0
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_71])).

cnf(c_0_74,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_75,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r2_hidden(esk3_1(esk7_0),k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_53])).

fof(c_0_76,plain,(
    ! [X31,X32] :
      ( ~ r1_tarski(X31,X32)
      | k2_xboole_0(X31,X32) = X32 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_77,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_78,negated_conjecture,
    ( esk1_2(esk6_0,X1) = esk5_0
    | esk6_0 = k1_xboole_0
    | r1_tarski(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_79,negated_conjecture,
    ( esk3_1(esk7_0) = esk5_0
    | esk7_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_58,c_0_75])).

cnf(c_0_80,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_81,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r1_tarski(esk6_0,X1)
    | ~ r2_hidden(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_82,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r2_hidden(esk5_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_79])).

cnf(c_0_83,negated_conjecture,
    ( esk6_0 != k1_tarski(esk5_0)
    | esk7_0 != k1_tarski(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_84,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_41]),c_0_42]),c_0_43]),c_0_44]),c_0_45]),c_0_46])).

cnf(c_0_85,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | r1_tarski(esk6_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_86,negated_conjecture,
    ( esk6_0 != k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)
    | esk7_0 != k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_83,c_0_48]),c_0_48]),c_0_29]),c_0_29]),c_0_42]),c_0_42]),c_0_43]),c_0_43]),c_0_44]),c_0_44]),c_0_45]),c_0_45]),c_0_46]),c_0_46])).

cnf(c_0_87,negated_conjecture,
    ( esk6_0 != k1_tarski(esk5_0)
    | esk7_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_88,negated_conjecture,
    ( k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) = esk7_0
    | esk6_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_53])).

cnf(c_0_89,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk7_0 != esk6_0 ),
    inference(spm,[status(thm)],[c_0_86,c_0_71])).

cnf(c_0_90,negated_conjecture,
    ( esk7_0 != k1_xboole_0
    | esk6_0 != k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_87,c_0_48]),c_0_29]),c_0_42]),c_0_43]),c_0_44]),c_0_45]),c_0_46])).

cnf(c_0_91,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_88]),c_0_89])).

cnf(c_0_92,negated_conjecture,
    ( esk6_0 != k1_xboole_0
    | esk7_0 != k1_tarski(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_93,negated_conjecture,
    ( esk6_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_71])).

fof(c_0_94,plain,(
    ! [X42,X43] : k3_xboole_0(X42,X43) = k5_xboole_0(k5_xboole_0(X42,X43),k2_xboole_0(X42,X43)) ),
    inference(variable_rename,[status(thm)],[t95_xboole_1])).

cnf(c_0_95,plain,
    ( X1 = k1_xboole_0
    | r1_tarski(k6_enumset1(esk3_1(X1),esk3_1(X1),esk3_1(X1),esk3_1(X1),esk3_1(X1),esk3_1(X1),esk3_1(X1),esk3_1(X1)),X1) ),
    inference(spm,[status(thm)],[c_0_65,c_0_51])).

cnf(c_0_96,negated_conjecture,
    ( esk6_0 != k1_xboole_0
    | esk7_0 != k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_92,c_0_48]),c_0_29]),c_0_42]),c_0_43]),c_0_44]),c_0_45]),c_0_46])).

cnf(c_0_97,plain,
    ( r2_hidden(esk1_2(X1,X2),k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X1)))
    | r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_70,c_0_74])).

cnf(c_0_98,negated_conjecture,
    ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,esk7_0)) = k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_93]),c_0_93]),c_0_93]),c_0_93]),c_0_93]),c_0_93]),c_0_93])).

fof(c_0_99,plain,(
    ! [X91,X92] :
      ( ( k4_xboole_0(k1_tarski(X91),k1_tarski(X92)) != k1_tarski(X91)
        | X91 != X92 )
      & ( X91 = X92
        | k4_xboole_0(k1_tarski(X91),k1_tarski(X92)) = k1_tarski(X91) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_zfmisc_1])])).

fof(c_0_100,plain,(
    ! [X29,X30] : k4_xboole_0(X29,X30) = k5_xboole_0(X29,k3_xboole_0(X29,X30)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_101,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_94])).

fof(c_0_102,plain,(
    ! [X24] : k2_xboole_0(X24,X24) = X24 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

cnf(c_0_103,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r1_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_95,c_0_79])).

cnf(c_0_104,negated_conjecture,
    ( k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) != esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_96,c_0_93])])).

cnf(c_0_105,negated_conjecture,
    ( r2_hidden(esk1_2(esk7_0,X1),k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))
    | r1_tarski(esk7_0,X1) ),
    inference(spm,[status(thm)],[c_0_97,c_0_98])).

cnf(c_0_106,plain,
    ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) != k1_tarski(X1)
    | X1 != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_99])).

cnf(c_0_107,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_100])).

cnf(c_0_108,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_101,c_0_41]),c_0_42]),c_0_43])).

fof(c_0_109,plain,(
    ! [X38,X39,X40] : k5_xboole_0(k5_xboole_0(X38,X39),X40) = k5_xboole_0(X38,k5_xboole_0(X39,X40)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_110,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_102])).

fof(c_0_111,plain,(
    ! [X41] : k5_xboole_0(X41,X41) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

fof(c_0_112,plain,(
    ! [X35] : k5_xboole_0(X35,k1_xboole_0) = X35 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

cnf(c_0_113,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | ~ r1_tarski(esk7_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_103]),c_0_104])).

cnf(c_0_114,negated_conjecture,
    ( r1_tarski(esk7_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_77,c_0_105])).

cnf(c_0_115,plain,
    ( X1 != X2
    | k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k5_xboole_0(k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)),k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))))) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_106,c_0_48]),c_0_48]),c_0_48]),c_0_29]),c_0_29]),c_0_29]),c_0_107]),c_0_42]),c_0_42]),c_0_42]),c_0_42]),c_0_43]),c_0_43]),c_0_43]),c_0_43]),c_0_108]),c_0_44]),c_0_44]),c_0_44]),c_0_44]),c_0_44]),c_0_44]),c_0_44]),c_0_44]),c_0_44]),c_0_44]),c_0_45]),c_0_45]),c_0_45]),c_0_45]),c_0_45]),c_0_45]),c_0_45]),c_0_45]),c_0_45]),c_0_45]),c_0_45]),c_0_46]),c_0_46]),c_0_46]),c_0_46]),c_0_46]),c_0_46]),c_0_46]),c_0_46]),c_0_46]),c_0_46]),c_0_46]),c_0_46])).

cnf(c_0_116,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_109])).

cnf(c_0_117,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_110,c_0_41]),c_0_42]),c_0_43]),c_0_44]),c_0_45]),c_0_46])).

cnf(c_0_118,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_111])).

cnf(c_0_119,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_112])).

cnf(c_0_120,negated_conjecture,
    ( esk7_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_113,c_0_114])])).

cnf(c_0_121,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(rw,[status(thm)],[c_0_115,c_0_116])]),c_0_117]),c_0_118]),c_0_119]),c_0_118])).

cnf(c_0_122,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_98,c_0_120]),c_0_117]),c_0_121]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:49:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.46  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S054N
% 0.21/0.46  # and selection function GSelectMinInfpos.
% 0.21/0.46  #
% 0.21/0.46  # Preprocessing time       : 0.028 s
% 0.21/0.46  # Presaturation interreduction done
% 0.21/0.46  
% 0.21/0.46  # Proof found!
% 0.21/0.46  # SZS status Theorem
% 0.21/0.46  # SZS output start CNFRefutation
% 0.21/0.46  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.21/0.46  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.21/0.46  fof(t43_zfmisc_1, conjecture, ![X1, X2, X3]:~((((k1_tarski(X1)=k2_xboole_0(X2,X3)&~((X2=k1_tarski(X1)&X3=k1_tarski(X1))))&~((X2=k1_xboole_0&X3=k1_tarski(X1))))&~((X2=k1_tarski(X1)&X3=k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 0.21/0.46  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.21/0.46  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.21/0.46  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.21/0.46  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.21/0.46  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.21/0.46  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 0.21/0.46  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.21/0.46  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 0.21/0.46  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.21/0.46  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.21/0.46  fof(l1_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 0.21/0.46  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 0.21/0.46  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.21/0.46  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.21/0.46  fof(t95_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 0.21/0.46  fof(t20_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)<=>X1!=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 0.21/0.46  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.21/0.46  fof(idempotence_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 0.21/0.46  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.21/0.46  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 0.21/0.46  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 0.21/0.46  fof(c_0_24, plain, ![X89, X90]:k3_tarski(k2_tarski(X89,X90))=k2_xboole_0(X89,X90), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.21/0.46  fof(c_0_25, plain, ![X60, X61]:k1_enumset1(X60,X60,X61)=k2_tarski(X60,X61), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.21/0.46  fof(c_0_26, negated_conjecture, ~(![X1, X2, X3]:~((((k1_tarski(X1)=k2_xboole_0(X2,X3)&~((X2=k1_tarski(X1)&X3=k1_tarski(X1))))&~((X2=k1_xboole_0&X3=k1_tarski(X1))))&~((X2=k1_tarski(X1)&X3=k1_xboole_0))))), inference(assume_negation,[status(cth)],[t43_zfmisc_1])).
% 0.21/0.46  fof(c_0_27, plain, ![X36, X37]:r1_tarski(X36,k2_xboole_0(X36,X37)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.21/0.46  cnf(c_0_28, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.21/0.46  cnf(c_0_29, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.46  fof(c_0_30, plain, ![X62, X63, X64]:k2_enumset1(X62,X62,X63,X64)=k1_enumset1(X62,X63,X64), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.21/0.46  fof(c_0_31, plain, ![X65, X66, X67, X68]:k3_enumset1(X65,X65,X66,X67,X68)=k2_enumset1(X65,X66,X67,X68), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.21/0.46  fof(c_0_32, plain, ![X69, X70, X71, X72, X73]:k4_enumset1(X69,X69,X70,X71,X72,X73)=k3_enumset1(X69,X70,X71,X72,X73), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.21/0.46  fof(c_0_33, plain, ![X74, X75, X76, X77, X78, X79]:k5_enumset1(X74,X74,X75,X76,X77,X78,X79)=k4_enumset1(X74,X75,X76,X77,X78,X79), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.21/0.46  fof(c_0_34, plain, ![X80, X81, X82, X83, X84, X85, X86]:k6_enumset1(X80,X80,X81,X82,X83,X84,X85,X86)=k5_enumset1(X80,X81,X82,X83,X84,X85,X86), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.21/0.46  fof(c_0_35, negated_conjecture, (((k1_tarski(esk5_0)=k2_xboole_0(esk6_0,esk7_0)&(esk6_0!=k1_tarski(esk5_0)|esk7_0!=k1_tarski(esk5_0)))&(esk6_0!=k1_xboole_0|esk7_0!=k1_tarski(esk5_0)))&(esk6_0!=k1_tarski(esk5_0)|esk7_0!=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_26])])])).
% 0.21/0.46  fof(c_0_36, plain, ![X59]:k2_tarski(X59,X59)=k1_tarski(X59), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.21/0.46  fof(c_0_37, plain, ![X44, X45, X46, X47, X48, X49]:(((~r2_hidden(X46,X45)|X46=X44|X45!=k1_tarski(X44))&(X47!=X44|r2_hidden(X47,X45)|X45!=k1_tarski(X44)))&((~r2_hidden(esk4_2(X48,X49),X49)|esk4_2(X48,X49)!=X48|X49=k1_tarski(X48))&(r2_hidden(esk4_2(X48,X49),X49)|esk4_2(X48,X49)=X48|X49=k1_tarski(X48)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.21/0.46  fof(c_0_38, plain, ![X9, X10, X11, X12, X13]:((~r1_tarski(X9,X10)|(~r2_hidden(X11,X9)|r2_hidden(X11,X10)))&((r2_hidden(esk1_2(X12,X13),X12)|r1_tarski(X12,X13))&(~r2_hidden(esk1_2(X12,X13),X13)|r1_tarski(X12,X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.21/0.46  fof(c_0_39, plain, ![X25]:(X25=k1_xboole_0|r2_hidden(esk3_1(X25),X25)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.21/0.46  cnf(c_0_40, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.21/0.46  cnf(c_0_41, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_28, c_0_29])).
% 0.21/0.46  cnf(c_0_42, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.21/0.46  cnf(c_0_43, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.21/0.46  cnf(c_0_44, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.21/0.46  cnf(c_0_45, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.21/0.46  cnf(c_0_46, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.21/0.46  cnf(c_0_47, negated_conjecture, (k1_tarski(esk5_0)=k2_xboole_0(esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.21/0.46  cnf(c_0_48, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.21/0.46  cnf(c_0_49, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.21/0.46  cnf(c_0_50, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.21/0.46  cnf(c_0_51, plain, (X1=k1_xboole_0|r2_hidden(esk3_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.21/0.46  cnf(c_0_52, plain, (r1_tarski(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_41]), c_0_42]), c_0_43]), c_0_44]), c_0_45]), c_0_46])).
% 0.21/0.46  cnf(c_0_53, negated_conjecture, (k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)=k3_tarski(k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk7_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_48]), c_0_29]), c_0_41]), c_0_42]), c_0_42]), c_0_43]), c_0_43]), c_0_44]), c_0_44]), c_0_45]), c_0_45]), c_0_46]), c_0_46])).
% 0.21/0.46  cnf(c_0_54, plain, (X1=X3|X2!=k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_48]), c_0_29]), c_0_42]), c_0_43]), c_0_44]), c_0_45]), c_0_46])).
% 0.21/0.46  cnf(c_0_55, plain, (X1=k1_xboole_0|r2_hidden(esk3_1(X1),X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.21/0.46  cnf(c_0_56, negated_conjecture, (r1_tarski(esk6_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.21/0.46  fof(c_0_57, plain, ![X87, X88]:((~r1_tarski(k1_tarski(X87),X88)|r2_hidden(X87,X88))&(~r2_hidden(X87,X88)|r1_tarski(k1_tarski(X87),X88))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).
% 0.21/0.46  cnf(c_0_58, plain, (X1=X2|~r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_54])).
% 0.21/0.46  cnf(c_0_59, negated_conjecture, (esk6_0=k1_xboole_0|r2_hidden(esk3_1(esk6_0),k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.21/0.46  fof(c_0_60, plain, ![X15, X16, X17, X18, X19, X20, X21, X22]:(((~r2_hidden(X18,X17)|(r2_hidden(X18,X15)|r2_hidden(X18,X16))|X17!=k2_xboole_0(X15,X16))&((~r2_hidden(X19,X15)|r2_hidden(X19,X17)|X17!=k2_xboole_0(X15,X16))&(~r2_hidden(X19,X16)|r2_hidden(X19,X17)|X17!=k2_xboole_0(X15,X16))))&(((~r2_hidden(esk2_3(X20,X21,X22),X20)|~r2_hidden(esk2_3(X20,X21,X22),X22)|X22=k2_xboole_0(X20,X21))&(~r2_hidden(esk2_3(X20,X21,X22),X21)|~r2_hidden(esk2_3(X20,X21,X22),X22)|X22=k2_xboole_0(X20,X21)))&(r2_hidden(esk2_3(X20,X21,X22),X22)|(r2_hidden(esk2_3(X20,X21,X22),X20)|r2_hidden(esk2_3(X20,X21,X22),X21))|X22=k2_xboole_0(X20,X21)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 0.21/0.46  cnf(c_0_61, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.21/0.46  cnf(c_0_62, negated_conjecture, (esk3_1(esk6_0)=esk5_0|esk6_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.21/0.46  cnf(c_0_63, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.21/0.46  fof(c_0_64, plain, ![X27, X28]:(((r1_tarski(X27,X28)|X27!=X28)&(r1_tarski(X28,X27)|X27!=X28))&(~r1_tarski(X27,X28)|~r1_tarski(X28,X27)|X27=X28)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.21/0.46  cnf(c_0_65, plain, (r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_48]), c_0_29]), c_0_42]), c_0_43]), c_0_44]), c_0_45]), c_0_46])).
% 0.21/0.46  cnf(c_0_66, negated_conjecture, (esk6_0=k1_xboole_0|r2_hidden(esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_51, c_0_62])).
% 0.21/0.46  cnf(c_0_67, plain, (r2_hidden(X1,X3)|X3!=k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X2))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_41]), c_0_42]), c_0_43]), c_0_44]), c_0_45]), c_0_46])).
% 0.21/0.46  cnf(c_0_68, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.21/0.46  cnf(c_0_69, negated_conjecture, (esk6_0=k1_xboole_0|r1_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk6_0)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.21/0.46  cnf(c_0_70, plain, (r2_hidden(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_67])).
% 0.21/0.46  cnf(c_0_71, negated_conjecture, (k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)=esk6_0|esk6_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_56])])).
% 0.21/0.46  cnf(c_0_72, plain, (X1=k1_xboole_0|r2_hidden(esk3_1(X1),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)))), inference(spm,[status(thm)],[c_0_70, c_0_51])).
% 0.21/0.46  cnf(c_0_73, negated_conjecture, (esk6_0=k1_xboole_0|X1=esk5_0|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_58, c_0_71])).
% 0.21/0.46  cnf(c_0_74, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.21/0.46  cnf(c_0_75, negated_conjecture, (esk7_0=k1_xboole_0|r2_hidden(esk3_1(esk7_0),k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))), inference(spm,[status(thm)],[c_0_72, c_0_53])).
% 0.21/0.46  fof(c_0_76, plain, ![X31, X32]:(~r1_tarski(X31,X32)|k2_xboole_0(X31,X32)=X32), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.21/0.46  cnf(c_0_77, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.21/0.46  cnf(c_0_78, negated_conjecture, (esk1_2(esk6_0,X1)=esk5_0|esk6_0=k1_xboole_0|r1_tarski(esk6_0,X1)), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.21/0.46  cnf(c_0_79, negated_conjecture, (esk3_1(esk7_0)=esk5_0|esk7_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_58, c_0_75])).
% 0.21/0.46  cnf(c_0_80, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_76])).
% 0.21/0.46  cnf(c_0_81, negated_conjecture, (esk6_0=k1_xboole_0|r1_tarski(esk6_0,X1)|~r2_hidden(esk5_0,X1)), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 0.21/0.46  cnf(c_0_82, negated_conjecture, (esk7_0=k1_xboole_0|r2_hidden(esk5_0,esk7_0)), inference(spm,[status(thm)],[c_0_51, c_0_79])).
% 0.21/0.46  cnf(c_0_83, negated_conjecture, (esk6_0!=k1_tarski(esk5_0)|esk7_0!=k1_tarski(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.21/0.46  cnf(c_0_84, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))=X2|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80, c_0_41]), c_0_42]), c_0_43]), c_0_44]), c_0_45]), c_0_46])).
% 0.21/0.46  cnf(c_0_85, negated_conjecture, (esk7_0=k1_xboole_0|esk6_0=k1_xboole_0|r1_tarski(esk6_0,esk7_0)), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 0.21/0.46  cnf(c_0_86, negated_conjecture, (esk6_0!=k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)|esk7_0!=k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_83, c_0_48]), c_0_48]), c_0_29]), c_0_29]), c_0_42]), c_0_42]), c_0_43]), c_0_43]), c_0_44]), c_0_44]), c_0_45]), c_0_45]), c_0_46]), c_0_46])).
% 0.21/0.46  cnf(c_0_87, negated_conjecture, (esk6_0!=k1_tarski(esk5_0)|esk7_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.21/0.46  cnf(c_0_88, negated_conjecture, (k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)=esk7_0|esk6_0=k1_xboole_0|esk7_0=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_53])).
% 0.21/0.46  cnf(c_0_89, negated_conjecture, (esk6_0=k1_xboole_0|esk7_0!=esk6_0), inference(spm,[status(thm)],[c_0_86, c_0_71])).
% 0.21/0.46  cnf(c_0_90, negated_conjecture, (esk7_0!=k1_xboole_0|esk6_0!=k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_87, c_0_48]), c_0_29]), c_0_42]), c_0_43]), c_0_44]), c_0_45]), c_0_46])).
% 0.21/0.46  cnf(c_0_91, negated_conjecture, (esk7_0=k1_xboole_0|esk6_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_88]), c_0_89])).
% 0.21/0.46  cnf(c_0_92, negated_conjecture, (esk6_0!=k1_xboole_0|esk7_0!=k1_tarski(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.21/0.46  cnf(c_0_93, negated_conjecture, (esk6_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_91]), c_0_71])).
% 0.21/0.46  fof(c_0_94, plain, ![X42, X43]:k3_xboole_0(X42,X43)=k5_xboole_0(k5_xboole_0(X42,X43),k2_xboole_0(X42,X43)), inference(variable_rename,[status(thm)],[t95_xboole_1])).
% 0.21/0.46  cnf(c_0_95, plain, (X1=k1_xboole_0|r1_tarski(k6_enumset1(esk3_1(X1),esk3_1(X1),esk3_1(X1),esk3_1(X1),esk3_1(X1),esk3_1(X1),esk3_1(X1),esk3_1(X1)),X1)), inference(spm,[status(thm)],[c_0_65, c_0_51])).
% 0.21/0.46  cnf(c_0_96, negated_conjecture, (esk6_0!=k1_xboole_0|esk7_0!=k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_92, c_0_48]), c_0_29]), c_0_42]), c_0_43]), c_0_44]), c_0_45]), c_0_46])).
% 0.21/0.46  cnf(c_0_97, plain, (r2_hidden(esk1_2(X1,X2),k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X1)))|r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_70, c_0_74])).
% 0.21/0.46  cnf(c_0_98, negated_conjecture, (k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,esk7_0))=k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_93]), c_0_93]), c_0_93]), c_0_93]), c_0_93]), c_0_93]), c_0_93])).
% 0.21/0.46  fof(c_0_99, plain, ![X91, X92]:((k4_xboole_0(k1_tarski(X91),k1_tarski(X92))!=k1_tarski(X91)|X91!=X92)&(X91=X92|k4_xboole_0(k1_tarski(X91),k1_tarski(X92))=k1_tarski(X91))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_zfmisc_1])])).
% 0.21/0.46  fof(c_0_100, plain, ![X29, X30]:k4_xboole_0(X29,X30)=k5_xboole_0(X29,k3_xboole_0(X29,X30)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.21/0.46  cnf(c_0_101, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_94])).
% 0.21/0.46  fof(c_0_102, plain, ![X24]:k2_xboole_0(X24,X24)=X24, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).
% 0.21/0.46  cnf(c_0_103, negated_conjecture, (esk7_0=k1_xboole_0|r1_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk7_0)), inference(spm,[status(thm)],[c_0_95, c_0_79])).
% 0.21/0.46  cnf(c_0_104, negated_conjecture, (k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)!=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_96, c_0_93])])).
% 0.21/0.46  cnf(c_0_105, negated_conjecture, (r2_hidden(esk1_2(esk7_0,X1),k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))|r1_tarski(esk7_0,X1)), inference(spm,[status(thm)],[c_0_97, c_0_98])).
% 0.21/0.46  cnf(c_0_106, plain, (k4_xboole_0(k1_tarski(X1),k1_tarski(X2))!=k1_tarski(X1)|X1!=X2), inference(split_conjunct,[status(thm)],[c_0_99])).
% 0.21/0.46  cnf(c_0_107, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_100])).
% 0.21/0.46  cnf(c_0_108, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_101, c_0_41]), c_0_42]), c_0_43])).
% 0.21/0.46  fof(c_0_109, plain, ![X38, X39, X40]:k5_xboole_0(k5_xboole_0(X38,X39),X40)=k5_xboole_0(X38,k5_xboole_0(X39,X40)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.21/0.46  cnf(c_0_110, plain, (k2_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_102])).
% 0.21/0.46  fof(c_0_111, plain, ![X41]:k5_xboole_0(X41,X41)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 0.21/0.46  fof(c_0_112, plain, ![X35]:k5_xboole_0(X35,k1_xboole_0)=X35, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.21/0.46  cnf(c_0_113, negated_conjecture, (esk7_0=k1_xboole_0|~r1_tarski(esk7_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_103]), c_0_104])).
% 0.21/0.46  cnf(c_0_114, negated_conjecture, (r1_tarski(esk7_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))), inference(spm,[status(thm)],[c_0_77, c_0_105])).
% 0.21/0.46  cnf(c_0_115, plain, (X1!=X2|k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k5_xboole_0(k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)),k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)))))!=k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_106, c_0_48]), c_0_48]), c_0_48]), c_0_29]), c_0_29]), c_0_29]), c_0_107]), c_0_42]), c_0_42]), c_0_42]), c_0_42]), c_0_43]), c_0_43]), c_0_43]), c_0_43]), c_0_108]), c_0_44]), c_0_44]), c_0_44]), c_0_44]), c_0_44]), c_0_44]), c_0_44]), c_0_44]), c_0_44]), c_0_44]), c_0_45]), c_0_45]), c_0_45]), c_0_45]), c_0_45]), c_0_45]), c_0_45]), c_0_45]), c_0_45]), c_0_45]), c_0_45]), c_0_46]), c_0_46]), c_0_46]), c_0_46]), c_0_46]), c_0_46]), c_0_46]), c_0_46]), c_0_46]), c_0_46]), c_0_46]), c_0_46])).
% 0.21/0.46  cnf(c_0_116, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_109])).
% 0.21/0.46  cnf(c_0_117, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_110, c_0_41]), c_0_42]), c_0_43]), c_0_44]), c_0_45]), c_0_46])).
% 0.21/0.46  cnf(c_0_118, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_111])).
% 0.21/0.46  cnf(c_0_119, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_112])).
% 0.21/0.46  cnf(c_0_120, negated_conjecture, (esk7_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_113, c_0_114])])).
% 0.21/0.46  cnf(c_0_121, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(rw,[status(thm)],[c_0_115, c_0_116])]), c_0_117]), c_0_118]), c_0_119]), c_0_118])).
% 0.21/0.46  cnf(c_0_122, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_98, c_0_120]), c_0_117]), c_0_121]), ['proof']).
% 0.21/0.46  # SZS output end CNFRefutation
% 0.21/0.46  # Proof object total steps             : 123
% 0.21/0.46  # Proof object clause steps            : 74
% 0.21/0.46  # Proof object formula steps           : 49
% 0.21/0.46  # Proof object conjectures             : 36
% 0.21/0.46  # Proof object clause conjectures      : 33
% 0.21/0.46  # Proof object formula conjectures     : 3
% 0.21/0.46  # Proof object initial clauses used    : 29
% 0.21/0.46  # Proof object initial formulas used   : 24
% 0.21/0.46  # Proof object generating inferences   : 25
% 0.21/0.46  # Proof object simplifying inferences  : 160
% 0.21/0.46  # Training examples: 0 positive, 0 negative
% 0.21/0.46  # Parsed axioms                        : 26
% 0.21/0.46  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.46  # Initial clauses                      : 43
% 0.21/0.46  # Removed in clause preprocessing      : 10
% 0.21/0.46  # Initial clauses in saturation        : 33
% 0.21/0.46  # Processed clauses                    : 542
% 0.21/0.46  # ...of these trivial                  : 4
% 0.21/0.46  # ...subsumed                          : 287
% 0.21/0.46  # ...remaining for further processing  : 251
% 0.21/0.46  # Other redundant clauses eliminated   : 38
% 0.21/0.46  # Clauses deleted for lack of memory   : 0
% 0.21/0.46  # Backward-subsumed                    : 12
% 0.21/0.46  # Backward-rewritten                   : 117
% 0.21/0.46  # Generated clauses                    : 2576
% 0.21/0.46  # ...of the previous two non-trivial   : 2386
% 0.21/0.46  # Contextual simplify-reflections      : 2
% 0.21/0.46  # Paramodulations                      : 2519
% 0.21/0.46  # Factorizations                       : 20
% 0.21/0.46  # Equation resolutions                 : 38
% 0.21/0.46  # Propositional unsat checks           : 0
% 0.21/0.46  #    Propositional check models        : 0
% 0.21/0.46  #    Propositional check unsatisfiable : 0
% 0.21/0.46  #    Propositional clauses             : 0
% 0.21/0.46  #    Propositional clauses after purity: 0
% 0.21/0.46  #    Propositional unsat core size     : 0
% 0.21/0.46  #    Propositional preprocessing time  : 0.000
% 0.21/0.46  #    Propositional encoding time       : 0.000
% 0.21/0.46  #    Propositional solver time         : 0.000
% 0.21/0.46  #    Success case prop preproc time    : 0.000
% 0.21/0.46  #    Success case prop encoding time   : 0.000
% 0.21/0.46  #    Success case prop solver time     : 0.000
% 0.21/0.46  # Current number of processed clauses  : 82
% 0.21/0.46  #    Positive orientable unit clauses  : 20
% 0.21/0.46  #    Positive unorientable unit clauses: 1
% 0.21/0.46  #    Negative unit clauses             : 3
% 0.21/0.46  #    Non-unit-clauses                  : 58
% 0.21/0.46  # Current number of unprocessed clauses: 1786
% 0.21/0.46  # ...number of literals in the above   : 7446
% 0.21/0.46  # Current number of archived formulas  : 0
% 0.21/0.46  # Current number of archived clauses   : 171
% 0.21/0.46  # Clause-clause subsumption calls (NU) : 3791
% 0.21/0.46  # Rec. Clause-clause subsumption calls : 1640
% 0.21/0.46  # Non-unit clause-clause subsumptions  : 290
% 0.21/0.46  # Unit Clause-clause subsumption calls : 54
% 0.21/0.46  # Rewrite failures with RHS unbound    : 0
% 0.21/0.46  # BW rewrite match attempts            : 71
% 0.21/0.46  # BW rewrite match successes           : 35
% 0.21/0.46  # Condensation attempts                : 0
% 0.21/0.46  # Condensation successes               : 0
% 0.21/0.46  # Termbank termtop insertions          : 52483
% 0.21/0.46  
% 0.21/0.46  # -------------------------------------------------
% 0.21/0.46  # User time                : 0.108 s
% 0.21/0.46  # System time              : 0.006 s
% 0.21/0.46  # Total time               : 0.114 s
% 0.21/0.46  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
