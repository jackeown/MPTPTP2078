%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:39:55 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  134 (53086 expanded)
%              Number of clauses        :   85 (21082 expanded)
%              Number of leaves         :   24 (15805 expanded)
%              Depth                    :   25
%              Number of atoms          :  284 (74348 expanded)
%              Number of equality atoms :  166 (60925 expanded)
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

fof(t95_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(t38_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_tarski(X1,X2),X3)
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(t105_xboole_1,axiom,(
    ! [X1,X2] :
      ~ ( r2_xboole_0(X1,X2)
        & k4_xboole_0(X2,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(d8_xboole_0,axiom,(
    ! [X1,X2] :
      ( r2_xboole_0(X1,X2)
    <=> ( r1_tarski(X1,X2)
        & X1 != X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(c_0_24,plain,(
    ! [X80,X81] : k3_tarski(k2_tarski(X80,X81)) = k2_xboole_0(X80,X81) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_25,plain,(
    ! [X53,X54] : k1_enumset1(X53,X53,X54) = k2_tarski(X53,X54) ),
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
    ! [X37,X38] : r1_tarski(X37,k2_xboole_0(X37,X38)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_28,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_29,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_30,plain,(
    ! [X55,X56,X57] : k2_enumset1(X55,X55,X56,X57) = k1_enumset1(X55,X56,X57) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_31,plain,(
    ! [X58,X59,X60,X61] : k3_enumset1(X58,X58,X59,X60,X61) = k2_enumset1(X58,X59,X60,X61) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_32,plain,(
    ! [X62,X63,X64,X65,X66] : k4_enumset1(X62,X62,X63,X64,X65,X66) = k3_enumset1(X62,X63,X64,X65,X66) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_33,plain,(
    ! [X67,X68,X69,X70,X71,X72] : k5_enumset1(X67,X67,X68,X69,X70,X71,X72) = k4_enumset1(X67,X68,X69,X70,X71,X72) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_34,plain,(
    ! [X73,X74,X75,X76,X77,X78,X79] : k6_enumset1(X73,X73,X74,X75,X76,X77,X78,X79) = k5_enumset1(X73,X74,X75,X76,X77,X78,X79) ),
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
    ! [X52] : k2_tarski(X52,X52) = k1_tarski(X52) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_37,plain,(
    ! [X45,X46,X47,X48,X49,X50] :
      ( ( ~ r2_hidden(X47,X46)
        | X47 = X45
        | X46 != k1_tarski(X45) )
      & ( X48 != X45
        | r2_hidden(X48,X46)
        | X46 != k1_tarski(X45) )
      & ( ~ r2_hidden(esk4_2(X49,X50),X50)
        | esk4_2(X49,X50) != X49
        | X50 = k1_tarski(X49) )
      & ( r2_hidden(esk4_2(X49,X50),X50)
        | esk4_2(X49,X50) = X49
        | X50 = k1_tarski(X49) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_38,plain,(
    ! [X8,X9,X10,X11,X12] :
      ( ( ~ r1_tarski(X8,X9)
        | ~ r2_hidden(X10,X8)
        | r2_hidden(X10,X9) )
      & ( r2_hidden(esk1_2(X11,X12),X11)
        | r1_tarski(X11,X12) )
      & ( ~ r2_hidden(esk1_2(X11,X12),X12)
        | r1_tarski(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_39,plain,(
    ! [X27] :
      ( X27 = k1_xboole_0
      | r2_hidden(esk3_1(X27),X27) ) ),
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

fof(c_0_54,plain,(
    ! [X43,X44] : k3_xboole_0(X43,X44) = k5_xboole_0(k5_xboole_0(X43,X44),k2_xboole_0(X43,X44)) ),
    inference(variable_rename,[status(thm)],[t95_xboole_1])).

cnf(c_0_55,plain,
    ( X1 = X3
    | X2 != k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_48]),c_0_29]),c_0_42]),c_0_43]),c_0_44]),c_0_45]),c_0_46])).

cnf(c_0_56,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk3_1(X1),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(esk6_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

fof(c_0_58,plain,(
    ! [X26] : k3_xboole_0(X26,X26) = X26 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

cnf(c_0_59,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

fof(c_0_60,plain,(
    ! [X25] : k2_xboole_0(X25,X25) = X25 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

fof(c_0_61,plain,(
    ! [X82,X83,X84] :
      ( ( r2_hidden(X82,X84)
        | ~ r1_tarski(k2_tarski(X82,X83),X84) )
      & ( r2_hidden(X83,X84)
        | ~ r1_tarski(k2_tarski(X82,X83),X84) )
      & ( ~ r2_hidden(X82,X84)
        | ~ r2_hidden(X83,X84)
        | r1_tarski(k2_tarski(X82,X83),X84) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).

cnf(c_0_62,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_55])).

cnf(c_0_63,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r2_hidden(esk3_1(esk6_0),k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

fof(c_0_64,plain,(
    ! [X31,X32] :
      ( ~ r2_xboole_0(X31,X32)
      | k4_xboole_0(X32,X31) != k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t105_xboole_1])])).

fof(c_0_65,plain,(
    ! [X29,X30] : k4_xboole_0(X29,X30) = k5_xboole_0(X29,k3_xboole_0(X29,X30)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_66,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_67,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_41]),c_0_42]),c_0_43])).

fof(c_0_68,plain,(
    ! [X42] : k5_xboole_0(X42,X42) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

cnf(c_0_69,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_70,plain,
    ( r1_tarski(k2_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_71,negated_conjecture,
    ( esk3_1(esk6_0) = esk5_0
    | esk6_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

fof(c_0_72,plain,(
    ! [X14,X15,X16,X17,X18,X19,X20,X21] :
      ( ( ~ r2_hidden(X17,X16)
        | r2_hidden(X17,X14)
        | r2_hidden(X17,X15)
        | X16 != k2_xboole_0(X14,X15) )
      & ( ~ r2_hidden(X18,X14)
        | r2_hidden(X18,X16)
        | X16 != k2_xboole_0(X14,X15) )
      & ( ~ r2_hidden(X18,X15)
        | r2_hidden(X18,X16)
        | X16 != k2_xboole_0(X14,X15) )
      & ( ~ r2_hidden(esk2_3(X19,X20,X21),X19)
        | ~ r2_hidden(esk2_3(X19,X20,X21),X21)
        | X21 = k2_xboole_0(X19,X20) )
      & ( ~ r2_hidden(esk2_3(X19,X20,X21),X20)
        | ~ r2_hidden(esk2_3(X19,X20,X21),X21)
        | X21 = k2_xboole_0(X19,X20) )
      & ( r2_hidden(esk2_3(X19,X20,X21),X21)
        | r2_hidden(esk2_3(X19,X20,X21),X19)
        | r2_hidden(esk2_3(X19,X20,X21),X20)
        | X21 = k2_xboole_0(X19,X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

cnf(c_0_73,plain,
    ( ~ r2_xboole_0(X1,X2)
    | k4_xboole_0(X2,X1) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_74,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

fof(c_0_75,plain,(
    ! [X39,X40,X41] : k5_xboole_0(k5_xboole_0(X39,X40),X41) = k5_xboole_0(X39,k5_xboole_0(X40,X41)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_76,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X1),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_67]),c_0_44]),c_0_45]),c_0_46])).

cnf(c_0_77,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_78,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_41]),c_0_42]),c_0_43]),c_0_44]),c_0_45]),c_0_46])).

cnf(c_0_79,plain,
    ( r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3),X2)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_29]),c_0_42]),c_0_43]),c_0_44]),c_0_45]),c_0_46])).

cnf(c_0_80,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r2_hidden(esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_71])).

fof(c_0_81,plain,(
    ! [X33,X34] :
      ( ~ r1_tarski(X33,X34)
      | k2_xboole_0(X33,X34) = X34 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_82,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_83,plain,
    ( k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,X1),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)))) != k1_xboole_0
    | ~ r2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_74]),c_0_67]),c_0_44]),c_0_45]),c_0_46])).

cnf(c_0_84,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_85,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_77]),c_0_78])).

fof(c_0_86,plain,(
    ! [X23,X24] :
      ( ( r1_tarski(X23,X24)
        | ~ r2_xboole_0(X23,X24) )
      & ( X23 != X24
        | ~ r2_xboole_0(X23,X24) )
      & ( ~ r1_tarski(X23,X24)
        | X23 = X24
        | r2_xboole_0(X23,X24) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).

cnf(c_0_87,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,esk5_0),esk6_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_88,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_89,plain,
    ( r2_hidden(X1,X3)
    | X3 != k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X2))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82,c_0_41]),c_0_42]),c_0_43]),c_0_44]),c_0_45]),c_0_46])).

cnf(c_0_90,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))) != k1_xboole_0
    | ~ r2_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_91,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_77]),c_0_85])).

cnf(c_0_92,plain,
    ( X1 = X2
    | r2_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_86])).

cnf(c_0_93,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r1_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_87,c_0_80])).

cnf(c_0_94,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_88,c_0_41]),c_0_42]),c_0_43]),c_0_44]),c_0_45]),c_0_46])).

cnf(c_0_95,plain,
    ( r2_hidden(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_89])).

cnf(c_0_96,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_97,plain,
    ( k5_xboole_0(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) != k1_xboole_0
    | ~ r2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_98,negated_conjecture,
    ( k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) = esk6_0
    | esk6_0 = k1_xboole_0
    | r2_xboole_0(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_92,c_0_93])).

cnf(c_0_99,negated_conjecture,
    ( k3_tarski(k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))) = k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_94,c_0_57])).

cnf(c_0_100,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk3_1(X1),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
    inference(spm,[status(thm)],[c_0_95,c_0_51])).

cnf(c_0_101,plain,
    ( esk1_2(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2) = X1
    | r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2) ),
    inference(spm,[status(thm)],[c_0_62,c_0_96])).

cnf(c_0_102,negated_conjecture,
    ( k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) = esk6_0
    | esk6_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_98]),c_0_99]),c_0_77])])).

cnf(c_0_103,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r2_hidden(esk3_1(esk7_0),k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_100,c_0_53])).

cnf(c_0_104,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_105,negated_conjecture,
    ( esk1_2(esk6_0,X1) = esk5_0
    | esk6_0 = k1_xboole_0
    | r1_tarski(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_101,c_0_102])).

cnf(c_0_106,negated_conjecture,
    ( esk3_1(esk7_0) = esk5_0
    | esk7_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_62,c_0_103])).

cnf(c_0_107,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r1_tarski(esk6_0,X1)
    | ~ r2_hidden(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_104,c_0_105])).

cnf(c_0_108,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r2_hidden(esk5_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_106])).

cnf(c_0_109,negated_conjecture,
    ( esk6_0 != k1_tarski(esk5_0)
    | esk7_0 != k1_tarski(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_110,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | r1_tarski(esk6_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_107,c_0_108])).

cnf(c_0_111,negated_conjecture,
    ( esk6_0 != k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)
    | esk7_0 != k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_109,c_0_48]),c_0_48]),c_0_29]),c_0_29]),c_0_42]),c_0_42]),c_0_43]),c_0_43]),c_0_44]),c_0_44]),c_0_45]),c_0_45]),c_0_46]),c_0_46])).

cnf(c_0_112,negated_conjecture,
    ( esk6_0 != k1_tarski(esk5_0)
    | esk7_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_113,negated_conjecture,
    ( k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) = esk7_0
    | esk6_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_110]),c_0_53])).

cnf(c_0_114,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk7_0 != esk6_0 ),
    inference(spm,[status(thm)],[c_0_111,c_0_102])).

cnf(c_0_115,negated_conjecture,
    ( esk7_0 != k1_xboole_0
    | esk6_0 != k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_112,c_0_48]),c_0_29]),c_0_42]),c_0_43]),c_0_44]),c_0_45]),c_0_46])).

cnf(c_0_116,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_113]),c_0_114])).

cnf(c_0_117,plain,
    ( X1 = k1_xboole_0
    | r1_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,esk3_1(X1)),X1)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_79,c_0_51])).

cnf(c_0_118,negated_conjecture,
    ( esk6_0 != k1_xboole_0
    | esk7_0 != k1_tarski(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_119,negated_conjecture,
    ( esk6_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_116]),c_0_102])).

cnf(c_0_120,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r1_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk3_1(esk7_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_117,c_0_108])).

cnf(c_0_121,negated_conjecture,
    ( esk6_0 != k1_xboole_0
    | esk7_0 != k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_118,c_0_48]),c_0_29]),c_0_42]),c_0_43]),c_0_44]),c_0_45]),c_0_46])).

cnf(c_0_122,plain,
    ( r2_hidden(esk1_2(X1,X2),k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X1)))
    | r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_95,c_0_96])).

cnf(c_0_123,negated_conjecture,
    ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,esk7_0)) = k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_119]),c_0_119]),c_0_119]),c_0_119]),c_0_119]),c_0_119]),c_0_119])).

cnf(c_0_124,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r1_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_120,c_0_106])).

cnf(c_0_125,negated_conjecture,
    ( k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) != esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_121,c_0_119])])).

cnf(c_0_126,negated_conjecture,
    ( r2_hidden(esk1_2(esk7_0,X1),k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))
    | r1_tarski(esk7_0,X1) ),
    inference(spm,[status(thm)],[c_0_122,c_0_123])).

cnf(c_0_127,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r2_xboole_0(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_124]),c_0_125])).

cnf(c_0_128,negated_conjecture,
    ( r1_tarski(esk7_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_104,c_0_126])).

cnf(c_0_129,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | k5_xboole_0(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_tarski(k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_97,c_0_127])).

cnf(c_0_130,negated_conjecture,
    ( k3_tarski(k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))) = k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_94,c_0_128])).

cnf(c_0_131,negated_conjecture,
    ( esk7_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_129,c_0_130]),c_0_77])])).

cnf(c_0_132,negated_conjecture,
    ( k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_125,c_0_131])).

cnf(c_0_133,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_123,c_0_131]),c_0_78]),c_0_132]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:42:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.45  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S054N
% 0.20/0.45  # and selection function GSelectMinInfpos.
% 0.20/0.45  #
% 0.20/0.45  # Preprocessing time       : 0.028 s
% 0.20/0.45  # Presaturation interreduction done
% 0.20/0.45  
% 0.20/0.45  # Proof found!
% 0.20/0.45  # SZS status Theorem
% 0.20/0.45  # SZS output start CNFRefutation
% 0.20/0.45  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.20/0.45  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.45  fof(t43_zfmisc_1, conjecture, ![X1, X2, X3]:~((((k1_tarski(X1)=k2_xboole_0(X2,X3)&~((X2=k1_tarski(X1)&X3=k1_tarski(X1))))&~((X2=k1_xboole_0&X3=k1_tarski(X1))))&~((X2=k1_tarski(X1)&X3=k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 0.20/0.45  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.20/0.45  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.20/0.45  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.20/0.45  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.20/0.45  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.20/0.45  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 0.20/0.45  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.20/0.45  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 0.20/0.45  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.45  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.20/0.45  fof(t95_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 0.20/0.45  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.20/0.45  fof(idempotence_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 0.20/0.45  fof(t38_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_tarski(X1,X2),X3)<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 0.20/0.45  fof(t105_xboole_1, axiom, ![X1, X2]:~((r2_xboole_0(X1,X2)&k4_xboole_0(X2,X1)=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t105_xboole_1)).
% 0.20/0.45  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.20/0.45  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 0.20/0.45  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 0.20/0.45  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.20/0.45  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.20/0.45  fof(d8_xboole_0, axiom, ![X1, X2]:(r2_xboole_0(X1,X2)<=>(r1_tarski(X1,X2)&X1!=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 0.20/0.45  fof(c_0_24, plain, ![X80, X81]:k3_tarski(k2_tarski(X80,X81))=k2_xboole_0(X80,X81), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.20/0.45  fof(c_0_25, plain, ![X53, X54]:k1_enumset1(X53,X53,X54)=k2_tarski(X53,X54), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.45  fof(c_0_26, negated_conjecture, ~(![X1, X2, X3]:~((((k1_tarski(X1)=k2_xboole_0(X2,X3)&~((X2=k1_tarski(X1)&X3=k1_tarski(X1))))&~((X2=k1_xboole_0&X3=k1_tarski(X1))))&~((X2=k1_tarski(X1)&X3=k1_xboole_0))))), inference(assume_negation,[status(cth)],[t43_zfmisc_1])).
% 0.20/0.45  fof(c_0_27, plain, ![X37, X38]:r1_tarski(X37,k2_xboole_0(X37,X38)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.20/0.45  cnf(c_0_28, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.45  cnf(c_0_29, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.45  fof(c_0_30, plain, ![X55, X56, X57]:k2_enumset1(X55,X55,X56,X57)=k1_enumset1(X55,X56,X57), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.20/0.45  fof(c_0_31, plain, ![X58, X59, X60, X61]:k3_enumset1(X58,X58,X59,X60,X61)=k2_enumset1(X58,X59,X60,X61), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.20/0.45  fof(c_0_32, plain, ![X62, X63, X64, X65, X66]:k4_enumset1(X62,X62,X63,X64,X65,X66)=k3_enumset1(X62,X63,X64,X65,X66), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.20/0.45  fof(c_0_33, plain, ![X67, X68, X69, X70, X71, X72]:k5_enumset1(X67,X67,X68,X69,X70,X71,X72)=k4_enumset1(X67,X68,X69,X70,X71,X72), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.20/0.45  fof(c_0_34, plain, ![X73, X74, X75, X76, X77, X78, X79]:k6_enumset1(X73,X73,X74,X75,X76,X77,X78,X79)=k5_enumset1(X73,X74,X75,X76,X77,X78,X79), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.20/0.45  fof(c_0_35, negated_conjecture, (((k1_tarski(esk5_0)=k2_xboole_0(esk6_0,esk7_0)&(esk6_0!=k1_tarski(esk5_0)|esk7_0!=k1_tarski(esk5_0)))&(esk6_0!=k1_xboole_0|esk7_0!=k1_tarski(esk5_0)))&(esk6_0!=k1_tarski(esk5_0)|esk7_0!=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_26])])])).
% 0.20/0.45  fof(c_0_36, plain, ![X52]:k2_tarski(X52,X52)=k1_tarski(X52), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.20/0.45  fof(c_0_37, plain, ![X45, X46, X47, X48, X49, X50]:(((~r2_hidden(X47,X46)|X47=X45|X46!=k1_tarski(X45))&(X48!=X45|r2_hidden(X48,X46)|X46!=k1_tarski(X45)))&((~r2_hidden(esk4_2(X49,X50),X50)|esk4_2(X49,X50)!=X49|X50=k1_tarski(X49))&(r2_hidden(esk4_2(X49,X50),X50)|esk4_2(X49,X50)=X49|X50=k1_tarski(X49)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.20/0.45  fof(c_0_38, plain, ![X8, X9, X10, X11, X12]:((~r1_tarski(X8,X9)|(~r2_hidden(X10,X8)|r2_hidden(X10,X9)))&((r2_hidden(esk1_2(X11,X12),X11)|r1_tarski(X11,X12))&(~r2_hidden(esk1_2(X11,X12),X12)|r1_tarski(X11,X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.45  fof(c_0_39, plain, ![X27]:(X27=k1_xboole_0|r2_hidden(esk3_1(X27),X27)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.20/0.45  cnf(c_0_40, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.45  cnf(c_0_41, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_28, c_0_29])).
% 0.20/0.45  cnf(c_0_42, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.45  cnf(c_0_43, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.45  cnf(c_0_44, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.45  cnf(c_0_45, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.45  cnf(c_0_46, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.45  cnf(c_0_47, negated_conjecture, (k1_tarski(esk5_0)=k2_xboole_0(esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.45  cnf(c_0_48, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.45  cnf(c_0_49, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.45  cnf(c_0_50, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.45  cnf(c_0_51, plain, (X1=k1_xboole_0|r2_hidden(esk3_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.45  cnf(c_0_52, plain, (r1_tarski(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_41]), c_0_42]), c_0_43]), c_0_44]), c_0_45]), c_0_46])).
% 0.20/0.45  cnf(c_0_53, negated_conjecture, (k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)=k3_tarski(k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk7_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_48]), c_0_29]), c_0_41]), c_0_42]), c_0_42]), c_0_43]), c_0_43]), c_0_44]), c_0_44]), c_0_45]), c_0_45]), c_0_46]), c_0_46])).
% 0.20/0.45  fof(c_0_54, plain, ![X43, X44]:k3_xboole_0(X43,X44)=k5_xboole_0(k5_xboole_0(X43,X44),k2_xboole_0(X43,X44)), inference(variable_rename,[status(thm)],[t95_xboole_1])).
% 0.20/0.45  cnf(c_0_55, plain, (X1=X3|X2!=k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_48]), c_0_29]), c_0_42]), c_0_43]), c_0_44]), c_0_45]), c_0_46])).
% 0.20/0.45  cnf(c_0_56, plain, (X1=k1_xboole_0|r2_hidden(esk3_1(X1),X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.20/0.45  cnf(c_0_57, negated_conjecture, (r1_tarski(esk6_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.20/0.45  fof(c_0_58, plain, ![X26]:k3_xboole_0(X26,X26)=X26, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.20/0.45  cnf(c_0_59, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.20/0.45  fof(c_0_60, plain, ![X25]:k2_xboole_0(X25,X25)=X25, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).
% 0.20/0.45  fof(c_0_61, plain, ![X82, X83, X84]:(((r2_hidden(X82,X84)|~r1_tarski(k2_tarski(X82,X83),X84))&(r2_hidden(X83,X84)|~r1_tarski(k2_tarski(X82,X83),X84)))&(~r2_hidden(X82,X84)|~r2_hidden(X83,X84)|r1_tarski(k2_tarski(X82,X83),X84))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).
% 0.20/0.45  cnf(c_0_62, plain, (X1=X2|~r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_55])).
% 0.20/0.45  cnf(c_0_63, negated_conjecture, (esk6_0=k1_xboole_0|r2_hidden(esk3_1(esk6_0),k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.20/0.45  fof(c_0_64, plain, ![X31, X32]:(~r2_xboole_0(X31,X32)|k4_xboole_0(X32,X31)!=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t105_xboole_1])])).
% 0.20/0.45  fof(c_0_65, plain, ![X29, X30]:k4_xboole_0(X29,X30)=k5_xboole_0(X29,k3_xboole_0(X29,X30)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.20/0.45  cnf(c_0_66, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.20/0.45  cnf(c_0_67, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_41]), c_0_42]), c_0_43])).
% 0.20/0.45  fof(c_0_68, plain, ![X42]:k5_xboole_0(X42,X42)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 0.20/0.45  cnf(c_0_69, plain, (k2_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.20/0.45  cnf(c_0_70, plain, (r1_tarski(k2_tarski(X1,X3),X2)|~r2_hidden(X1,X2)|~r2_hidden(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.20/0.45  cnf(c_0_71, negated_conjecture, (esk3_1(esk6_0)=esk5_0|esk6_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.20/0.45  fof(c_0_72, plain, ![X14, X15, X16, X17, X18, X19, X20, X21]:(((~r2_hidden(X17,X16)|(r2_hidden(X17,X14)|r2_hidden(X17,X15))|X16!=k2_xboole_0(X14,X15))&((~r2_hidden(X18,X14)|r2_hidden(X18,X16)|X16!=k2_xboole_0(X14,X15))&(~r2_hidden(X18,X15)|r2_hidden(X18,X16)|X16!=k2_xboole_0(X14,X15))))&(((~r2_hidden(esk2_3(X19,X20,X21),X19)|~r2_hidden(esk2_3(X19,X20,X21),X21)|X21=k2_xboole_0(X19,X20))&(~r2_hidden(esk2_3(X19,X20,X21),X20)|~r2_hidden(esk2_3(X19,X20,X21),X21)|X21=k2_xboole_0(X19,X20)))&(r2_hidden(esk2_3(X19,X20,X21),X21)|(r2_hidden(esk2_3(X19,X20,X21),X19)|r2_hidden(esk2_3(X19,X20,X21),X20))|X21=k2_xboole_0(X19,X20)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 0.20/0.45  cnf(c_0_73, plain, (~r2_xboole_0(X1,X2)|k4_xboole_0(X2,X1)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.20/0.45  cnf(c_0_74, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.20/0.45  fof(c_0_75, plain, ![X39, X40, X41]:k5_xboole_0(k5_xboole_0(X39,X40),X41)=k5_xboole_0(X39,k5_xboole_0(X40,X41)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.20/0.45  cnf(c_0_76, plain, (k5_xboole_0(k5_xboole_0(X1,X1),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_67]), c_0_44]), c_0_45]), c_0_46])).
% 0.20/0.45  cnf(c_0_77, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.20/0.45  cnf(c_0_78, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69, c_0_41]), c_0_42]), c_0_43]), c_0_44]), c_0_45]), c_0_46])).
% 0.20/0.45  cnf(c_0_79, plain, (r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3),X2)|~r2_hidden(X3,X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_29]), c_0_42]), c_0_43]), c_0_44]), c_0_45]), c_0_46])).
% 0.20/0.45  cnf(c_0_80, negated_conjecture, (esk6_0=k1_xboole_0|r2_hidden(esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_51, c_0_71])).
% 0.20/0.45  fof(c_0_81, plain, ![X33, X34]:(~r1_tarski(X33,X34)|k2_xboole_0(X33,X34)=X34), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.20/0.45  cnf(c_0_82, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.20/0.45  cnf(c_0_83, plain, (k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,X1),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))))!=k1_xboole_0|~r2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73, c_0_74]), c_0_67]), c_0_44]), c_0_45]), c_0_46])).
% 0.20/0.45  cnf(c_0_84, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.20/0.45  cnf(c_0_85, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76, c_0_77]), c_0_78])).
% 0.20/0.45  fof(c_0_86, plain, ![X23, X24]:(((r1_tarski(X23,X24)|~r2_xboole_0(X23,X24))&(X23!=X24|~r2_xboole_0(X23,X24)))&(~r1_tarski(X23,X24)|X23=X24|r2_xboole_0(X23,X24))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).
% 0.20/0.45  cnf(c_0_87, negated_conjecture, (esk6_0=k1_xboole_0|r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,esk5_0),esk6_0)|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_79, c_0_80])).
% 0.20/0.45  cnf(c_0_88, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_81])).
% 0.20/0.45  cnf(c_0_89, plain, (r2_hidden(X1,X3)|X3!=k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X2))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82, c_0_41]), c_0_42]), c_0_43]), c_0_44]), c_0_45]), c_0_46])).
% 0.20/0.45  cnf(c_0_90, plain, (k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))))!=k1_xboole_0|~r2_xboole_0(X2,X1)), inference(rw,[status(thm)],[c_0_83, c_0_84])).
% 0.20/0.45  cnf(c_0_91, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_77]), c_0_85])).
% 0.20/0.45  cnf(c_0_92, plain, (X1=X2|r2_xboole_0(X1,X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_86])).
% 0.20/0.45  cnf(c_0_93, negated_conjecture, (esk6_0=k1_xboole_0|r1_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk6_0)), inference(spm,[status(thm)],[c_0_87, c_0_80])).
% 0.20/0.45  cnf(c_0_94, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))=X2|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_88, c_0_41]), c_0_42]), c_0_43]), c_0_44]), c_0_45]), c_0_46])).
% 0.20/0.45  cnf(c_0_95, plain, (r2_hidden(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_89])).
% 0.20/0.45  cnf(c_0_96, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.45  cnf(c_0_97, plain, (k5_xboole_0(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)))!=k1_xboole_0|~r2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_90, c_0_91])).
% 0.20/0.45  cnf(c_0_98, negated_conjecture, (k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)=esk6_0|esk6_0=k1_xboole_0|r2_xboole_0(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk6_0)), inference(spm,[status(thm)],[c_0_92, c_0_93])).
% 0.20/0.45  cnf(c_0_99, negated_conjecture, (k3_tarski(k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))=k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)), inference(spm,[status(thm)],[c_0_94, c_0_57])).
% 0.20/0.45  cnf(c_0_100, plain, (X1=k1_xboole_0|r2_hidden(esk3_1(X1),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)))), inference(spm,[status(thm)],[c_0_95, c_0_51])).
% 0.20/0.45  cnf(c_0_101, plain, (esk1_2(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)=X1|r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)), inference(spm,[status(thm)],[c_0_62, c_0_96])).
% 0.20/0.45  cnf(c_0_102, negated_conjecture, (k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)=esk6_0|esk6_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_98]), c_0_99]), c_0_77])])).
% 0.20/0.45  cnf(c_0_103, negated_conjecture, (esk7_0=k1_xboole_0|r2_hidden(esk3_1(esk7_0),k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))), inference(spm,[status(thm)],[c_0_100, c_0_53])).
% 0.20/0.45  cnf(c_0_104, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.45  cnf(c_0_105, negated_conjecture, (esk1_2(esk6_0,X1)=esk5_0|esk6_0=k1_xboole_0|r1_tarski(esk6_0,X1)), inference(spm,[status(thm)],[c_0_101, c_0_102])).
% 0.20/0.45  cnf(c_0_106, negated_conjecture, (esk3_1(esk7_0)=esk5_0|esk7_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_62, c_0_103])).
% 0.20/0.45  cnf(c_0_107, negated_conjecture, (esk6_0=k1_xboole_0|r1_tarski(esk6_0,X1)|~r2_hidden(esk5_0,X1)), inference(spm,[status(thm)],[c_0_104, c_0_105])).
% 0.20/0.45  cnf(c_0_108, negated_conjecture, (esk7_0=k1_xboole_0|r2_hidden(esk5_0,esk7_0)), inference(spm,[status(thm)],[c_0_51, c_0_106])).
% 0.20/0.45  cnf(c_0_109, negated_conjecture, (esk6_0!=k1_tarski(esk5_0)|esk7_0!=k1_tarski(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.45  cnf(c_0_110, negated_conjecture, (esk7_0=k1_xboole_0|esk6_0=k1_xboole_0|r1_tarski(esk6_0,esk7_0)), inference(spm,[status(thm)],[c_0_107, c_0_108])).
% 0.20/0.45  cnf(c_0_111, negated_conjecture, (esk6_0!=k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)|esk7_0!=k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_109, c_0_48]), c_0_48]), c_0_29]), c_0_29]), c_0_42]), c_0_42]), c_0_43]), c_0_43]), c_0_44]), c_0_44]), c_0_45]), c_0_45]), c_0_46]), c_0_46])).
% 0.20/0.45  cnf(c_0_112, negated_conjecture, (esk6_0!=k1_tarski(esk5_0)|esk7_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.45  cnf(c_0_113, negated_conjecture, (k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)=esk7_0|esk6_0=k1_xboole_0|esk7_0=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_110]), c_0_53])).
% 0.20/0.45  cnf(c_0_114, negated_conjecture, (esk6_0=k1_xboole_0|esk7_0!=esk6_0), inference(spm,[status(thm)],[c_0_111, c_0_102])).
% 0.20/0.45  cnf(c_0_115, negated_conjecture, (esk7_0!=k1_xboole_0|esk6_0!=k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_112, c_0_48]), c_0_29]), c_0_42]), c_0_43]), c_0_44]), c_0_45]), c_0_46])).
% 0.20/0.45  cnf(c_0_116, negated_conjecture, (esk7_0=k1_xboole_0|esk6_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_113]), c_0_114])).
% 0.20/0.45  cnf(c_0_117, plain, (X1=k1_xboole_0|r1_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,esk3_1(X1)),X1)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_79, c_0_51])).
% 0.20/0.45  cnf(c_0_118, negated_conjecture, (esk6_0!=k1_xboole_0|esk7_0!=k1_tarski(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.45  cnf(c_0_119, negated_conjecture, (esk6_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_116]), c_0_102])).
% 0.20/0.45  cnf(c_0_120, negated_conjecture, (esk7_0=k1_xboole_0|r1_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk3_1(esk7_0)),esk7_0)), inference(spm,[status(thm)],[c_0_117, c_0_108])).
% 0.20/0.45  cnf(c_0_121, negated_conjecture, (esk6_0!=k1_xboole_0|esk7_0!=k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_118, c_0_48]), c_0_29]), c_0_42]), c_0_43]), c_0_44]), c_0_45]), c_0_46])).
% 0.20/0.45  cnf(c_0_122, plain, (r2_hidden(esk1_2(X1,X2),k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X1)))|r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_95, c_0_96])).
% 0.20/0.45  cnf(c_0_123, negated_conjecture, (k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,esk7_0))=k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_119]), c_0_119]), c_0_119]), c_0_119]), c_0_119]), c_0_119]), c_0_119])).
% 0.20/0.45  cnf(c_0_124, negated_conjecture, (esk7_0=k1_xboole_0|r1_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk7_0)), inference(spm,[status(thm)],[c_0_120, c_0_106])).
% 0.20/0.45  cnf(c_0_125, negated_conjecture, (k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)!=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_121, c_0_119])])).
% 0.20/0.45  cnf(c_0_126, negated_conjecture, (r2_hidden(esk1_2(esk7_0,X1),k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))|r1_tarski(esk7_0,X1)), inference(spm,[status(thm)],[c_0_122, c_0_123])).
% 0.20/0.45  cnf(c_0_127, negated_conjecture, (esk7_0=k1_xboole_0|r2_xboole_0(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk7_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_124]), c_0_125])).
% 0.20/0.45  cnf(c_0_128, negated_conjecture, (r1_tarski(esk7_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))), inference(spm,[status(thm)],[c_0_104, c_0_126])).
% 0.20/0.45  cnf(c_0_129, negated_conjecture, (esk7_0=k1_xboole_0|k5_xboole_0(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_tarski(k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_97, c_0_127])).
% 0.20/0.45  cnf(c_0_130, negated_conjecture, (k3_tarski(k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))=k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)), inference(spm,[status(thm)],[c_0_94, c_0_128])).
% 0.20/0.45  cnf(c_0_131, negated_conjecture, (esk7_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_129, c_0_130]), c_0_77])])).
% 0.20/0.45  cnf(c_0_132, negated_conjecture, (k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_125, c_0_131])).
% 0.20/0.45  cnf(c_0_133, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_123, c_0_131]), c_0_78]), c_0_132]), ['proof']).
% 0.20/0.45  # SZS output end CNFRefutation
% 0.20/0.45  # Proof object total steps             : 134
% 0.20/0.45  # Proof object clause steps            : 85
% 0.20/0.45  # Proof object formula steps           : 49
% 0.20/0.45  # Proof object conjectures             : 42
% 0.20/0.45  # Proof object clause conjectures      : 39
% 0.20/0.45  # Proof object formula conjectures     : 3
% 0.20/0.45  # Proof object initial clauses used    : 29
% 0.20/0.45  # Proof object initial formulas used   : 24
% 0.20/0.45  # Proof object generating inferences   : 32
% 0.20/0.45  # Proof object simplifying inferences  : 121
% 0.20/0.45  # Training examples: 0 positive, 0 negative
% 0.20/0.45  # Parsed axioms                        : 25
% 0.20/0.45  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.45  # Initial clauses                      : 42
% 0.20/0.45  # Removed in clause preprocessing      : 10
% 0.20/0.45  # Initial clauses in saturation        : 32
% 0.20/0.45  # Processed clauses                    : 507
% 0.20/0.45  # ...of these trivial                  : 7
% 0.20/0.45  # ...subsumed                          : 247
% 0.20/0.45  # ...remaining for further processing  : 252
% 0.20/0.45  # Other redundant clauses eliminated   : 26
% 0.20/0.45  # Clauses deleted for lack of memory   : 0
% 0.20/0.45  # Backward-subsumed                    : 9
% 0.20/0.45  # Backward-rewritten                   : 140
% 0.20/0.45  # Generated clauses                    : 2060
% 0.20/0.45  # ...of the previous two non-trivial   : 1951
% 0.20/0.45  # Contextual simplify-reflections      : 4
% 0.20/0.45  # Paramodulations                      : 1992
% 0.20/0.45  # Factorizations                       : 42
% 0.20/0.45  # Equation resolutions                 : 26
% 0.20/0.45  # Propositional unsat checks           : 0
% 0.20/0.45  #    Propositional check models        : 0
% 0.20/0.45  #    Propositional check unsatisfiable : 0
% 0.20/0.45  #    Propositional clauses             : 0
% 0.20/0.45  #    Propositional clauses after purity: 0
% 0.20/0.45  #    Propositional unsat core size     : 0
% 0.20/0.45  #    Propositional preprocessing time  : 0.000
% 0.20/0.45  #    Propositional encoding time       : 0.000
% 0.20/0.45  #    Propositional solver time         : 0.000
% 0.20/0.45  #    Success case prop preproc time    : 0.000
% 0.20/0.45  #    Success case prop encoding time   : 0.000
% 0.20/0.45  #    Success case prop solver time     : 0.000
% 0.20/0.45  # Current number of processed clauses  : 64
% 0.20/0.45  #    Positive orientable unit clauses  : 20
% 0.20/0.45  #    Positive unorientable unit clauses: 1
% 0.20/0.45  #    Negative unit clauses             : 2
% 0.20/0.45  #    Non-unit-clauses                  : 41
% 0.20/0.45  # Current number of unprocessed clauses: 1416
% 0.20/0.45  # ...number of literals in the above   : 6917
% 0.20/0.45  # Current number of archived formulas  : 0
% 0.20/0.45  # Current number of archived clauses   : 192
% 0.20/0.45  # Clause-clause subsumption calls (NU) : 4277
% 0.20/0.45  # Rec. Clause-clause subsumption calls : 1577
% 0.20/0.45  # Non-unit clause-clause subsumptions  : 257
% 0.20/0.45  # Unit Clause-clause subsumption calls : 66
% 0.20/0.45  # Rewrite failures with RHS unbound    : 0
% 0.20/0.45  # BW rewrite match attempts            : 77
% 0.20/0.45  # BW rewrite match successes           : 33
% 0.20/0.45  # Condensation attempts                : 0
% 0.20/0.45  # Condensation successes               : 0
% 0.20/0.45  # Termbank termtop insertions          : 50423
% 0.20/0.45  
% 0.20/0.45  # -------------------------------------------------
% 0.20/0.45  # User time                : 0.103 s
% 0.20/0.45  # System time              : 0.008 s
% 0.20/0.45  # Total time               : 0.110 s
% 0.20/0.45  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
