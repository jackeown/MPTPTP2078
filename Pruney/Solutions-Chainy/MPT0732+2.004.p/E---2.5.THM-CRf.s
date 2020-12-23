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
% DateTime   : Thu Dec  3 10:56:09 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 411 expanded)
%              Number of clauses        :   65 ( 191 expanded)
%              Number of leaves         :   21 ( 108 expanded)
%              Depth                    :   13
%              Number of atoms          :  252 ( 842 expanded)
%              Number of equality atoms :  125 ( 538 expanded)
%              Maximal formula depth    :   42 (   3 average)
%              Maximal clause size      :   60 (   1 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t22_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t21_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

fof(t14_zfmisc_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k1_tarski(X1),k2_tarski(X1,X2)) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_zfmisc_1)).

fof(t87_enumset1,axiom,(
    ! [X1] : k3_enumset1(X1,X1,X1,X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_enumset1)).

fof(t80_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k5_enumset1(X1,X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_enumset1)).

fof(t60_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_enumset1)).

fof(d5_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] :
      ( X8 = k5_enumset1(X1,X2,X3,X4,X5,X6,X7)
    <=> ! [X9] :
          ( r2_hidden(X9,X8)
        <=> ~ ( X9 != X1
              & X9 != X2
              & X9 != X3
              & X9 != X4
              & X9 != X5
              & X9 != X6
              & X9 != X7 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_enumset1)).

fof(d6_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

fof(l49_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(X1,k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(t107_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k5_xboole_0(X2,X3))
    <=> ( r1_tarski(X1,k2_xboole_0(X2,X3))
        & r1_xboole_0(X1,k3_xboole_0(X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_xboole_1)).

fof(t40_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(t45_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => X2 = k2_xboole_0(X1,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).

fof(t51_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(t19_ordinal1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_ordinal1(X3)
     => ( ( r2_hidden(X1,X2)
          & r2_hidden(X2,X3) )
       => r2_hidden(X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_ordinal1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(d2_ordinal1,axiom,(
    ! [X1] :
      ( v1_ordinal1(X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
         => r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_ordinal1)).

fof(l38_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k4_xboole_0(k2_tarski(X1,X2),X3) = k1_tarski(X1)
    <=> ( ~ r2_hidden(X1,X3)
        & ( r2_hidden(X2,X3)
          | X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l38_zfmisc_1)).

fof(t81_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_xboole_0(X1,k4_xboole_0(X2,X3))
     => r1_xboole_0(X2,k4_xboole_0(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_xboole_1)).

fof(t55_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( r1_xboole_0(k2_tarski(X1,X2),X3)
        & r2_hidden(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).

fof(c_0_21,plain,(
    ! [X19,X20] : k2_xboole_0(X19,k3_xboole_0(X19,X20)) = X19 ),
    inference(variable_rename,[status(thm)],[t22_xboole_1])).

fof(c_0_22,plain,(
    ! [X49,X50] : k3_tarski(k2_tarski(X49,X50)) = k2_xboole_0(X49,X50) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_23,plain,(
    ! [X17,X18] : k3_xboole_0(X17,k2_xboole_0(X17,X18)) = X17 ),
    inference(variable_rename,[status(thm)],[t21_xboole_1])).

fof(c_0_24,plain,(
    ! [X51,X52] : k2_xboole_0(k1_tarski(X51),k2_tarski(X51,X52)) = k2_tarski(X51,X52) ),
    inference(variable_rename,[status(thm)],[t14_zfmisc_1])).

fof(c_0_25,plain,(
    ! [X43] : k3_enumset1(X43,X43,X43,X43,X43) = k1_tarski(X43) ),
    inference(variable_rename,[status(thm)],[t87_enumset1])).

fof(c_0_26,plain,(
    ! [X38,X39,X40,X41,X42] : k5_enumset1(X38,X38,X38,X39,X40,X41,X42) = k3_enumset1(X38,X39,X40,X41,X42) ),
    inference(variable_rename,[status(thm)],[t80_enumset1])).

fof(c_0_27,plain,(
    ! [X31,X32,X33,X34,X35,X36,X37] : k5_enumset1(X31,X32,X33,X34,X35,X36,X37) = k2_xboole_0(k3_enumset1(X31,X32,X33,X34,X35),k2_tarski(X36,X37)) ),
    inference(variable_rename,[status(thm)],[t60_enumset1])).

cnf(c_0_28,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_31,plain,(
    ! [X56,X57,X58,X59,X60,X61,X62,X63,X64,X65,X66,X67,X68,X69,X70,X71,X72,X73] :
      ( ( ~ r2_hidden(X64,X63)
        | X64 = X56
        | X64 = X57
        | X64 = X58
        | X64 = X59
        | X64 = X60
        | X64 = X61
        | X64 = X62
        | X63 != k5_enumset1(X56,X57,X58,X59,X60,X61,X62) )
      & ( X65 != X56
        | r2_hidden(X65,X63)
        | X63 != k5_enumset1(X56,X57,X58,X59,X60,X61,X62) )
      & ( X65 != X57
        | r2_hidden(X65,X63)
        | X63 != k5_enumset1(X56,X57,X58,X59,X60,X61,X62) )
      & ( X65 != X58
        | r2_hidden(X65,X63)
        | X63 != k5_enumset1(X56,X57,X58,X59,X60,X61,X62) )
      & ( X65 != X59
        | r2_hidden(X65,X63)
        | X63 != k5_enumset1(X56,X57,X58,X59,X60,X61,X62) )
      & ( X65 != X60
        | r2_hidden(X65,X63)
        | X63 != k5_enumset1(X56,X57,X58,X59,X60,X61,X62) )
      & ( X65 != X61
        | r2_hidden(X65,X63)
        | X63 != k5_enumset1(X56,X57,X58,X59,X60,X61,X62) )
      & ( X65 != X62
        | r2_hidden(X65,X63)
        | X63 != k5_enumset1(X56,X57,X58,X59,X60,X61,X62) )
      & ( esk1_8(X66,X67,X68,X69,X70,X71,X72,X73) != X66
        | ~ r2_hidden(esk1_8(X66,X67,X68,X69,X70,X71,X72,X73),X73)
        | X73 = k5_enumset1(X66,X67,X68,X69,X70,X71,X72) )
      & ( esk1_8(X66,X67,X68,X69,X70,X71,X72,X73) != X67
        | ~ r2_hidden(esk1_8(X66,X67,X68,X69,X70,X71,X72,X73),X73)
        | X73 = k5_enumset1(X66,X67,X68,X69,X70,X71,X72) )
      & ( esk1_8(X66,X67,X68,X69,X70,X71,X72,X73) != X68
        | ~ r2_hidden(esk1_8(X66,X67,X68,X69,X70,X71,X72,X73),X73)
        | X73 = k5_enumset1(X66,X67,X68,X69,X70,X71,X72) )
      & ( esk1_8(X66,X67,X68,X69,X70,X71,X72,X73) != X69
        | ~ r2_hidden(esk1_8(X66,X67,X68,X69,X70,X71,X72,X73),X73)
        | X73 = k5_enumset1(X66,X67,X68,X69,X70,X71,X72) )
      & ( esk1_8(X66,X67,X68,X69,X70,X71,X72,X73) != X70
        | ~ r2_hidden(esk1_8(X66,X67,X68,X69,X70,X71,X72,X73),X73)
        | X73 = k5_enumset1(X66,X67,X68,X69,X70,X71,X72) )
      & ( esk1_8(X66,X67,X68,X69,X70,X71,X72,X73) != X71
        | ~ r2_hidden(esk1_8(X66,X67,X68,X69,X70,X71,X72,X73),X73)
        | X73 = k5_enumset1(X66,X67,X68,X69,X70,X71,X72) )
      & ( esk1_8(X66,X67,X68,X69,X70,X71,X72,X73) != X72
        | ~ r2_hidden(esk1_8(X66,X67,X68,X69,X70,X71,X72,X73),X73)
        | X73 = k5_enumset1(X66,X67,X68,X69,X70,X71,X72) )
      & ( r2_hidden(esk1_8(X66,X67,X68,X69,X70,X71,X72,X73),X73)
        | esk1_8(X66,X67,X68,X69,X70,X71,X72,X73) = X66
        | esk1_8(X66,X67,X68,X69,X70,X71,X72,X73) = X67
        | esk1_8(X66,X67,X68,X69,X70,X71,X72,X73) = X68
        | esk1_8(X66,X67,X68,X69,X70,X71,X72,X73) = X69
        | esk1_8(X66,X67,X68,X69,X70,X71,X72,X73) = X70
        | esk1_8(X66,X67,X68,X69,X70,X71,X72,X73) = X71
        | esk1_8(X66,X67,X68,X69,X70,X71,X72,X73) = X72
        | X73 = k5_enumset1(X66,X67,X68,X69,X70,X71,X72) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_enumset1])])])])])])).

cnf(c_0_32,plain,
    ( k2_xboole_0(k1_tarski(X1),k2_tarski(X1,X2)) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,plain,
    ( k3_enumset1(X1,X1,X1,X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,plain,
    ( k5_enumset1(X1,X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_36,plain,(
    ! [X10,X11] : k5_xboole_0(X10,X11) = k2_xboole_0(k4_xboole_0(X10,X11),k4_xboole_0(X11,X10)) ),
    inference(variable_rename,[status(thm)],[d6_xboole_0])).

fof(c_0_37,plain,(
    ! [X47,X48] :
      ( ~ r2_hidden(X47,X48)
      | r1_tarski(X47,k3_tarski(X48)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).

cnf(c_0_38,plain,
    ( k3_tarski(k2_tarski(X1,k3_xboole_0(X1,X2))) = X1 ),
    inference(rw,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_39,plain,
    ( k3_xboole_0(X1,k3_tarski(k2_tarski(X1,X2))) = X1 ),
    inference(rw,[status(thm)],[c_0_30,c_0_29])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k5_enumset1(X2,X4,X5,X6,X7,X8,X9) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_41,plain,
    ( k3_tarski(k2_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k2_tarski(X1,X2))) = k2_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_29]),c_0_33]),c_0_34])).

cnf(c_0_42,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k2_tarski(k5_enumset1(X1,X1,X1,X2,X3,X4,X5),k2_tarski(X6,X7))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_29]),c_0_34])).

fof(c_0_43,plain,(
    ! [X14,X15,X16] :
      ( ( r1_tarski(X14,k2_xboole_0(X15,X16))
        | ~ r1_tarski(X14,k5_xboole_0(X15,X16)) )
      & ( r1_xboole_0(X14,k3_xboole_0(X15,X16))
        | ~ r1_tarski(X14,k5_xboole_0(X15,X16)) )
      & ( ~ r1_tarski(X14,k2_xboole_0(X15,X16))
        | ~ r1_xboole_0(X14,k3_xboole_0(X15,X16))
        | r1_tarski(X14,k5_xboole_0(X15,X16)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t107_xboole_1])])])).

cnf(c_0_44,plain,
    ( k5_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_45,plain,(
    ! [X22,X23] : k4_xboole_0(k2_xboole_0(X22,X23),X23) = k4_xboole_0(X22,X23) ),
    inference(variable_rename,[status(thm)],[t40_xboole_1])).

fof(c_0_46,plain,(
    ! [X24,X25] :
      ( ~ r1_tarski(X24,X25)
      | X25 = k2_xboole_0(X24,k4_xboole_0(X25,X24)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_xboole_1])])).

cnf(c_0_47,plain,
    ( r1_tarski(X1,k3_tarski(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_48,plain,
    ( k3_tarski(k2_tarski(X1,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_49,plain,
    ( r2_hidden(X1,k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_40])])).

cnf(c_0_50,plain,
    ( k5_enumset1(X1,X1,X1,X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_41,c_0_42])).

fof(c_0_51,plain,(
    ! [X26,X27] : k2_xboole_0(k3_xboole_0(X26,X27),k4_xboole_0(X26,X27)) = X26 ),
    inference(variable_rename,[status(thm)],[t51_xboole_1])).

fof(c_0_52,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_ordinal1(X3)
       => ( ( r2_hidden(X1,X2)
            & r2_hidden(X2,X3) )
         => r2_hidden(X1,X3) ) ) ),
    inference(assume_negation,[status(cth)],[t19_ordinal1])).

cnf(c_0_53,plain,
    ( r1_xboole_0(X1,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_54,plain,
    ( k5_xboole_0(X1,X2) = k3_tarski(k2_tarski(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[c_0_44,c_0_29])).

fof(c_0_55,plain,(
    ! [X21] : r1_tarski(k1_xboole_0,X21) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_56,plain,(
    ! [X12,X13] :
      ( ( k4_xboole_0(X12,X13) != k1_xboole_0
        | r1_tarski(X12,X13) )
      & ( ~ r1_tarski(X12,X13)
        | k4_xboole_0(X12,X13) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_57,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_58,plain,
    ( X2 = k2_xboole_0(X1,k4_xboole_0(X2,X1))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_59,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k2_tarski(X2,X2)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_60,plain,
    ( r2_hidden(X1,k2_tarski(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_61,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_62,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k5_enumset1(X4,X5,X6,X7,X8,X9,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_63,plain,(
    ! [X75,X76,X77] :
      ( ( ~ v1_ordinal1(X75)
        | ~ r2_hidden(X76,X75)
        | r1_tarski(X76,X75) )
      & ( r2_hidden(esk2_1(X77),X77)
        | v1_ordinal1(X77) )
      & ( ~ r1_tarski(esk2_1(X77),X77)
        | v1_ordinal1(X77) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_ordinal1])])])])])])).

fof(c_0_64,negated_conjecture,
    ( v1_ordinal1(esk5_0)
    & r2_hidden(esk3_0,esk4_0)
    & r2_hidden(esk4_0,esk5_0)
    & ~ r2_hidden(esk3_0,esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_52])])])).

cnf(c_0_65,plain,
    ( r1_xboole_0(X1,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,k3_tarski(k2_tarski(k4_xboole_0(X2,X3),k4_xboole_0(X3,X2)))) ),
    inference(rw,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_66,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

fof(c_0_67,plain,(
    ! [X44,X45,X46] :
      ( ( ~ r2_hidden(X44,X46)
        | k4_xboole_0(k2_tarski(X44,X45),X46) != k1_tarski(X44) )
      & ( r2_hidden(X45,X46)
        | X44 = X45
        | k4_xboole_0(k2_tarski(X44,X45),X46) != k1_tarski(X44) )
      & ( ~ r2_hidden(X45,X46)
        | r2_hidden(X44,X46)
        | k4_xboole_0(k2_tarski(X44,X45),X46) = k1_tarski(X44) )
      & ( X44 != X45
        | r2_hidden(X44,X46)
        | k4_xboole_0(k2_tarski(X44,X45),X46) = k1_tarski(X44) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l38_zfmisc_1])])])])).

cnf(c_0_68,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_69,plain,
    ( k4_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_57,c_0_29])).

cnf(c_0_70,plain,
    ( X2 = k3_tarski(k2_tarski(X1,k4_xboole_0(X2,X1)))
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_58,c_0_29])).

cnf(c_0_71,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_72,plain,
    ( k3_tarski(k2_tarski(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))) = X1 ),
    inference(rw,[status(thm)],[c_0_61,c_0_29])).

cnf(c_0_73,plain,
    ( r2_hidden(X1,k5_enumset1(X2,X3,X4,X5,X6,X7,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_62])])).

cnf(c_0_74,plain,
    ( r1_tarski(X2,X1)
    | ~ v1_ordinal1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_75,negated_conjecture,
    ( r2_hidden(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_76,negated_conjecture,
    ( v1_ordinal1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

fof(c_0_77,plain,(
    ! [X28,X29,X30] :
      ( ~ r1_xboole_0(X28,k4_xboole_0(X29,X30))
      | r1_xboole_0(X29,k4_xboole_0(X28,X30)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t81_xboole_1])])).

cnf(c_0_78,plain,
    ( r1_xboole_0(k1_xboole_0,k3_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_79,plain,
    ( r2_hidden(X1,X3)
    | k4_xboole_0(k2_tarski(X1,X2),X3) = k1_tarski(X1)
    | X1 != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_80,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_68,c_0_66])).

cnf(c_0_81,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X1,X2))
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_82,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_68,c_0_71])).

cnf(c_0_83,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_39,c_0_38])).

cnf(c_0_84,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k2_tarski(k3_xboole_0(X2,X3),k4_xboole_0(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_47,c_0_72])).

cnf(c_0_85,plain,
    ( r2_hidden(X1,k2_tarski(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_50])).

cnf(c_0_86,negated_conjecture,
    ( r1_tarski(esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_76])])).

cnf(c_0_87,plain,
    ( r1_xboole_0(X2,k4_xboole_0(X1,X3))
    | ~ r1_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_88,plain,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_78,c_0_39])).

cnf(c_0_89,plain,
    ( k4_xboole_0(k2_tarski(X1,X2),X3) = k5_enumset1(X1,X1,X1,X1,X1,X1,X1)
    | r2_hidden(X1,X3)
    | X1 != X2 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_33]),c_0_34])).

cnf(c_0_90,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_66])])).

cnf(c_0_91,plain,
    ( k3_tarski(k2_tarski(X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_82]),c_0_83])).

cnf(c_0_92,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_93,negated_conjecture,
    ( k4_xboole_0(esk4_0,esk5_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_68,c_0_86])).

cnf(c_0_94,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_80])).

cnf(c_0_95,plain,
    ( k4_xboole_0(k2_tarski(X1,X1),X2) = k5_enumset1(X1,X1,X1,X1,X1,X1,X1)
    | r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_89])).

cnf(c_0_96,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_90]),c_0_91]),c_0_92])])).

cnf(c_0_97,negated_conjecture,
    ( r1_xboole_0(esk4_0,k4_xboole_0(X1,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_93]),c_0_94])])).

cnf(c_0_98,plain,
    ( k4_xboole_0(k2_tarski(X1,X1),X2) = k2_tarski(X1,X1)
    | r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_95,c_0_50])).

fof(c_0_99,plain,(
    ! [X53,X54,X55] :
      ( ~ r1_xboole_0(k2_tarski(X53,X54),X55)
      | ~ r2_hidden(X53,X55) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_zfmisc_1])])).

cnf(c_0_100,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_96]),c_0_96])).

cnf(c_0_101,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | r1_xboole_0(esk4_0,k2_tarski(X1,X1)) ),
    inference(spm,[status(thm)],[c_0_97,c_0_98])).

cnf(c_0_102,plain,
    ( ~ r1_xboole_0(k2_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_99])).

cnf(c_0_103,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | r1_xboole_0(k2_tarski(X1,X1),esk4_0) ),
    inference(spm,[status(thm)],[c_0_100,c_0_101])).

cnf(c_0_104,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_102,c_0_103])).

cnf(c_0_105,negated_conjecture,
    ( r2_hidden(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_106,negated_conjecture,
    ( ~ r2_hidden(esk3_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_107,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_105]),c_0_106]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 21:01:06 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.43  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.21/0.43  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.21/0.43  #
% 0.21/0.43  # Preprocessing time       : 0.029 s
% 0.21/0.43  # Presaturation interreduction done
% 0.21/0.43  
% 0.21/0.43  # Proof found!
% 0.21/0.43  # SZS status Theorem
% 0.21/0.43  # SZS output start CNFRefutation
% 0.21/0.43  fof(t22_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 0.21/0.43  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.21/0.43  fof(t21_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 0.21/0.43  fof(t14_zfmisc_1, axiom, ![X1, X2]:k2_xboole_0(k1_tarski(X1),k2_tarski(X1,X2))=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_zfmisc_1)).
% 0.21/0.43  fof(t87_enumset1, axiom, ![X1]:k3_enumset1(X1,X1,X1,X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_enumset1)).
% 0.21/0.43  fof(t80_enumset1, axiom, ![X1, X2, X3, X4, X5]:k5_enumset1(X1,X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_enumset1)).
% 0.21/0.43  fof(t60_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_tarski(X6,X7)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_enumset1)).
% 0.21/0.43  fof(d5_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:(X8=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)<=>![X9]:(r2_hidden(X9,X8)<=>~(((((((X9!=X1&X9!=X2)&X9!=X3)&X9!=X4)&X9!=X5)&X9!=X6)&X9!=X7)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_enumset1)).
% 0.21/0.43  fof(d6_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_xboole_0)).
% 0.21/0.43  fof(l49_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>r1_tarski(X1,k3_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 0.21/0.43  fof(t107_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k5_xboole_0(X2,X3))<=>(r1_tarski(X1,k2_xboole_0(X2,X3))&r1_xboole_0(X1,k3_xboole_0(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t107_xboole_1)).
% 0.21/0.43  fof(t40_xboole_1, axiom, ![X1, X2]:k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 0.21/0.43  fof(t45_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>X2=k2_xboole_0(X1,k4_xboole_0(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_xboole_1)).
% 0.21/0.43  fof(t51_xboole_1, axiom, ![X1, X2]:k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 0.21/0.43  fof(t19_ordinal1, conjecture, ![X1, X2, X3]:(v1_ordinal1(X3)=>((r2_hidden(X1,X2)&r2_hidden(X2,X3))=>r2_hidden(X1,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_ordinal1)).
% 0.21/0.43  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.21/0.43  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.21/0.43  fof(d2_ordinal1, axiom, ![X1]:(v1_ordinal1(X1)<=>![X2]:(r2_hidden(X2,X1)=>r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_ordinal1)).
% 0.21/0.43  fof(l38_zfmisc_1, axiom, ![X1, X2, X3]:(k4_xboole_0(k2_tarski(X1,X2),X3)=k1_tarski(X1)<=>(~(r2_hidden(X1,X3))&(r2_hidden(X2,X3)|X1=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l38_zfmisc_1)).
% 0.21/0.43  fof(t81_xboole_1, axiom, ![X1, X2, X3]:(r1_xboole_0(X1,k4_xboole_0(X2,X3))=>r1_xboole_0(X2,k4_xboole_0(X1,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_xboole_1)).
% 0.21/0.43  fof(t55_zfmisc_1, axiom, ![X1, X2, X3]:~((r1_xboole_0(k2_tarski(X1,X2),X3)&r2_hidden(X1,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 0.21/0.43  fof(c_0_21, plain, ![X19, X20]:k2_xboole_0(X19,k3_xboole_0(X19,X20))=X19, inference(variable_rename,[status(thm)],[t22_xboole_1])).
% 0.21/0.43  fof(c_0_22, plain, ![X49, X50]:k3_tarski(k2_tarski(X49,X50))=k2_xboole_0(X49,X50), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.21/0.43  fof(c_0_23, plain, ![X17, X18]:k3_xboole_0(X17,k2_xboole_0(X17,X18))=X17, inference(variable_rename,[status(thm)],[t21_xboole_1])).
% 0.21/0.43  fof(c_0_24, plain, ![X51, X52]:k2_xboole_0(k1_tarski(X51),k2_tarski(X51,X52))=k2_tarski(X51,X52), inference(variable_rename,[status(thm)],[t14_zfmisc_1])).
% 0.21/0.43  fof(c_0_25, plain, ![X43]:k3_enumset1(X43,X43,X43,X43,X43)=k1_tarski(X43), inference(variable_rename,[status(thm)],[t87_enumset1])).
% 0.21/0.43  fof(c_0_26, plain, ![X38, X39, X40, X41, X42]:k5_enumset1(X38,X38,X38,X39,X40,X41,X42)=k3_enumset1(X38,X39,X40,X41,X42), inference(variable_rename,[status(thm)],[t80_enumset1])).
% 0.21/0.43  fof(c_0_27, plain, ![X31, X32, X33, X34, X35, X36, X37]:k5_enumset1(X31,X32,X33,X34,X35,X36,X37)=k2_xboole_0(k3_enumset1(X31,X32,X33,X34,X35),k2_tarski(X36,X37)), inference(variable_rename,[status(thm)],[t60_enumset1])).
% 0.21/0.43  cnf(c_0_28, plain, (k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.43  cnf(c_0_29, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.43  cnf(c_0_30, plain, (k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.43  fof(c_0_31, plain, ![X56, X57, X58, X59, X60, X61, X62, X63, X64, X65, X66, X67, X68, X69, X70, X71, X72, X73]:(((~r2_hidden(X64,X63)|(X64=X56|X64=X57|X64=X58|X64=X59|X64=X60|X64=X61|X64=X62)|X63!=k5_enumset1(X56,X57,X58,X59,X60,X61,X62))&(((((((X65!=X56|r2_hidden(X65,X63)|X63!=k5_enumset1(X56,X57,X58,X59,X60,X61,X62))&(X65!=X57|r2_hidden(X65,X63)|X63!=k5_enumset1(X56,X57,X58,X59,X60,X61,X62)))&(X65!=X58|r2_hidden(X65,X63)|X63!=k5_enumset1(X56,X57,X58,X59,X60,X61,X62)))&(X65!=X59|r2_hidden(X65,X63)|X63!=k5_enumset1(X56,X57,X58,X59,X60,X61,X62)))&(X65!=X60|r2_hidden(X65,X63)|X63!=k5_enumset1(X56,X57,X58,X59,X60,X61,X62)))&(X65!=X61|r2_hidden(X65,X63)|X63!=k5_enumset1(X56,X57,X58,X59,X60,X61,X62)))&(X65!=X62|r2_hidden(X65,X63)|X63!=k5_enumset1(X56,X57,X58,X59,X60,X61,X62))))&((((((((esk1_8(X66,X67,X68,X69,X70,X71,X72,X73)!=X66|~r2_hidden(esk1_8(X66,X67,X68,X69,X70,X71,X72,X73),X73)|X73=k5_enumset1(X66,X67,X68,X69,X70,X71,X72))&(esk1_8(X66,X67,X68,X69,X70,X71,X72,X73)!=X67|~r2_hidden(esk1_8(X66,X67,X68,X69,X70,X71,X72,X73),X73)|X73=k5_enumset1(X66,X67,X68,X69,X70,X71,X72)))&(esk1_8(X66,X67,X68,X69,X70,X71,X72,X73)!=X68|~r2_hidden(esk1_8(X66,X67,X68,X69,X70,X71,X72,X73),X73)|X73=k5_enumset1(X66,X67,X68,X69,X70,X71,X72)))&(esk1_8(X66,X67,X68,X69,X70,X71,X72,X73)!=X69|~r2_hidden(esk1_8(X66,X67,X68,X69,X70,X71,X72,X73),X73)|X73=k5_enumset1(X66,X67,X68,X69,X70,X71,X72)))&(esk1_8(X66,X67,X68,X69,X70,X71,X72,X73)!=X70|~r2_hidden(esk1_8(X66,X67,X68,X69,X70,X71,X72,X73),X73)|X73=k5_enumset1(X66,X67,X68,X69,X70,X71,X72)))&(esk1_8(X66,X67,X68,X69,X70,X71,X72,X73)!=X71|~r2_hidden(esk1_8(X66,X67,X68,X69,X70,X71,X72,X73),X73)|X73=k5_enumset1(X66,X67,X68,X69,X70,X71,X72)))&(esk1_8(X66,X67,X68,X69,X70,X71,X72,X73)!=X72|~r2_hidden(esk1_8(X66,X67,X68,X69,X70,X71,X72,X73),X73)|X73=k5_enumset1(X66,X67,X68,X69,X70,X71,X72)))&(r2_hidden(esk1_8(X66,X67,X68,X69,X70,X71,X72,X73),X73)|(esk1_8(X66,X67,X68,X69,X70,X71,X72,X73)=X66|esk1_8(X66,X67,X68,X69,X70,X71,X72,X73)=X67|esk1_8(X66,X67,X68,X69,X70,X71,X72,X73)=X68|esk1_8(X66,X67,X68,X69,X70,X71,X72,X73)=X69|esk1_8(X66,X67,X68,X69,X70,X71,X72,X73)=X70|esk1_8(X66,X67,X68,X69,X70,X71,X72,X73)=X71|esk1_8(X66,X67,X68,X69,X70,X71,X72,X73)=X72)|X73=k5_enumset1(X66,X67,X68,X69,X70,X71,X72)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_enumset1])])])])])])).
% 0.21/0.43  cnf(c_0_32, plain, (k2_xboole_0(k1_tarski(X1),k2_tarski(X1,X2))=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.21/0.43  cnf(c_0_33, plain, (k3_enumset1(X1,X1,X1,X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.43  cnf(c_0_34, plain, (k5_enumset1(X1,X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.21/0.43  cnf(c_0_35, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_tarski(X6,X7))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.21/0.43  fof(c_0_36, plain, ![X10, X11]:k5_xboole_0(X10,X11)=k2_xboole_0(k4_xboole_0(X10,X11),k4_xboole_0(X11,X10)), inference(variable_rename,[status(thm)],[d6_xboole_0])).
% 0.21/0.43  fof(c_0_37, plain, ![X47, X48]:(~r2_hidden(X47,X48)|r1_tarski(X47,k3_tarski(X48))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).
% 0.21/0.43  cnf(c_0_38, plain, (k3_tarski(k2_tarski(X1,k3_xboole_0(X1,X2)))=X1), inference(rw,[status(thm)],[c_0_28, c_0_29])).
% 0.21/0.43  cnf(c_0_39, plain, (k3_xboole_0(X1,k3_tarski(k2_tarski(X1,X2)))=X1), inference(rw,[status(thm)],[c_0_30, c_0_29])).
% 0.21/0.43  cnf(c_0_40, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k5_enumset1(X2,X4,X5,X6,X7,X8,X9)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.21/0.43  cnf(c_0_41, plain, (k3_tarski(k2_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k2_tarski(X1,X2)))=k2_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_29]), c_0_33]), c_0_34])).
% 0.21/0.43  cnf(c_0_42, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k3_tarski(k2_tarski(k5_enumset1(X1,X1,X1,X2,X3,X4,X5),k2_tarski(X6,X7)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_29]), c_0_34])).
% 0.21/0.43  fof(c_0_43, plain, ![X14, X15, X16]:(((r1_tarski(X14,k2_xboole_0(X15,X16))|~r1_tarski(X14,k5_xboole_0(X15,X16)))&(r1_xboole_0(X14,k3_xboole_0(X15,X16))|~r1_tarski(X14,k5_xboole_0(X15,X16))))&(~r1_tarski(X14,k2_xboole_0(X15,X16))|~r1_xboole_0(X14,k3_xboole_0(X15,X16))|r1_tarski(X14,k5_xboole_0(X15,X16)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t107_xboole_1])])])).
% 0.21/0.43  cnf(c_0_44, plain, (k5_xboole_0(X1,X2)=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.21/0.43  fof(c_0_45, plain, ![X22, X23]:k4_xboole_0(k2_xboole_0(X22,X23),X23)=k4_xboole_0(X22,X23), inference(variable_rename,[status(thm)],[t40_xboole_1])).
% 0.21/0.43  fof(c_0_46, plain, ![X24, X25]:(~r1_tarski(X24,X25)|X25=k2_xboole_0(X24,k4_xboole_0(X25,X24))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_xboole_1])])).
% 0.21/0.43  cnf(c_0_47, plain, (r1_tarski(X1,k3_tarski(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.21/0.43  cnf(c_0_48, plain, (k3_tarski(k2_tarski(X1,X1))=X1), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.21/0.43  cnf(c_0_49, plain, (r2_hidden(X1,k5_enumset1(X1,X2,X3,X4,X5,X6,X7))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_40])])).
% 0.21/0.43  cnf(c_0_50, plain, (k5_enumset1(X1,X1,X1,X1,X1,X1,X2)=k2_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_41, c_0_42])).
% 0.21/0.43  fof(c_0_51, plain, ![X26, X27]:k2_xboole_0(k3_xboole_0(X26,X27),k4_xboole_0(X26,X27))=X26, inference(variable_rename,[status(thm)],[t51_xboole_1])).
% 0.21/0.43  fof(c_0_52, negated_conjecture, ~(![X1, X2, X3]:(v1_ordinal1(X3)=>((r2_hidden(X1,X2)&r2_hidden(X2,X3))=>r2_hidden(X1,X3)))), inference(assume_negation,[status(cth)],[t19_ordinal1])).
% 0.21/0.43  cnf(c_0_53, plain, (r1_xboole_0(X1,k3_xboole_0(X2,X3))|~r1_tarski(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.21/0.43  cnf(c_0_54, plain, (k5_xboole_0(X1,X2)=k3_tarski(k2_tarski(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)))), inference(rw,[status(thm)],[c_0_44, c_0_29])).
% 0.21/0.43  fof(c_0_55, plain, ![X21]:r1_tarski(k1_xboole_0,X21), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.21/0.43  fof(c_0_56, plain, ![X12, X13]:((k4_xboole_0(X12,X13)!=k1_xboole_0|r1_tarski(X12,X13))&(~r1_tarski(X12,X13)|k4_xboole_0(X12,X13)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.21/0.43  cnf(c_0_57, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.21/0.43  cnf(c_0_58, plain, (X2=k2_xboole_0(X1,k4_xboole_0(X2,X1))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.21/0.43  cnf(c_0_59, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k2_tarski(X2,X2))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.21/0.43  cnf(c_0_60, plain, (r2_hidden(X1,k2_tarski(X1,X2))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.21/0.43  cnf(c_0_61, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.21/0.43  cnf(c_0_62, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k5_enumset1(X4,X5,X6,X7,X8,X9,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.21/0.43  fof(c_0_63, plain, ![X75, X76, X77]:((~v1_ordinal1(X75)|(~r2_hidden(X76,X75)|r1_tarski(X76,X75)))&((r2_hidden(esk2_1(X77),X77)|v1_ordinal1(X77))&(~r1_tarski(esk2_1(X77),X77)|v1_ordinal1(X77)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_ordinal1])])])])])])).
% 0.21/0.43  fof(c_0_64, negated_conjecture, (v1_ordinal1(esk5_0)&((r2_hidden(esk3_0,esk4_0)&r2_hidden(esk4_0,esk5_0))&~r2_hidden(esk3_0,esk5_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_52])])])).
% 0.21/0.43  cnf(c_0_65, plain, (r1_xboole_0(X1,k3_xboole_0(X2,X3))|~r1_tarski(X1,k3_tarski(k2_tarski(k4_xboole_0(X2,X3),k4_xboole_0(X3,X2))))), inference(rw,[status(thm)],[c_0_53, c_0_54])).
% 0.21/0.43  cnf(c_0_66, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.21/0.43  fof(c_0_67, plain, ![X44, X45, X46]:(((~r2_hidden(X44,X46)|k4_xboole_0(k2_tarski(X44,X45),X46)!=k1_tarski(X44))&(r2_hidden(X45,X46)|X44=X45|k4_xboole_0(k2_tarski(X44,X45),X46)!=k1_tarski(X44)))&((~r2_hidden(X45,X46)|r2_hidden(X44,X46)|k4_xboole_0(k2_tarski(X44,X45),X46)=k1_tarski(X44))&(X44!=X45|r2_hidden(X44,X46)|k4_xboole_0(k2_tarski(X44,X45),X46)=k1_tarski(X44)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l38_zfmisc_1])])])])).
% 0.21/0.43  cnf(c_0_68, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.21/0.43  cnf(c_0_69, plain, (k4_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_57, c_0_29])).
% 0.21/0.43  cnf(c_0_70, plain, (X2=k3_tarski(k2_tarski(X1,k4_xboole_0(X2,X1)))|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_58, c_0_29])).
% 0.21/0.43  cnf(c_0_71, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.21/0.43  cnf(c_0_72, plain, (k3_tarski(k2_tarski(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)))=X1), inference(rw,[status(thm)],[c_0_61, c_0_29])).
% 0.21/0.43  cnf(c_0_73, plain, (r2_hidden(X1,k5_enumset1(X2,X3,X4,X5,X6,X7,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_62])])).
% 0.21/0.43  cnf(c_0_74, plain, (r1_tarski(X2,X1)|~v1_ordinal1(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.21/0.43  cnf(c_0_75, negated_conjecture, (r2_hidden(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.21/0.43  cnf(c_0_76, negated_conjecture, (v1_ordinal1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.21/0.43  fof(c_0_77, plain, ![X28, X29, X30]:(~r1_xboole_0(X28,k4_xboole_0(X29,X30))|r1_xboole_0(X29,k4_xboole_0(X28,X30))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t81_xboole_1])])).
% 0.21/0.43  cnf(c_0_78, plain, (r1_xboole_0(k1_xboole_0,k3_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.21/0.43  cnf(c_0_79, plain, (r2_hidden(X1,X3)|k4_xboole_0(k2_tarski(X1,X2),X3)=k1_tarski(X1)|X1!=X2), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.21/0.43  cnf(c_0_80, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_68, c_0_66])).
% 0.21/0.43  cnf(c_0_81, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X1,X2))|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.21/0.43  cnf(c_0_82, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_68, c_0_71])).
% 0.21/0.43  cnf(c_0_83, plain, (k3_xboole_0(X1,X1)=X1), inference(spm,[status(thm)],[c_0_39, c_0_38])).
% 0.21/0.43  cnf(c_0_84, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k2_tarski(k3_xboole_0(X2,X3),k4_xboole_0(X2,X3)))), inference(spm,[status(thm)],[c_0_47, c_0_72])).
% 0.21/0.43  cnf(c_0_85, plain, (r2_hidden(X1,k2_tarski(X2,X1))), inference(spm,[status(thm)],[c_0_73, c_0_50])).
% 0.21/0.43  cnf(c_0_86, negated_conjecture, (r1_tarski(esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_76])])).
% 0.21/0.43  cnf(c_0_87, plain, (r1_xboole_0(X2,k4_xboole_0(X1,X3))|~r1_xboole_0(X1,k4_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_77])).
% 0.21/0.43  cnf(c_0_88, plain, (r1_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_78, c_0_39])).
% 0.21/0.43  cnf(c_0_89, plain, (k4_xboole_0(k2_tarski(X1,X2),X3)=k5_enumset1(X1,X1,X1,X1,X1,X1,X1)|r2_hidden(X1,X3)|X1!=X2), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79, c_0_33]), c_0_34])).
% 0.21/0.43  cnf(c_0_90, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_66])])).
% 0.21/0.43  cnf(c_0_91, plain, (k3_tarski(k2_tarski(X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_82]), c_0_83])).
% 0.21/0.43  cnf(c_0_92, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_84, c_0_85])).
% 0.21/0.43  cnf(c_0_93, negated_conjecture, (k4_xboole_0(esk4_0,esk5_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_68, c_0_86])).
% 0.21/0.43  cnf(c_0_94, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_80])).
% 0.21/0.43  cnf(c_0_95, plain, (k4_xboole_0(k2_tarski(X1,X1),X2)=k5_enumset1(X1,X1,X1,X1,X1,X1,X1)|r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_89])).
% 0.21/0.43  cnf(c_0_96, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_90]), c_0_91]), c_0_92])])).
% 0.21/0.43  cnf(c_0_97, negated_conjecture, (r1_xboole_0(esk4_0,k4_xboole_0(X1,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_93]), c_0_94])])).
% 0.21/0.43  cnf(c_0_98, plain, (k4_xboole_0(k2_tarski(X1,X1),X2)=k2_tarski(X1,X1)|r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_95, c_0_50])).
% 0.21/0.43  fof(c_0_99, plain, ![X53, X54, X55]:(~r1_xboole_0(k2_tarski(X53,X54),X55)|~r2_hidden(X53,X55)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_zfmisc_1])])).
% 0.21/0.43  cnf(c_0_100, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_96]), c_0_96])).
% 0.21/0.43  cnf(c_0_101, negated_conjecture, (r2_hidden(X1,esk5_0)|r1_xboole_0(esk4_0,k2_tarski(X1,X1))), inference(spm,[status(thm)],[c_0_97, c_0_98])).
% 0.21/0.43  cnf(c_0_102, plain, (~r1_xboole_0(k2_tarski(X1,X2),X3)|~r2_hidden(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_99])).
% 0.21/0.43  cnf(c_0_103, negated_conjecture, (r2_hidden(X1,esk5_0)|r1_xboole_0(k2_tarski(X1,X1),esk4_0)), inference(spm,[status(thm)],[c_0_100, c_0_101])).
% 0.21/0.43  cnf(c_0_104, negated_conjecture, (r2_hidden(X1,esk5_0)|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_102, c_0_103])).
% 0.21/0.43  cnf(c_0_105, negated_conjecture, (r2_hidden(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.21/0.43  cnf(c_0_106, negated_conjecture, (~r2_hidden(esk3_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.21/0.43  cnf(c_0_107, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_105]), c_0_106]), ['proof']).
% 0.21/0.43  # SZS output end CNFRefutation
% 0.21/0.43  # Proof object total steps             : 108
% 0.21/0.43  # Proof object clause steps            : 65
% 0.21/0.43  # Proof object formula steps           : 43
% 0.21/0.43  # Proof object conjectures             : 14
% 0.21/0.43  # Proof object clause conjectures      : 11
% 0.21/0.43  # Proof object formula conjectures     : 3
% 0.21/0.43  # Proof object initial clauses used    : 25
% 0.21/0.43  # Proof object initial formulas used   : 21
% 0.21/0.43  # Proof object generating inferences   : 25
% 0.21/0.43  # Proof object simplifying inferences  : 34
% 0.21/0.43  # Training examples: 0 positive, 0 negative
% 0.21/0.43  # Parsed axioms                        : 21
% 0.21/0.43  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.43  # Initial clauses                      : 47
% 0.21/0.43  # Removed in clause preprocessing      : 4
% 0.21/0.43  # Initial clauses in saturation        : 43
% 0.21/0.43  # Processed clauses                    : 635
% 0.21/0.43  # ...of these trivial                  : 16
% 0.21/0.43  # ...subsumed                          : 274
% 0.21/0.43  # ...remaining for further processing  : 345
% 0.21/0.43  # Other redundant clauses eliminated   : 68
% 0.21/0.43  # Clauses deleted for lack of memory   : 0
% 0.21/0.43  # Backward-subsumed                    : 14
% 0.21/0.43  # Backward-rewritten                   : 56
% 0.21/0.43  # Generated clauses                    : 2157
% 0.21/0.43  # ...of the previous two non-trivial   : 1569
% 0.21/0.43  # Contextual simplify-reflections      : 1
% 0.21/0.43  # Paramodulations                      : 1927
% 0.21/0.43  # Factorizations                       : 168
% 0.21/0.43  # Equation resolutions                 : 69
% 0.21/0.43  # Propositional unsat checks           : 0
% 0.21/0.43  #    Propositional check models        : 0
% 0.21/0.43  #    Propositional check unsatisfiable : 0
% 0.21/0.43  #    Propositional clauses             : 0
% 0.21/0.43  #    Propositional clauses after purity: 0
% 0.21/0.43  #    Propositional unsat core size     : 0
% 0.21/0.43  #    Propositional preprocessing time  : 0.000
% 0.21/0.43  #    Propositional encoding time       : 0.000
% 0.21/0.43  #    Propositional solver time         : 0.000
% 0.21/0.43  #    Success case prop preproc time    : 0.000
% 0.21/0.43  #    Success case prop encoding time   : 0.000
% 0.21/0.43  #    Success case prop solver time     : 0.000
% 0.21/0.43  # Current number of processed clauses  : 223
% 0.21/0.43  #    Positive orientable unit clauses  : 55
% 0.21/0.43  #    Positive unorientable unit clauses: 0
% 0.21/0.43  #    Negative unit clauses             : 15
% 0.21/0.43  #    Non-unit-clauses                  : 153
% 0.21/0.43  # Current number of unprocessed clauses: 991
% 0.21/0.43  # ...number of literals in the above   : 2996
% 0.21/0.43  # Current number of archived formulas  : 0
% 0.21/0.43  # Current number of archived clauses   : 117
% 0.21/0.43  # Clause-clause subsumption calls (NU) : 4959
% 0.21/0.43  # Rec. Clause-clause subsumption calls : 4554
% 0.21/0.43  # Non-unit clause-clause subsumptions  : 152
% 0.21/0.43  # Unit Clause-clause subsumption calls : 860
% 0.21/0.43  # Rewrite failures with RHS unbound    : 0
% 0.21/0.43  # BW rewrite match attempts            : 146
% 0.21/0.43  # BW rewrite match successes           : 26
% 0.21/0.43  # Condensation attempts                : 0
% 0.21/0.43  # Condensation successes               : 0
% 0.21/0.43  # Termbank termtop insertions          : 25816
% 0.21/0.43  
% 0.21/0.43  # -------------------------------------------------
% 0.21/0.43  # User time                : 0.078 s
% 0.21/0.43  # System time              : 0.006 s
% 0.21/0.43  # Total time               : 0.084 s
% 0.21/0.43  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
