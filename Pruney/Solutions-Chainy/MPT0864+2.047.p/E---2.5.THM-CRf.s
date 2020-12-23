%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:59:24 EST 2020

% Result     : Theorem 0.42s
% Output     : CNFRefutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :   90 (5757 expanded)
%              Number of clauses        :   57 (2455 expanded)
%              Number of leaves         :   16 (1610 expanded)
%              Depth                    :   14
%              Number of atoms          :  255 (18292 expanded)
%              Number of equality atoms :  144 (10268 expanded)
%              Maximal formula depth    :   37 (   4 average)
%              Maximal clause size      :   52 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(t66_xboole_1,axiom,(
    ! [X1] :
      ( ~ ( ~ r1_xboole_0(X1,X1)
          & X1 = k1_xboole_0 )
      & ~ ( X1 != k1_xboole_0
          & r1_xboole_0(X1,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

fof(d4_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] :
      ( X7 = k4_enumset1(X1,X2,X3,X4,X5,X6)
    <=> ! [X8] :
          ( r2_hidden(X8,X7)
        <=> ~ ( X8 != X1
              & X8 != X2
              & X8 != X3
              & X8 != X4
              & X8 != X5
              & X8 != X6 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(t36_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3)) = k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3))
      & k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)) = k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(t20_mcart_1,conjecture,(
    ! [X1] :
      ( ? [X2,X3] : X1 = k4_tarski(X2,X3)
     => ( X1 != k1_mcart_1(X1)
        & X1 != k2_mcart_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

fof(d2_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_zfmisc_1(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ? [X5,X6] :
              ( r2_hidden(X5,X1)
              & r2_hidden(X6,X2)
              & X4 = k4_tarski(X5,X6) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(t7_mcart_1,axiom,(
    ! [X1,X2] :
      ( k1_mcart_1(k4_tarski(X1,X2)) = X1
      & k2_mcart_1(k4_tarski(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(t135_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( ( r1_tarski(X1,k2_zfmisc_1(X1,X2))
        | r1_tarski(X1,k2_zfmisc_1(X2,X1)) )
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t135_zfmisc_1)).

fof(l1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(c_0_16,plain,(
    ! [X9,X10,X12,X13,X14] :
      ( ( r2_hidden(esk1_2(X9,X10),X9)
        | r1_xboole_0(X9,X10) )
      & ( r2_hidden(esk1_2(X9,X10),X10)
        | r1_xboole_0(X9,X10) )
      & ( ~ r2_hidden(X14,X12)
        | ~ r2_hidden(X14,X13)
        | ~ r1_xboole_0(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_17,plain,(
    ! [X15] :
      ( ( r1_xboole_0(X15,X15)
        | X15 != k1_xboole_0 )
      & ( X15 = k1_xboole_0
        | ~ r1_xboole_0(X15,X15) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t66_xboole_1])])])).

cnf(c_0_18,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_19,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,plain,
    ( r1_xboole_0(X1,X1)
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_21,plain,(
    ! [X68,X69,X70,X71,X72,X73,X74,X75,X76,X77,X78,X79,X80,X81,X82,X83] :
      ( ( ~ r2_hidden(X75,X74)
        | X75 = X68
        | X75 = X69
        | X75 = X70
        | X75 = X71
        | X75 = X72
        | X75 = X73
        | X74 != k4_enumset1(X68,X69,X70,X71,X72,X73) )
      & ( X76 != X68
        | r2_hidden(X76,X74)
        | X74 != k4_enumset1(X68,X69,X70,X71,X72,X73) )
      & ( X76 != X69
        | r2_hidden(X76,X74)
        | X74 != k4_enumset1(X68,X69,X70,X71,X72,X73) )
      & ( X76 != X70
        | r2_hidden(X76,X74)
        | X74 != k4_enumset1(X68,X69,X70,X71,X72,X73) )
      & ( X76 != X71
        | r2_hidden(X76,X74)
        | X74 != k4_enumset1(X68,X69,X70,X71,X72,X73) )
      & ( X76 != X72
        | r2_hidden(X76,X74)
        | X74 != k4_enumset1(X68,X69,X70,X71,X72,X73) )
      & ( X76 != X73
        | r2_hidden(X76,X74)
        | X74 != k4_enumset1(X68,X69,X70,X71,X72,X73) )
      & ( esk7_7(X77,X78,X79,X80,X81,X82,X83) != X77
        | ~ r2_hidden(esk7_7(X77,X78,X79,X80,X81,X82,X83),X83)
        | X83 = k4_enumset1(X77,X78,X79,X80,X81,X82) )
      & ( esk7_7(X77,X78,X79,X80,X81,X82,X83) != X78
        | ~ r2_hidden(esk7_7(X77,X78,X79,X80,X81,X82,X83),X83)
        | X83 = k4_enumset1(X77,X78,X79,X80,X81,X82) )
      & ( esk7_7(X77,X78,X79,X80,X81,X82,X83) != X79
        | ~ r2_hidden(esk7_7(X77,X78,X79,X80,X81,X82,X83),X83)
        | X83 = k4_enumset1(X77,X78,X79,X80,X81,X82) )
      & ( esk7_7(X77,X78,X79,X80,X81,X82,X83) != X80
        | ~ r2_hidden(esk7_7(X77,X78,X79,X80,X81,X82,X83),X83)
        | X83 = k4_enumset1(X77,X78,X79,X80,X81,X82) )
      & ( esk7_7(X77,X78,X79,X80,X81,X82,X83) != X81
        | ~ r2_hidden(esk7_7(X77,X78,X79,X80,X81,X82,X83),X83)
        | X83 = k4_enumset1(X77,X78,X79,X80,X81,X82) )
      & ( esk7_7(X77,X78,X79,X80,X81,X82,X83) != X82
        | ~ r2_hidden(esk7_7(X77,X78,X79,X80,X81,X82,X83),X83)
        | X83 = k4_enumset1(X77,X78,X79,X80,X81,X82) )
      & ( r2_hidden(esk7_7(X77,X78,X79,X80,X81,X82,X83),X83)
        | esk7_7(X77,X78,X79,X80,X81,X82,X83) = X77
        | esk7_7(X77,X78,X79,X80,X81,X82,X83) = X78
        | esk7_7(X77,X78,X79,X80,X81,X82,X83) = X79
        | esk7_7(X77,X78,X79,X80,X81,X82,X83) = X80
        | esk7_7(X77,X78,X79,X80,X81,X82,X83) = X81
        | esk7_7(X77,X78,X79,X80,X81,X82,X83) = X82
        | X83 = k4_enumset1(X77,X78,X79,X80,X81,X82) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_enumset1])])])])])])).

fof(c_0_22,plain,(
    ! [X31,X32,X33,X34,X35,X36] : k5_enumset1(X31,X31,X32,X33,X34,X35,X36) = k4_enumset1(X31,X32,X33,X34,X35,X36) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_23,plain,(
    ! [X37,X38,X39,X40,X41,X42,X43] : k6_enumset1(X37,X37,X38,X39,X40,X41,X42,X43) = k5_enumset1(X37,X38,X39,X40,X41,X42,X43) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

cnf(c_0_24,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X3)
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_26,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k4_enumset1(X4,X5,X6,X7,X8,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_30,plain,(
    ! [X65,X66,X67] :
      ( k2_zfmisc_1(k1_tarski(X65),k2_tarski(X66,X67)) = k2_tarski(k4_tarski(X65,X66),k4_tarski(X65,X67))
      & k2_zfmisc_1(k2_tarski(X65,X66),k1_tarski(X67)) = k2_tarski(k4_tarski(X65,X67),k4_tarski(X66,X67)) ) ),
    inference(variable_rename,[status(thm)],[t36_zfmisc_1])).

fof(c_0_31,plain,(
    ! [X16] : k2_tarski(X16,X16) = k1_tarski(X16) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_32,plain,(
    ! [X17,X18] : k1_enumset1(X17,X17,X18) = k2_tarski(X17,X18) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_33,plain,(
    ! [X19,X20,X21] : k2_enumset1(X19,X19,X20,X21) = k1_enumset1(X19,X20,X21) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_34,plain,(
    ! [X22,X23,X24,X25] : k3_enumset1(X22,X22,X23,X24,X25) = k2_enumset1(X22,X23,X24,X25) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_35,plain,(
    ! [X26,X27,X28,X29,X30] : k4_enumset1(X26,X26,X27,X28,X29,X30) = k3_enumset1(X26,X27,X28,X29,X30) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_36,negated_conjecture,(
    ~ ! [X1] :
        ( ? [X2,X3] : X1 = k4_tarski(X2,X3)
       => ( X1 != k1_mcart_1(X1)
          & X1 != k2_mcart_1(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t20_mcart_1])).

fof(c_0_37,plain,(
    ! [X44,X45,X46,X47,X50,X51,X52,X53,X54,X55,X57,X58] :
      ( ( r2_hidden(esk2_4(X44,X45,X46,X47),X44)
        | ~ r2_hidden(X47,X46)
        | X46 != k2_zfmisc_1(X44,X45) )
      & ( r2_hidden(esk3_4(X44,X45,X46,X47),X45)
        | ~ r2_hidden(X47,X46)
        | X46 != k2_zfmisc_1(X44,X45) )
      & ( X47 = k4_tarski(esk2_4(X44,X45,X46,X47),esk3_4(X44,X45,X46,X47))
        | ~ r2_hidden(X47,X46)
        | X46 != k2_zfmisc_1(X44,X45) )
      & ( ~ r2_hidden(X51,X44)
        | ~ r2_hidden(X52,X45)
        | X50 != k4_tarski(X51,X52)
        | r2_hidden(X50,X46)
        | X46 != k2_zfmisc_1(X44,X45) )
      & ( ~ r2_hidden(esk4_3(X53,X54,X55),X55)
        | ~ r2_hidden(X57,X53)
        | ~ r2_hidden(X58,X54)
        | esk4_3(X53,X54,X55) != k4_tarski(X57,X58)
        | X55 = k2_zfmisc_1(X53,X54) )
      & ( r2_hidden(esk5_3(X53,X54,X55),X53)
        | r2_hidden(esk4_3(X53,X54,X55),X55)
        | X55 = k2_zfmisc_1(X53,X54) )
      & ( r2_hidden(esk6_3(X53,X54,X55),X54)
        | r2_hidden(esk4_3(X53,X54,X55),X55)
        | X55 = k2_zfmisc_1(X53,X54) )
      & ( esk4_3(X53,X54,X55) = k4_tarski(esk5_3(X53,X54,X55),esk6_3(X53,X54,X55))
        | r2_hidden(esk4_3(X53,X54,X55),X55)
        | X55 = k2_zfmisc_1(X53,X54) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).

cnf(c_0_38,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X3)
    | ~ r1_xboole_0(X3,X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_24])).

cnf(c_0_39,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_19])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k6_enumset1(X4,X4,X4,X5,X6,X7,X8,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_28]),c_0_29])).

cnf(c_0_41,plain,
    ( k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)) = k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_42,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_43,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_44,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_45,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_46,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_47,negated_conjecture,
    ( esk8_0 = k4_tarski(esk9_0,esk10_0)
    & ( esk8_0 = k1_mcart_1(esk8_0)
      | esk8_0 = k2_mcart_1(esk8_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_36])])])).

fof(c_0_48,plain,(
    ! [X85,X86] :
      ( k1_mcart_1(k4_tarski(X85,X86)) = X85
      & k2_mcart_1(k4_tarski(X85,X86)) = X86 ) ),
    inference(variable_rename,[status(thm)],[t7_mcart_1])).

cnf(c_0_49,plain,
    ( r2_hidden(esk6_3(X1,X2,X3),X2)
    | r2_hidden(esk4_3(X1,X2,X3),X3)
    | X3 = k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_50,plain,
    ( r1_xboole_0(k1_xboole_0,X1)
    | ~ r2_hidden(esk1_2(k1_xboole_0,X1),X2) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_51,plain,
    ( r2_hidden(X1,k6_enumset1(X2,X2,X2,X3,X4,X5,X6,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_40])])).

fof(c_0_52,plain,(
    ! [X63,X64] :
      ( ( ~ r1_tarski(X63,k2_zfmisc_1(X63,X64))
        | X63 = k1_xboole_0 )
      & ( ~ r1_tarski(X63,k2_zfmisc_1(X64,X63))
        | X63 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t135_zfmisc_1])])])).

cnf(c_0_53,plain,
    ( k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)) = k6_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_42]),c_0_43]),c_0_43]),c_0_43]),c_0_44]),c_0_44]),c_0_44]),c_0_45]),c_0_45]),c_0_45]),c_0_46]),c_0_46]),c_0_46]),c_0_28]),c_0_28]),c_0_28]),c_0_29]),c_0_29]),c_0_29])).

cnf(c_0_54,negated_conjecture,
    ( esk8_0 = k4_tarski(esk9_0,esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_55,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_56,plain,
    ( X1 = k2_zfmisc_1(X2,X3)
    | r2_hidden(esk4_3(X2,X3,X1),X1)
    | ~ r2_hidden(esk6_3(X2,X3,X1),X4)
    | ~ r1_xboole_0(X4,X3) ),
    inference(spm,[status(thm)],[c_0_18,c_0_49])).

cnf(c_0_57,plain,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_58,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_59,negated_conjecture,
    ( k2_zfmisc_1(k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,X1),k6_enumset1(esk10_0,esk10_0,esk10_0,esk10_0,esk10_0,esk10_0,esk10_0,esk10_0)) = k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,k4_tarski(X1,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_60,negated_conjecture,
    ( esk8_0 = k1_mcart_1(esk8_0)
    | esk8_0 = k2_mcart_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_61,negated_conjecture,
    ( k1_mcart_1(esk8_0) = esk9_0 ),
    inference(spm,[status(thm)],[c_0_55,c_0_54])).

cnf(c_0_62,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

fof(c_0_63,plain,(
    ! [X61,X62] :
      ( ( ~ r1_tarski(k1_tarski(X61),X62)
        | r2_hidden(X61,X62) )
      & ( ~ r2_hidden(X61,X62)
        | r1_tarski(k1_tarski(X61),X62) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).

cnf(c_0_64,plain,
    ( X1 = k2_zfmisc_1(X2,X3)
    | r2_hidden(esk4_3(X2,X3,X1),X1)
    | ~ r2_hidden(esk6_3(X2,X3,X1),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_65,negated_conjecture,
    ( k6_enumset1(esk10_0,esk10_0,esk10_0,esk10_0,esk10_0,esk10_0,esk10_0,esk10_0) = k1_xboole_0
    | ~ r1_tarski(k6_enumset1(esk10_0,esk10_0,esk10_0,esk10_0,esk10_0,esk10_0,esk10_0,esk10_0),k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,k4_tarski(X1,esk10_0))) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_66,negated_conjecture,
    ( k2_mcart_1(esk8_0) = esk8_0
    | esk9_0 = esk8_0 ),
    inference(rw,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_67,negated_conjecture,
    ( k2_mcart_1(esk8_0) = esk10_0 ),
    inference(spm,[status(thm)],[c_0_62,c_0_54])).

cnf(c_0_68,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_69,plain,
    ( X1 = k2_zfmisc_1(X2,k1_xboole_0)
    | r2_hidden(esk4_3(X2,k1_xboole_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_64,c_0_49])).

cnf(c_0_70,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_xboole_0(X2,k6_enumset1(X3,X3,X3,X4,X5,X6,X7,X1)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_51])).

cnf(c_0_71,plain,
    ( k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3)) = k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_72,negated_conjecture,
    ( k6_enumset1(esk10_0,esk10_0,esk10_0,esk10_0,esk10_0,esk10_0,esk10_0,esk10_0) = k1_xboole_0
    | ~ r1_tarski(k6_enumset1(esk10_0,esk10_0,esk10_0,esk10_0,esk10_0,esk10_0,esk10_0,esk10_0),k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_54])).

cnf(c_0_73,negated_conjecture,
    ( esk9_0 = esk8_0
    | esk10_0 = esk8_0 ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_74,plain,
    ( r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_42]),c_0_43]),c_0_44]),c_0_45]),c_0_46]),c_0_28]),c_0_29])).

cnf(c_0_75,plain,
    ( X1 = k2_zfmisc_1(X2,k1_xboole_0)
    | ~ r2_hidden(esk4_3(X2,k1_xboole_0,X1),X3)
    | ~ r1_xboole_0(X3,X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_69])).

cnf(c_0_76,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_77,plain,
    ( ~ r1_xboole_0(k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X7,X7,X7,X8,X9,X10,X11,X6)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_51])).

cnf(c_0_78,plain,
    ( k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)) = k6_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_42]),c_0_43]),c_0_43]),c_0_43]),c_0_44]),c_0_44]),c_0_44]),c_0_45]),c_0_45]),c_0_45]),c_0_46]),c_0_46]),c_0_46]),c_0_28]),c_0_28]),c_0_28]),c_0_29]),c_0_29]),c_0_29])).

cnf(c_0_79,negated_conjecture,
    ( k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0) = k1_xboole_0
    | esk9_0 = esk8_0
    | ~ r1_tarski(k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0),k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_80,plain,
    ( r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X2,X2,X2,X3,X4,X5,X6,X1)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_51])).

cnf(c_0_81,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0
    | ~ r2_hidden(esk4_3(X1,k1_xboole_0,k1_xboole_0),X2) ),
    inference(spm,[status(thm)],[c_0_75,c_0_39])).

cnf(c_0_82,negated_conjecture,
    ( k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,X1) = k1_xboole_0
    | ~ r1_tarski(k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,X1),k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,k4_tarski(X1,esk10_0))) ),
    inference(spm,[status(thm)],[c_0_76,c_0_59])).

cnf(c_0_83,plain,
    ( ~ r1_xboole_0(k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)),k6_enumset1(X4,X4,X4,X5,X6,X7,X8,k4_tarski(X1,X3))) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_84,negated_conjecture,
    ( k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0) = k1_xboole_0
    | esk9_0 = esk8_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_80])])).

cnf(c_0_85,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_81,c_0_51])).

cnf(c_0_86,negated_conjecture,
    ( k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0) = k1_xboole_0
    | ~ r1_tarski(k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0),k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_82,c_0_54])).

cnf(c_0_87,negated_conjecture,
    ( esk9_0 = esk8_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_85]),c_0_57])])).

cnf(c_0_88,negated_conjecture,
    ( k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_86,c_0_87]),c_0_87]),c_0_87]),c_0_87]),c_0_87]),c_0_87]),c_0_87]),c_0_87]),c_0_87]),c_0_87]),c_0_87]),c_0_87]),c_0_87]),c_0_87]),c_0_87]),c_0_87]),c_0_80])])).

cnf(c_0_89,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_88]),c_0_85]),c_0_57])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:43:35 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.42/0.57  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S054N
% 0.42/0.57  # and selection function GSelectMinInfpos.
% 0.42/0.57  #
% 0.42/0.57  # Preprocessing time       : 0.029 s
% 0.42/0.57  # Presaturation interreduction done
% 0.42/0.57  
% 0.42/0.57  # Proof found!
% 0.42/0.57  # SZS status Theorem
% 0.42/0.57  # SZS output start CNFRefutation
% 0.42/0.57  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.42/0.57  fof(t66_xboole_1, axiom, ![X1]:(~((~(r1_xboole_0(X1,X1))&X1=k1_xboole_0))&~((X1!=k1_xboole_0&r1_xboole_0(X1,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 0.42/0.57  fof(d4_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:(X7=k4_enumset1(X1,X2,X3,X4,X5,X6)<=>![X8]:(r2_hidden(X8,X7)<=>~((((((X8!=X1&X8!=X2)&X8!=X3)&X8!=X4)&X8!=X5)&X8!=X6)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_enumset1)).
% 0.42/0.57  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.42/0.57  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 0.42/0.57  fof(t36_zfmisc_1, axiom, ![X1, X2, X3]:(k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3))=k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3))&k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))=k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_zfmisc_1)).
% 0.42/0.57  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.42/0.57  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.42/0.57  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.42/0.57  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.42/0.57  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.42/0.57  fof(t20_mcart_1, conjecture, ![X1]:(?[X2, X3]:X1=k4_tarski(X2,X3)=>(X1!=k1_mcart_1(X1)&X1!=k2_mcart_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_mcart_1)).
% 0.42/0.57  fof(d2_zfmisc_1, axiom, ![X1, X2, X3]:(X3=k2_zfmisc_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5, X6]:((r2_hidden(X5,X1)&r2_hidden(X6,X2))&X4=k4_tarski(X5,X6)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 0.42/0.57  fof(t7_mcart_1, axiom, ![X1, X2]:(k1_mcart_1(k4_tarski(X1,X2))=X1&k2_mcart_1(k4_tarski(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 0.42/0.57  fof(t135_zfmisc_1, axiom, ![X1, X2]:((r1_tarski(X1,k2_zfmisc_1(X1,X2))|r1_tarski(X1,k2_zfmisc_1(X2,X1)))=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t135_zfmisc_1)).
% 0.42/0.57  fof(l1_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 0.42/0.57  fof(c_0_16, plain, ![X9, X10, X12, X13, X14]:(((r2_hidden(esk1_2(X9,X10),X9)|r1_xboole_0(X9,X10))&(r2_hidden(esk1_2(X9,X10),X10)|r1_xboole_0(X9,X10)))&(~r2_hidden(X14,X12)|~r2_hidden(X14,X13)|~r1_xboole_0(X12,X13))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.42/0.57  fof(c_0_17, plain, ![X15]:((r1_xboole_0(X15,X15)|X15!=k1_xboole_0)&(X15=k1_xboole_0|~r1_xboole_0(X15,X15))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t66_xboole_1])])])).
% 0.42/0.57  cnf(c_0_18, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.42/0.57  cnf(c_0_19, plain, (r2_hidden(esk1_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.42/0.57  cnf(c_0_20, plain, (r1_xboole_0(X1,X1)|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.42/0.57  fof(c_0_21, plain, ![X68, X69, X70, X71, X72, X73, X74, X75, X76, X77, X78, X79, X80, X81, X82, X83]:(((~r2_hidden(X75,X74)|(X75=X68|X75=X69|X75=X70|X75=X71|X75=X72|X75=X73)|X74!=k4_enumset1(X68,X69,X70,X71,X72,X73))&((((((X76!=X68|r2_hidden(X76,X74)|X74!=k4_enumset1(X68,X69,X70,X71,X72,X73))&(X76!=X69|r2_hidden(X76,X74)|X74!=k4_enumset1(X68,X69,X70,X71,X72,X73)))&(X76!=X70|r2_hidden(X76,X74)|X74!=k4_enumset1(X68,X69,X70,X71,X72,X73)))&(X76!=X71|r2_hidden(X76,X74)|X74!=k4_enumset1(X68,X69,X70,X71,X72,X73)))&(X76!=X72|r2_hidden(X76,X74)|X74!=k4_enumset1(X68,X69,X70,X71,X72,X73)))&(X76!=X73|r2_hidden(X76,X74)|X74!=k4_enumset1(X68,X69,X70,X71,X72,X73))))&(((((((esk7_7(X77,X78,X79,X80,X81,X82,X83)!=X77|~r2_hidden(esk7_7(X77,X78,X79,X80,X81,X82,X83),X83)|X83=k4_enumset1(X77,X78,X79,X80,X81,X82))&(esk7_7(X77,X78,X79,X80,X81,X82,X83)!=X78|~r2_hidden(esk7_7(X77,X78,X79,X80,X81,X82,X83),X83)|X83=k4_enumset1(X77,X78,X79,X80,X81,X82)))&(esk7_7(X77,X78,X79,X80,X81,X82,X83)!=X79|~r2_hidden(esk7_7(X77,X78,X79,X80,X81,X82,X83),X83)|X83=k4_enumset1(X77,X78,X79,X80,X81,X82)))&(esk7_7(X77,X78,X79,X80,X81,X82,X83)!=X80|~r2_hidden(esk7_7(X77,X78,X79,X80,X81,X82,X83),X83)|X83=k4_enumset1(X77,X78,X79,X80,X81,X82)))&(esk7_7(X77,X78,X79,X80,X81,X82,X83)!=X81|~r2_hidden(esk7_7(X77,X78,X79,X80,X81,X82,X83),X83)|X83=k4_enumset1(X77,X78,X79,X80,X81,X82)))&(esk7_7(X77,X78,X79,X80,X81,X82,X83)!=X82|~r2_hidden(esk7_7(X77,X78,X79,X80,X81,X82,X83),X83)|X83=k4_enumset1(X77,X78,X79,X80,X81,X82)))&(r2_hidden(esk7_7(X77,X78,X79,X80,X81,X82,X83),X83)|(esk7_7(X77,X78,X79,X80,X81,X82,X83)=X77|esk7_7(X77,X78,X79,X80,X81,X82,X83)=X78|esk7_7(X77,X78,X79,X80,X81,X82,X83)=X79|esk7_7(X77,X78,X79,X80,X81,X82,X83)=X80|esk7_7(X77,X78,X79,X80,X81,X82,X83)=X81|esk7_7(X77,X78,X79,X80,X81,X82,X83)=X82)|X83=k4_enumset1(X77,X78,X79,X80,X81,X82)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_enumset1])])])])])])).
% 0.42/0.57  fof(c_0_22, plain, ![X31, X32, X33, X34, X35, X36]:k5_enumset1(X31,X31,X32,X33,X34,X35,X36)=k4_enumset1(X31,X32,X33,X34,X35,X36), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.42/0.57  fof(c_0_23, plain, ![X37, X38, X39, X40, X41, X42, X43]:k6_enumset1(X37,X37,X38,X39,X40,X41,X42,X43)=k5_enumset1(X37,X38,X39,X40,X41,X42,X43), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.42/0.57  cnf(c_0_24, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.42/0.57  cnf(c_0_25, plain, (r1_xboole_0(X1,X2)|~r2_hidden(esk1_2(X1,X2),X3)|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.42/0.57  cnf(c_0_26, plain, (r1_xboole_0(k1_xboole_0,k1_xboole_0)), inference(er,[status(thm)],[c_0_20])).
% 0.42/0.57  cnf(c_0_27, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k4_enumset1(X4,X5,X6,X7,X8,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.42/0.57  cnf(c_0_28, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.42/0.57  cnf(c_0_29, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.42/0.57  fof(c_0_30, plain, ![X65, X66, X67]:(k2_zfmisc_1(k1_tarski(X65),k2_tarski(X66,X67))=k2_tarski(k4_tarski(X65,X66),k4_tarski(X65,X67))&k2_zfmisc_1(k2_tarski(X65,X66),k1_tarski(X67))=k2_tarski(k4_tarski(X65,X67),k4_tarski(X66,X67))), inference(variable_rename,[status(thm)],[t36_zfmisc_1])).
% 0.42/0.57  fof(c_0_31, plain, ![X16]:k2_tarski(X16,X16)=k1_tarski(X16), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.42/0.57  fof(c_0_32, plain, ![X17, X18]:k1_enumset1(X17,X17,X18)=k2_tarski(X17,X18), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.42/0.57  fof(c_0_33, plain, ![X19, X20, X21]:k2_enumset1(X19,X19,X20,X21)=k1_enumset1(X19,X20,X21), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.42/0.57  fof(c_0_34, plain, ![X22, X23, X24, X25]:k3_enumset1(X22,X22,X23,X24,X25)=k2_enumset1(X22,X23,X24,X25), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.42/0.57  fof(c_0_35, plain, ![X26, X27, X28, X29, X30]:k4_enumset1(X26,X26,X27,X28,X29,X30)=k3_enumset1(X26,X27,X28,X29,X30), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.42/0.57  fof(c_0_36, negated_conjecture, ~(![X1]:(?[X2, X3]:X1=k4_tarski(X2,X3)=>(X1!=k1_mcart_1(X1)&X1!=k2_mcart_1(X1)))), inference(assume_negation,[status(cth)],[t20_mcart_1])).
% 0.42/0.57  fof(c_0_37, plain, ![X44, X45, X46, X47, X50, X51, X52, X53, X54, X55, X57, X58]:(((((r2_hidden(esk2_4(X44,X45,X46,X47),X44)|~r2_hidden(X47,X46)|X46!=k2_zfmisc_1(X44,X45))&(r2_hidden(esk3_4(X44,X45,X46,X47),X45)|~r2_hidden(X47,X46)|X46!=k2_zfmisc_1(X44,X45)))&(X47=k4_tarski(esk2_4(X44,X45,X46,X47),esk3_4(X44,X45,X46,X47))|~r2_hidden(X47,X46)|X46!=k2_zfmisc_1(X44,X45)))&(~r2_hidden(X51,X44)|~r2_hidden(X52,X45)|X50!=k4_tarski(X51,X52)|r2_hidden(X50,X46)|X46!=k2_zfmisc_1(X44,X45)))&((~r2_hidden(esk4_3(X53,X54,X55),X55)|(~r2_hidden(X57,X53)|~r2_hidden(X58,X54)|esk4_3(X53,X54,X55)!=k4_tarski(X57,X58))|X55=k2_zfmisc_1(X53,X54))&(((r2_hidden(esk5_3(X53,X54,X55),X53)|r2_hidden(esk4_3(X53,X54,X55),X55)|X55=k2_zfmisc_1(X53,X54))&(r2_hidden(esk6_3(X53,X54,X55),X54)|r2_hidden(esk4_3(X53,X54,X55),X55)|X55=k2_zfmisc_1(X53,X54)))&(esk4_3(X53,X54,X55)=k4_tarski(esk5_3(X53,X54,X55),esk6_3(X53,X54,X55))|r2_hidden(esk4_3(X53,X54,X55),X55)|X55=k2_zfmisc_1(X53,X54))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).
% 0.42/0.57  cnf(c_0_38, plain, (r1_xboole_0(X1,X2)|~r2_hidden(esk1_2(X1,X2),X3)|~r1_xboole_0(X3,X1)), inference(spm,[status(thm)],[c_0_18, c_0_24])).
% 0.42/0.57  cnf(c_0_39, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_19])).
% 0.42/0.57  cnf(c_0_40, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k6_enumset1(X4,X4,X4,X5,X6,X7,X8,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_28]), c_0_29])).
% 0.42/0.57  cnf(c_0_41, plain, (k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))=k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.42/0.57  cnf(c_0_42, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.42/0.57  cnf(c_0_43, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.42/0.57  cnf(c_0_44, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.42/0.57  cnf(c_0_45, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.42/0.57  cnf(c_0_46, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.42/0.57  fof(c_0_47, negated_conjecture, (esk8_0=k4_tarski(esk9_0,esk10_0)&(esk8_0=k1_mcart_1(esk8_0)|esk8_0=k2_mcart_1(esk8_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_36])])])).
% 0.42/0.57  fof(c_0_48, plain, ![X85, X86]:(k1_mcart_1(k4_tarski(X85,X86))=X85&k2_mcart_1(k4_tarski(X85,X86))=X86), inference(variable_rename,[status(thm)],[t7_mcart_1])).
% 0.42/0.57  cnf(c_0_49, plain, (r2_hidden(esk6_3(X1,X2,X3),X2)|r2_hidden(esk4_3(X1,X2,X3),X3)|X3=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.42/0.57  cnf(c_0_50, plain, (r1_xboole_0(k1_xboole_0,X1)|~r2_hidden(esk1_2(k1_xboole_0,X1),X2)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.42/0.57  cnf(c_0_51, plain, (r2_hidden(X1,k6_enumset1(X2,X2,X2,X3,X4,X5,X6,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_40])])).
% 0.42/0.57  fof(c_0_52, plain, ![X63, X64]:((~r1_tarski(X63,k2_zfmisc_1(X63,X64))|X63=k1_xboole_0)&(~r1_tarski(X63,k2_zfmisc_1(X64,X63))|X63=k1_xboole_0)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t135_zfmisc_1])])])).
% 0.42/0.57  cnf(c_0_53, plain, (k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3))=k6_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_42]), c_0_43]), c_0_43]), c_0_43]), c_0_44]), c_0_44]), c_0_44]), c_0_45]), c_0_45]), c_0_45]), c_0_46]), c_0_46]), c_0_46]), c_0_28]), c_0_28]), c_0_28]), c_0_29]), c_0_29]), c_0_29])).
% 0.42/0.57  cnf(c_0_54, negated_conjecture, (esk8_0=k4_tarski(esk9_0,esk10_0)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.42/0.57  cnf(c_0_55, plain, (k1_mcart_1(k4_tarski(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.42/0.57  cnf(c_0_56, plain, (X1=k2_zfmisc_1(X2,X3)|r2_hidden(esk4_3(X2,X3,X1),X1)|~r2_hidden(esk6_3(X2,X3,X1),X4)|~r1_xboole_0(X4,X3)), inference(spm,[status(thm)],[c_0_18, c_0_49])).
% 0.42/0.57  cnf(c_0_57, plain, (r1_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.42/0.57  cnf(c_0_58, plain, (X1=k1_xboole_0|~r1_tarski(X1,k2_zfmisc_1(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.42/0.57  cnf(c_0_59, negated_conjecture, (k2_zfmisc_1(k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,X1),k6_enumset1(esk10_0,esk10_0,esk10_0,esk10_0,esk10_0,esk10_0,esk10_0,esk10_0))=k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,k4_tarski(X1,esk10_0))), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.42/0.57  cnf(c_0_60, negated_conjecture, (esk8_0=k1_mcart_1(esk8_0)|esk8_0=k2_mcart_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.42/0.57  cnf(c_0_61, negated_conjecture, (k1_mcart_1(esk8_0)=esk9_0), inference(spm,[status(thm)],[c_0_55, c_0_54])).
% 0.42/0.57  cnf(c_0_62, plain, (k2_mcart_1(k4_tarski(X1,X2))=X2), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.42/0.57  fof(c_0_63, plain, ![X61, X62]:((~r1_tarski(k1_tarski(X61),X62)|r2_hidden(X61,X62))&(~r2_hidden(X61,X62)|r1_tarski(k1_tarski(X61),X62))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).
% 0.42/0.57  cnf(c_0_64, plain, (X1=k2_zfmisc_1(X2,X3)|r2_hidden(esk4_3(X2,X3,X1),X1)|~r2_hidden(esk6_3(X2,X3,X1),k1_xboole_0)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.42/0.57  cnf(c_0_65, negated_conjecture, (k6_enumset1(esk10_0,esk10_0,esk10_0,esk10_0,esk10_0,esk10_0,esk10_0,esk10_0)=k1_xboole_0|~r1_tarski(k6_enumset1(esk10_0,esk10_0,esk10_0,esk10_0,esk10_0,esk10_0,esk10_0,esk10_0),k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,k4_tarski(X1,esk10_0)))), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.42/0.57  cnf(c_0_66, negated_conjecture, (k2_mcart_1(esk8_0)=esk8_0|esk9_0=esk8_0), inference(rw,[status(thm)],[c_0_60, c_0_61])).
% 0.42/0.57  cnf(c_0_67, negated_conjecture, (k2_mcart_1(esk8_0)=esk10_0), inference(spm,[status(thm)],[c_0_62, c_0_54])).
% 0.42/0.57  cnf(c_0_68, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.42/0.57  cnf(c_0_69, plain, (X1=k2_zfmisc_1(X2,k1_xboole_0)|r2_hidden(esk4_3(X2,k1_xboole_0,X1),X1)), inference(spm,[status(thm)],[c_0_64, c_0_49])).
% 0.42/0.57  cnf(c_0_70, plain, (~r2_hidden(X1,X2)|~r1_xboole_0(X2,k6_enumset1(X3,X3,X3,X4,X5,X6,X7,X1))), inference(spm,[status(thm)],[c_0_18, c_0_51])).
% 0.42/0.57  cnf(c_0_71, plain, (k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3))=k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.42/0.57  cnf(c_0_72, negated_conjecture, (k6_enumset1(esk10_0,esk10_0,esk10_0,esk10_0,esk10_0,esk10_0,esk10_0,esk10_0)=k1_xboole_0|~r1_tarski(k6_enumset1(esk10_0,esk10_0,esk10_0,esk10_0,esk10_0,esk10_0,esk10_0,esk10_0),k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0))), inference(spm,[status(thm)],[c_0_65, c_0_54])).
% 0.42/0.57  cnf(c_0_73, negated_conjecture, (esk9_0=esk8_0|esk10_0=esk8_0), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.42/0.57  cnf(c_0_74, plain, (r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68, c_0_42]), c_0_43]), c_0_44]), c_0_45]), c_0_46]), c_0_28]), c_0_29])).
% 0.42/0.57  cnf(c_0_75, plain, (X1=k2_zfmisc_1(X2,k1_xboole_0)|~r2_hidden(esk4_3(X2,k1_xboole_0,X1),X3)|~r1_xboole_0(X3,X1)), inference(spm,[status(thm)],[c_0_18, c_0_69])).
% 0.42/0.57  cnf(c_0_76, plain, (X1=k1_xboole_0|~r1_tarski(X1,k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.42/0.57  cnf(c_0_77, plain, (~r1_xboole_0(k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X7,X7,X7,X8,X9,X10,X11,X6))), inference(spm,[status(thm)],[c_0_70, c_0_51])).
% 0.42/0.57  cnf(c_0_78, plain, (k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))=k6_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71, c_0_42]), c_0_43]), c_0_43]), c_0_43]), c_0_44]), c_0_44]), c_0_44]), c_0_45]), c_0_45]), c_0_45]), c_0_46]), c_0_46]), c_0_46]), c_0_28]), c_0_28]), c_0_28]), c_0_29]), c_0_29]), c_0_29])).
% 0.42/0.57  cnf(c_0_79, negated_conjecture, (k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0)=k1_xboole_0|esk9_0=esk8_0|~r1_tarski(k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0),k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0))), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.42/0.57  cnf(c_0_80, plain, (r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X2,X2,X2,X3,X4,X5,X6,X1))), inference(spm,[status(thm)],[c_0_74, c_0_51])).
% 0.42/0.57  cnf(c_0_81, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0|~r2_hidden(esk4_3(X1,k1_xboole_0,k1_xboole_0),X2)), inference(spm,[status(thm)],[c_0_75, c_0_39])).
% 0.42/0.57  cnf(c_0_82, negated_conjecture, (k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,X1)=k1_xboole_0|~r1_tarski(k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,X1),k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,k4_tarski(X1,esk10_0)))), inference(spm,[status(thm)],[c_0_76, c_0_59])).
% 0.42/0.57  cnf(c_0_83, plain, (~r1_xboole_0(k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)),k6_enumset1(X4,X4,X4,X5,X6,X7,X8,k4_tarski(X1,X3)))), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 0.42/0.57  cnf(c_0_84, negated_conjecture, (k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0)=k1_xboole_0|esk9_0=esk8_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_79, c_0_80])])).
% 0.42/0.57  cnf(c_0_85, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_81, c_0_51])).
% 0.42/0.57  cnf(c_0_86, negated_conjecture, (k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0)=k1_xboole_0|~r1_tarski(k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0),k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0))), inference(spm,[status(thm)],[c_0_82, c_0_54])).
% 0.42/0.57  cnf(c_0_87, negated_conjecture, (esk9_0=esk8_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_85]), c_0_57])])).
% 0.42/0.57  cnf(c_0_88, negated_conjecture, (k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_86, c_0_87]), c_0_87]), c_0_87]), c_0_87]), c_0_87]), c_0_87]), c_0_87]), c_0_87]), c_0_87]), c_0_87]), c_0_87]), c_0_87]), c_0_87]), c_0_87]), c_0_87]), c_0_87]), c_0_80])])).
% 0.42/0.57  cnf(c_0_89, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_88]), c_0_85]), c_0_57])]), ['proof']).
% 0.42/0.57  # SZS output end CNFRefutation
% 0.42/0.57  # Proof object total steps             : 90
% 0.42/0.57  # Proof object clause steps            : 57
% 0.42/0.57  # Proof object formula steps           : 33
% 0.42/0.57  # Proof object conjectures             : 19
% 0.42/0.57  # Proof object clause conjectures      : 16
% 0.42/0.57  # Proof object formula conjectures     : 3
% 0.42/0.57  # Proof object initial clauses used    : 22
% 0.42/0.57  # Proof object initial formulas used   : 16
% 0.42/0.57  # Proof object generating inferences   : 26
% 0.42/0.57  # Proof object simplifying inferences  : 78
% 0.42/0.57  # Training examples: 0 positive, 0 negative
% 0.42/0.57  # Parsed axioms                        : 16
% 0.42/0.57  # Removed by relevancy pruning/SinE    : 0
% 0.42/0.57  # Initial clauses                      : 44
% 0.42/0.57  # Removed in clause preprocessing      : 7
% 0.42/0.57  # Initial clauses in saturation        : 37
% 0.42/0.57  # Processed clauses                    : 914
% 0.42/0.57  # ...of these trivial                  : 20
% 0.42/0.57  # ...subsumed                          : 357
% 0.42/0.57  # ...remaining for further processing  : 537
% 0.42/0.57  # Other redundant clauses eliminated   : 25
% 0.42/0.57  # Clauses deleted for lack of memory   : 0
% 0.42/0.57  # Backward-subsumed                    : 26
% 0.42/0.57  # Backward-rewritten                   : 127
% 0.42/0.57  # Generated clauses                    : 8920
% 0.42/0.57  # ...of the previous two non-trivial   : 8328
% 0.42/0.57  # Contextual simplify-reflections      : 1
% 0.42/0.57  # Paramodulations                      : 8902
% 0.42/0.57  # Factorizations                       : 0
% 0.42/0.57  # Equation resolutions                 : 25
% 0.42/0.57  # Propositional unsat checks           : 0
% 0.42/0.57  #    Propositional check models        : 0
% 0.42/0.57  #    Propositional check unsatisfiable : 0
% 0.42/0.57  #    Propositional clauses             : 0
% 0.42/0.57  #    Propositional clauses after purity: 0
% 0.42/0.57  #    Propositional unsat core size     : 0
% 0.42/0.57  #    Propositional preprocessing time  : 0.000
% 0.42/0.57  #    Propositional encoding time       : 0.000
% 0.42/0.57  #    Propositional solver time         : 0.000
% 0.42/0.57  #    Success case prop preproc time    : 0.000
% 0.42/0.57  #    Success case prop encoding time   : 0.000
% 0.42/0.57  #    Success case prop solver time     : 0.000
% 0.42/0.57  # Current number of processed clauses  : 335
% 0.42/0.57  #    Positive orientable unit clauses  : 27
% 0.42/0.57  #    Positive unorientable unit clauses: 0
% 0.42/0.57  #    Negative unit clauses             : 44
% 0.42/0.57  #    Non-unit-clauses                  : 264
% 0.42/0.57  # Current number of unprocessed clauses: 7307
% 0.42/0.57  # ...number of literals in the above   : 26716
% 0.42/0.57  # Current number of archived formulas  : 0
% 0.42/0.57  # Current number of archived clauses   : 197
% 0.42/0.57  # Clause-clause subsumption calls (NU) : 13366
% 0.42/0.57  # Rec. Clause-clause subsumption calls : 10701
% 0.42/0.57  # Non-unit clause-clause subsumptions  : 303
% 0.42/0.57  # Unit Clause-clause subsumption calls : 951
% 0.42/0.57  # Rewrite failures with RHS unbound    : 0
% 0.42/0.57  # BW rewrite match attempts            : 88
% 0.42/0.57  # BW rewrite match successes           : 14
% 0.42/0.57  # Condensation attempts                : 0
% 0.42/0.57  # Condensation successes               : 0
% 0.42/0.57  # Termbank termtop insertions          : 198288
% 0.42/0.57  
% 0.42/0.57  # -------------------------------------------------
% 0.42/0.57  # User time                : 0.219 s
% 0.42/0.57  # System time              : 0.008 s
% 0.42/0.57  # Total time               : 0.226 s
% 0.42/0.57  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
