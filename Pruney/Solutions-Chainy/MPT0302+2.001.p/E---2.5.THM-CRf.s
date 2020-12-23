%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:43:31 EST 2020

% Result     : Theorem 9.50s
% Output     : CNFRefutation 9.50s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 289 expanded)
%              Number of clauses        :   60 ( 124 expanded)
%              Number of leaves         :   23 (  78 expanded)
%              Depth                    :   13
%              Number of atoms          :  187 ( 571 expanded)
%              Number of equality atoms :   85 ( 305 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t114_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k2_zfmisc_1(X2,X1)
     => ( X1 = k1_xboole_0
        | X2 = k1_xboole_0
        | X1 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t114_zfmisc_1)).

fof(l54_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(commutativity_k5_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

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

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(l97_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

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

fof(c_0_23,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k2_zfmisc_1(X1,X2) = k2_zfmisc_1(X2,X1)
       => ( X1 = k1_xboole_0
          | X2 = k1_xboole_0
          | X1 = X2 ) ) ),
    inference(assume_negation,[status(cth)],[t114_zfmisc_1])).

fof(c_0_24,plain,(
    ! [X76,X77,X78,X79] :
      ( ( r2_hidden(X76,X78)
        | ~ r2_hidden(k4_tarski(X76,X77),k2_zfmisc_1(X78,X79)) )
      & ( r2_hidden(X77,X79)
        | ~ r2_hidden(k4_tarski(X76,X77),k2_zfmisc_1(X78,X79)) )
      & ( ~ r2_hidden(X76,X78)
        | ~ r2_hidden(X77,X79)
        | r2_hidden(k4_tarski(X76,X77),k2_zfmisc_1(X78,X79)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).

fof(c_0_25,plain,(
    ! [X30] :
      ( X30 = k1_xboole_0
      | r2_hidden(esk4_1(X30),X30) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

fof(c_0_26,negated_conjecture,
    ( k2_zfmisc_1(esk5_0,esk6_0) = k2_zfmisc_1(esk6_0,esk5_0)
    & esk5_0 != k1_xboole_0
    & esk6_0 != k1_xboole_0
    & esk5_0 != esk6_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).

cnf(c_0_27,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_28,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk4_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_29,plain,(
    ! [X12,X13,X14,X15,X16] :
      ( ( ~ r1_tarski(X12,X13)
        | ~ r2_hidden(X14,X12)
        | r2_hidden(X14,X13) )
      & ( r2_hidden(esk1_2(X15,X16),X15)
        | r1_tarski(X15,X16) )
      & ( ~ r2_hidden(esk1_2(X15,X16),X16)
        | r1_tarski(X15,X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( k2_zfmisc_1(esk5_0,esk6_0) = k2_zfmisc_1(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(k4_tarski(X2,esk4_1(X1)),k2_zfmisc_1(X3,X1))
    | ~ r2_hidden(X2,X3) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_34,plain,(
    ! [X74,X75] : k3_tarski(k2_tarski(X74,X75)) = k2_xboole_0(X74,X75) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_35,plain,(
    ! [X47,X48] : k1_enumset1(X47,X47,X48) = k2_tarski(X47,X48) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_36,plain,(
    ! [X38] : k5_xboole_0(X38,k1_xboole_0) = X38 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

fof(c_0_37,plain,(
    ! [X10,X11] : k5_xboole_0(X10,X11) = k5_xboole_0(X11,X10) ),
    inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).

fof(c_0_38,plain,(
    ! [X32,X33] :
      ( ( k4_xboole_0(X32,X33) != k1_xboole_0
        | r1_tarski(X32,X33) )
      & ( ~ r1_tarski(X32,X33)
        | k4_xboole_0(X32,X33) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_39,plain,(
    ! [X36,X37] : k4_xboole_0(X36,X37) = k5_xboole_0(X36,k3_xboole_0(X36,X37)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | ~ r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(esk6_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_41,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(k4_tarski(esk1_2(X2,X3),esk4_1(X1)),k2_zfmisc_1(X2,X1))
    | r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_42,negated_conjecture,
    ( esk5_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_43,plain,(
    ! [X39,X40] : r1_tarski(X39,k2_xboole_0(X39,X40)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_44,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_45,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_46,plain,(
    ! [X49,X50,X51] : k2_enumset1(X49,X49,X50,X51) = k1_enumset1(X49,X50,X51) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_47,plain,(
    ! [X52,X53,X54,X55] : k3_enumset1(X52,X52,X53,X54,X55) = k2_enumset1(X52,X53,X54,X55) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_48,plain,(
    ! [X56,X57,X58,X59,X60] : k4_enumset1(X56,X56,X57,X58,X59,X60) = k3_enumset1(X56,X57,X58,X59,X60) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_49,plain,(
    ! [X61,X62,X63,X64,X65,X66] : k5_enumset1(X61,X61,X62,X63,X64,X65,X66) = k4_enumset1(X61,X62,X63,X64,X65,X66) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_50,plain,(
    ! [X67,X68,X69,X70,X71,X72,X73] : k6_enumset1(X67,X67,X68,X69,X70,X71,X72,X73) = k5_enumset1(X67,X68,X69,X70,X71,X72,X73) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_51,plain,(
    ! [X45,X46] : k2_xboole_0(X45,X46) = k5_xboole_0(X45,k4_xboole_0(X46,X45)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_52,plain,(
    ! [X24,X25,X27,X28,X29] :
      ( ( r1_xboole_0(X24,X25)
        | r2_hidden(esk3_2(X24,X25),k3_xboole_0(X24,X25)) )
      & ( ~ r2_hidden(X29,k3_xboole_0(X27,X28))
        | ~ r1_xboole_0(X27,X28) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_53,plain,(
    ! [X34,X35] : r1_xboole_0(k3_xboole_0(X34,X35),k5_xboole_0(X34,X35)) ),
    inference(variable_rename,[status(thm)],[l97_xboole_1])).

fof(c_0_54,plain,(
    ! [X8,X9] : k3_xboole_0(X8,X9) = k3_xboole_0(X9,X8) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_55,plain,(
    ! [X41,X42,X43] : k5_xboole_0(k5_xboole_0(X41,X42),X43) = k5_xboole_0(X41,k5_xboole_0(X42,X43)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

fof(c_0_56,plain,(
    ! [X44] : k5_xboole_0(X44,X44) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

cnf(c_0_57,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_58,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_59,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_60,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_61,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(esk1_2(esk6_0,X1),esk5_0)
    | r1_tarski(esk6_0,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])).

cnf(c_0_63,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_64,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_65,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_66,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_67,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_68,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_69,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_70,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_71,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_72,plain,
    ( r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_73,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_74,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_75,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_76,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_77,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_78,negated_conjecture,
    ( r1_tarski(esk6_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_79,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_80,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_81,plain,
    ( r1_tarski(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_64]),c_0_65]),c_0_66]),c_0_67]),c_0_68]),c_0_69])).

cnf(c_0_82,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_64]),c_0_60]),c_0_65]),c_0_66]),c_0_67]),c_0_68]),c_0_69])).

cnf(c_0_83,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(k5_xboole_0(X2,X3),k3_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_73])).

cnf(c_0_84,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_76])).

cnf(c_0_85,negated_conjecture,
    ( k5_xboole_0(esk6_0,k3_xboole_0(esk6_0,esk5_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

fof(c_0_86,plain,(
    ! [X18,X19,X21,X22,X23] :
      ( ( r2_hidden(esk2_2(X18,X19),X18)
        | r1_xboole_0(X18,X19) )
      & ( r2_hidden(esk2_2(X18,X19),X19)
        | r1_xboole_0(X18,X19) )
      & ( ~ r2_hidden(X23,X21)
        | ~ r2_hidden(X23,X22)
        | ~ r1_xboole_0(X21,X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_87,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | ~ r2_hidden(k4_tarski(X2,X1),k2_zfmisc_1(esk6_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_79,c_0_31])).

cnf(c_0_88,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | r2_hidden(k4_tarski(esk4_1(X1),esk4_1(X2)),k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_28])).

cnf(c_0_89,negated_conjecture,
    ( esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_90,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk4_1(X1),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_80,c_0_28])).

cnf(c_0_91,plain,
    ( r1_tarski(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_92,plain,
    ( k3_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_83,c_0_28])).

cnf(c_0_93,negated_conjecture,
    ( k3_xboole_0(esk6_0,esk5_0) = esk6_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_57])).

cnf(c_0_94,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_86])).

cnf(c_0_95,negated_conjecture,
    ( r2_hidden(esk4_1(esk5_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_89]),c_0_42])).

cnf(c_0_96,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk4_1(X1),k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) ),
    inference(spm,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_97,negated_conjecture,
    ( k3_xboole_0(esk6_0,k5_xboole_0(esk6_0,esk5_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_73])).

cnf(c_0_98,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,X3))
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_94,c_0_72])).

cnf(c_0_99,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk4_1(esk5_0)),k2_zfmisc_1(X2,esk6_0))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_95])).

cnf(c_0_100,negated_conjecture,
    ( k5_xboole_0(esk6_0,esk5_0) = k1_xboole_0
    | r2_hidden(esk4_1(k5_xboole_0(esk6_0,esk5_0)),esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_57]),c_0_74]),c_0_58]),c_0_84])).

cnf(c_0_101,plain,
    ( k5_xboole_0(X1,X2) = k1_xboole_0
    | ~ r2_hidden(esk4_1(k5_xboole_0(X1,X2)),k3_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_98,c_0_28])).

cnf(c_0_102,negated_conjecture,
    ( k5_xboole_0(esk6_0,esk5_0) = k1_xboole_0
    | r2_hidden(k4_tarski(esk4_1(k5_xboole_0(esk6_0,esk5_0)),esk4_1(esk5_0)),k2_zfmisc_1(esk6_0,esk5_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_100]),c_0_31])).

cnf(c_0_103,negated_conjecture,
    ( k5_xboole_0(esk6_0,esk5_0) = k1_xboole_0
    | ~ r2_hidden(esk4_1(k5_xboole_0(esk6_0,esk5_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_101,c_0_93])).

cnf(c_0_104,negated_conjecture,
    ( k5_xboole_0(esk6_0,esk5_0) = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_102]),c_0_103])).

cnf(c_0_105,negated_conjecture,
    ( esk5_0 != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_106,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_104]),c_0_57]),c_0_105]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:01:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 9.50/9.71  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S054N
% 9.50/9.71  # and selection function GSelectMinInfpos.
% 9.50/9.71  #
% 9.50/9.71  # Preprocessing time       : 0.044 s
% 9.50/9.71  # Presaturation interreduction done
% 9.50/9.71  
% 9.50/9.71  # Proof found!
% 9.50/9.71  # SZS status Theorem
% 9.50/9.71  # SZS output start CNFRefutation
% 9.50/9.71  fof(t114_zfmisc_1, conjecture, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k2_zfmisc_1(X2,X1)=>(X1=k1_xboole_0|X2=k1_xboole_0|X1=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t114_zfmisc_1)).
% 9.50/9.71  fof(l54_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))<=>(r2_hidden(X1,X3)&r2_hidden(X2,X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 9.50/9.71  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 9.50/9.71  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 9.50/9.71  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 9.50/9.71  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 9.50/9.71  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 9.50/9.71  fof(commutativity_k5_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 9.50/9.71  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 9.50/9.71  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 9.50/9.71  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 9.50/9.71  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 9.50/9.71  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 9.50/9.71  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 9.50/9.71  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 9.50/9.71  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 9.50/9.71  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 9.50/9.71  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 9.50/9.71  fof(l97_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l97_xboole_1)).
% 9.50/9.71  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 9.50/9.71  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 9.50/9.71  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 9.50/9.71  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 9.50/9.71  fof(c_0_23, negated_conjecture, ~(![X1, X2]:(k2_zfmisc_1(X1,X2)=k2_zfmisc_1(X2,X1)=>(X1=k1_xboole_0|X2=k1_xboole_0|X1=X2))), inference(assume_negation,[status(cth)],[t114_zfmisc_1])).
% 9.50/9.71  fof(c_0_24, plain, ![X76, X77, X78, X79]:(((r2_hidden(X76,X78)|~r2_hidden(k4_tarski(X76,X77),k2_zfmisc_1(X78,X79)))&(r2_hidden(X77,X79)|~r2_hidden(k4_tarski(X76,X77),k2_zfmisc_1(X78,X79))))&(~r2_hidden(X76,X78)|~r2_hidden(X77,X79)|r2_hidden(k4_tarski(X76,X77),k2_zfmisc_1(X78,X79)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).
% 9.50/9.71  fof(c_0_25, plain, ![X30]:(X30=k1_xboole_0|r2_hidden(esk4_1(X30),X30)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 9.50/9.71  fof(c_0_26, negated_conjecture, (k2_zfmisc_1(esk5_0,esk6_0)=k2_zfmisc_1(esk6_0,esk5_0)&((esk5_0!=k1_xboole_0&esk6_0!=k1_xboole_0)&esk5_0!=esk6_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).
% 9.50/9.71  cnf(c_0_27, plain, (r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 9.50/9.71  cnf(c_0_28, plain, (X1=k1_xboole_0|r2_hidden(esk4_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 9.50/9.71  fof(c_0_29, plain, ![X12, X13, X14, X15, X16]:((~r1_tarski(X12,X13)|(~r2_hidden(X14,X12)|r2_hidden(X14,X13)))&((r2_hidden(esk1_2(X15,X16),X15)|r1_tarski(X15,X16))&(~r2_hidden(esk1_2(X15,X16),X16)|r1_tarski(X15,X16)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 9.50/9.71  cnf(c_0_30, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 9.50/9.71  cnf(c_0_31, negated_conjecture, (k2_zfmisc_1(esk5_0,esk6_0)=k2_zfmisc_1(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 9.50/9.71  cnf(c_0_32, plain, (X1=k1_xboole_0|r2_hidden(k4_tarski(X2,esk4_1(X1)),k2_zfmisc_1(X3,X1))|~r2_hidden(X2,X3)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 9.50/9.71  cnf(c_0_33, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 9.50/9.71  fof(c_0_34, plain, ![X74, X75]:k3_tarski(k2_tarski(X74,X75))=k2_xboole_0(X74,X75), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 9.50/9.71  fof(c_0_35, plain, ![X47, X48]:k1_enumset1(X47,X47,X48)=k2_tarski(X47,X48), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 9.50/9.71  fof(c_0_36, plain, ![X38]:k5_xboole_0(X38,k1_xboole_0)=X38, inference(variable_rename,[status(thm)],[t5_boole])).
% 9.50/9.71  fof(c_0_37, plain, ![X10, X11]:k5_xboole_0(X10,X11)=k5_xboole_0(X11,X10), inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).
% 9.50/9.71  fof(c_0_38, plain, ![X32, X33]:((k4_xboole_0(X32,X33)!=k1_xboole_0|r1_tarski(X32,X33))&(~r1_tarski(X32,X33)|k4_xboole_0(X32,X33)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 9.50/9.71  fof(c_0_39, plain, ![X36, X37]:k4_xboole_0(X36,X37)=k5_xboole_0(X36,k3_xboole_0(X36,X37)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 9.50/9.71  cnf(c_0_40, negated_conjecture, (r2_hidden(X1,esk5_0)|~r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(esk6_0,esk5_0))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 9.50/9.71  cnf(c_0_41, plain, (X1=k1_xboole_0|r2_hidden(k4_tarski(esk1_2(X2,X3),esk4_1(X1)),k2_zfmisc_1(X2,X1))|r1_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 9.50/9.71  cnf(c_0_42, negated_conjecture, (esk5_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_26])).
% 9.50/9.71  fof(c_0_43, plain, ![X39, X40]:r1_tarski(X39,k2_xboole_0(X39,X40)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 9.50/9.71  cnf(c_0_44, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 9.50/9.71  cnf(c_0_45, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 9.50/9.71  fof(c_0_46, plain, ![X49, X50, X51]:k2_enumset1(X49,X49,X50,X51)=k1_enumset1(X49,X50,X51), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 9.50/9.71  fof(c_0_47, plain, ![X52, X53, X54, X55]:k3_enumset1(X52,X52,X53,X54,X55)=k2_enumset1(X52,X53,X54,X55), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 9.50/9.71  fof(c_0_48, plain, ![X56, X57, X58, X59, X60]:k4_enumset1(X56,X56,X57,X58,X59,X60)=k3_enumset1(X56,X57,X58,X59,X60), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 9.50/9.71  fof(c_0_49, plain, ![X61, X62, X63, X64, X65, X66]:k5_enumset1(X61,X61,X62,X63,X64,X65,X66)=k4_enumset1(X61,X62,X63,X64,X65,X66), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 9.50/9.71  fof(c_0_50, plain, ![X67, X68, X69, X70, X71, X72, X73]:k6_enumset1(X67,X67,X68,X69,X70,X71,X72,X73)=k5_enumset1(X67,X68,X69,X70,X71,X72,X73), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 9.50/9.71  fof(c_0_51, plain, ![X45, X46]:k2_xboole_0(X45,X46)=k5_xboole_0(X45,k4_xboole_0(X46,X45)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 9.50/9.71  fof(c_0_52, plain, ![X24, X25, X27, X28, X29]:((r1_xboole_0(X24,X25)|r2_hidden(esk3_2(X24,X25),k3_xboole_0(X24,X25)))&(~r2_hidden(X29,k3_xboole_0(X27,X28))|~r1_xboole_0(X27,X28))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 9.50/9.71  fof(c_0_53, plain, ![X34, X35]:r1_xboole_0(k3_xboole_0(X34,X35),k5_xboole_0(X34,X35)), inference(variable_rename,[status(thm)],[l97_xboole_1])).
% 9.50/9.71  fof(c_0_54, plain, ![X8, X9]:k3_xboole_0(X8,X9)=k3_xboole_0(X9,X8), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 9.50/9.71  fof(c_0_55, plain, ![X41, X42, X43]:k5_xboole_0(k5_xboole_0(X41,X42),X43)=k5_xboole_0(X41,k5_xboole_0(X42,X43)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 9.50/9.71  fof(c_0_56, plain, ![X44]:k5_xboole_0(X44,X44)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 9.50/9.71  cnf(c_0_57, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_36])).
% 9.50/9.71  cnf(c_0_58, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 9.50/9.71  cnf(c_0_59, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 9.50/9.71  cnf(c_0_60, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 9.50/9.71  cnf(c_0_61, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 9.50/9.71  cnf(c_0_62, negated_conjecture, (r2_hidden(esk1_2(esk6_0,X1),esk5_0)|r1_tarski(esk6_0,X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42])).
% 9.50/9.71  cnf(c_0_63, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 9.50/9.71  cnf(c_0_64, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_44, c_0_45])).
% 9.50/9.71  cnf(c_0_65, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 9.50/9.71  cnf(c_0_66, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 9.50/9.71  cnf(c_0_67, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 9.50/9.71  cnf(c_0_68, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 9.50/9.71  cnf(c_0_69, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 9.50/9.71  cnf(c_0_70, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 9.50/9.71  cnf(c_0_71, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 9.50/9.71  cnf(c_0_72, plain, (r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 9.50/9.71  cnf(c_0_73, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 9.50/9.71  cnf(c_0_74, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 9.50/9.71  cnf(c_0_75, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_56])).
% 9.50/9.71  cnf(c_0_76, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 9.50/9.71  cnf(c_0_77, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=k1_xboole_0|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_59, c_0_60])).
% 9.50/9.71  cnf(c_0_78, negated_conjecture, (r1_tarski(esk6_0,esk5_0)), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 9.50/9.71  cnf(c_0_79, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 9.50/9.71  cnf(c_0_80, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 9.50/9.71  cnf(c_0_81, plain, (r1_tarski(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_64]), c_0_65]), c_0_66]), c_0_67]), c_0_68]), c_0_69])).
% 9.50/9.71  cnf(c_0_82, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_64]), c_0_60]), c_0_65]), c_0_66]), c_0_67]), c_0_68]), c_0_69])).
% 9.50/9.71  cnf(c_0_83, plain, (~r2_hidden(X1,k3_xboole_0(k5_xboole_0(X2,X3),k3_xboole_0(X2,X3)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_73])).
% 9.50/9.71  cnf(c_0_84, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_76])).
% 9.50/9.71  cnf(c_0_85, negated_conjecture, (k5_xboole_0(esk6_0,k3_xboole_0(esk6_0,esk5_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 9.50/9.71  fof(c_0_86, plain, ![X18, X19, X21, X22, X23]:(((r2_hidden(esk2_2(X18,X19),X18)|r1_xboole_0(X18,X19))&(r2_hidden(esk2_2(X18,X19),X19)|r1_xboole_0(X18,X19)))&(~r2_hidden(X23,X21)|~r2_hidden(X23,X22)|~r1_xboole_0(X21,X22))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 9.50/9.71  cnf(c_0_87, negated_conjecture, (r2_hidden(X1,esk6_0)|~r2_hidden(k4_tarski(X2,X1),k2_zfmisc_1(esk6_0,esk5_0))), inference(spm,[status(thm)],[c_0_79, c_0_31])).
% 9.50/9.71  cnf(c_0_88, plain, (X1=k1_xboole_0|X2=k1_xboole_0|r2_hidden(k4_tarski(esk4_1(X1),esk4_1(X2)),k2_zfmisc_1(X1,X2))), inference(spm,[status(thm)],[c_0_32, c_0_28])).
% 9.50/9.71  cnf(c_0_89, negated_conjecture, (esk6_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_26])).
% 9.50/9.71  cnf(c_0_90, plain, (X1=k1_xboole_0|r2_hidden(esk4_1(X1),X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_80, c_0_28])).
% 9.50/9.71  cnf(c_0_91, plain, (r1_tarski(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 9.50/9.71  cnf(c_0_92, plain, (k3_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))=k1_xboole_0), inference(spm,[status(thm)],[c_0_83, c_0_28])).
% 9.50/9.71  cnf(c_0_93, negated_conjecture, (k3_xboole_0(esk6_0,esk5_0)=esk6_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_57])).
% 9.50/9.71  cnf(c_0_94, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_86])).
% 9.50/9.71  cnf(c_0_95, negated_conjecture, (r2_hidden(esk4_1(esk5_0),esk6_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_89]), c_0_42])).
% 9.50/9.71  cnf(c_0_96, plain, (X1=k1_xboole_0|r2_hidden(esk4_1(X1),k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))), inference(spm,[status(thm)],[c_0_90, c_0_91])).
% 9.50/9.71  cnf(c_0_97, negated_conjecture, (k3_xboole_0(esk6_0,k5_xboole_0(esk6_0,esk5_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_73])).
% 9.50/9.71  cnf(c_0_98, plain, (~r2_hidden(X1,k5_xboole_0(X2,X3))|~r2_hidden(X1,k3_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_94, c_0_72])).
% 9.50/9.71  cnf(c_0_99, negated_conjecture, (r2_hidden(k4_tarski(X1,esk4_1(esk5_0)),k2_zfmisc_1(X2,esk6_0))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_27, c_0_95])).
% 9.50/9.71  cnf(c_0_100, negated_conjecture, (k5_xboole_0(esk6_0,esk5_0)=k1_xboole_0|r2_hidden(esk4_1(k5_xboole_0(esk6_0,esk5_0)),esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_97]), c_0_57]), c_0_74]), c_0_58]), c_0_84])).
% 9.50/9.71  cnf(c_0_101, plain, (k5_xboole_0(X1,X2)=k1_xboole_0|~r2_hidden(esk4_1(k5_xboole_0(X1,X2)),k3_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_98, c_0_28])).
% 9.50/9.71  cnf(c_0_102, negated_conjecture, (k5_xboole_0(esk6_0,esk5_0)=k1_xboole_0|r2_hidden(k4_tarski(esk4_1(k5_xboole_0(esk6_0,esk5_0)),esk4_1(esk5_0)),k2_zfmisc_1(esk6_0,esk5_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_100]), c_0_31])).
% 9.50/9.71  cnf(c_0_103, negated_conjecture, (k5_xboole_0(esk6_0,esk5_0)=k1_xboole_0|~r2_hidden(esk4_1(k5_xboole_0(esk6_0,esk5_0)),esk6_0)), inference(spm,[status(thm)],[c_0_101, c_0_93])).
% 9.50/9.71  cnf(c_0_104, negated_conjecture, (k5_xboole_0(esk6_0,esk5_0)=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_102]), c_0_103])).
% 9.50/9.71  cnf(c_0_105, negated_conjecture, (esk5_0!=esk6_0), inference(split_conjunct,[status(thm)],[c_0_26])).
% 9.50/9.71  cnf(c_0_106, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_104]), c_0_57]), c_0_105]), ['proof']).
% 9.50/9.71  # SZS output end CNFRefutation
% 9.50/9.71  # Proof object total steps             : 107
% 9.50/9.71  # Proof object clause steps            : 60
% 9.50/9.71  # Proof object formula steps           : 47
% 9.50/9.71  # Proof object conjectures             : 21
% 9.50/9.71  # Proof object clause conjectures      : 18
% 9.50/9.71  # Proof object formula conjectures     : 3
% 9.50/9.71  # Proof object initial clauses used    : 30
% 9.50/9.71  # Proof object initial formulas used   : 23
% 9.50/9.71  # Proof object generating inferences   : 26
% 9.50/9.71  # Proof object simplifying inferences  : 30
% 9.50/9.71  # Training examples: 0 positive, 0 negative
% 9.50/9.71  # Parsed axioms                        : 23
% 9.50/9.71  # Removed by relevancy pruning/SinE    : 0
% 9.50/9.71  # Initial clauses                      : 34
% 9.50/9.71  # Removed in clause preprocessing      : 8
% 9.50/9.71  # Initial clauses in saturation        : 26
% 9.50/9.71  # Processed clauses                    : 14258
% 9.50/9.71  # ...of these trivial                  : 460
% 9.50/9.71  # ...subsumed                          : 12136
% 9.50/9.71  # ...remaining for further processing  : 1662
% 9.50/9.71  # Other redundant clauses eliminated   : 1068
% 9.50/9.71  # Clauses deleted for lack of memory   : 0
% 9.50/9.71  # Backward-subsumed                    : 2
% 9.50/9.71  # Backward-rewritten                   : 187
% 9.50/9.71  # Generated clauses                    : 389807
% 9.50/9.71  # ...of the previous two non-trivial   : 368077
% 9.50/9.71  # Contextual simplify-reflections      : 1
% 9.50/9.71  # Paramodulations                      : 388739
% 9.50/9.71  # Factorizations                       : 0
% 9.50/9.71  # Equation resolutions                 : 1068
% 9.50/9.71  # Propositional unsat checks           : 0
% 9.50/9.71  #    Propositional check models        : 0
% 9.50/9.71  #    Propositional check unsatisfiable : 0
% 9.50/9.71  #    Propositional clauses             : 0
% 9.50/9.71  #    Propositional clauses after purity: 0
% 9.50/9.71  #    Propositional unsat core size     : 0
% 9.50/9.71  #    Propositional preprocessing time  : 0.000
% 9.50/9.71  #    Propositional encoding time       : 0.000
% 9.50/9.71  #    Propositional solver time         : 0.000
% 9.50/9.71  #    Success case prop preproc time    : 0.000
% 9.50/9.71  #    Success case prop encoding time   : 0.000
% 9.50/9.71  #    Success case prop solver time     : 0.000
% 9.50/9.71  # Current number of processed clauses  : 1444
% 9.50/9.71  #    Positive orientable unit clauses  : 350
% 9.50/9.71  #    Positive unorientable unit clauses: 95
% 9.50/9.71  #    Negative unit clauses             : 179
% 9.50/9.71  #    Non-unit-clauses                  : 820
% 9.50/9.71  # Current number of unprocessed clauses: 352777
% 9.50/9.71  # ...number of literals in the above   : 547529
% 9.50/9.71  # Current number of archived formulas  : 0
% 9.50/9.71  # Current number of archived clauses   : 223
% 9.50/9.71  # Clause-clause subsumption calls (NU) : 94210
% 9.50/9.71  # Rec. Clause-clause subsumption calls : 91014
% 9.50/9.71  # Non-unit clause-clause subsumptions  : 4354
% 9.50/9.71  # Unit Clause-clause subsumption calls : 7029
% 9.50/9.71  # Rewrite failures with RHS unbound    : 25083
% 9.50/9.71  # BW rewrite match attempts            : 13531
% 9.50/9.71  # BW rewrite match successes           : 893
% 9.50/9.71  # Condensation attempts                : 0
% 9.50/9.71  # Condensation successes               : 0
% 9.50/9.71  # Termbank termtop insertions          : 10248799
% 9.50/9.74  
% 9.50/9.74  # -------------------------------------------------
% 9.50/9.74  # User time                : 9.148 s
% 9.50/9.74  # System time              : 0.244 s
% 9.50/9.74  # Total time               : 9.392 s
% 9.50/9.74  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
