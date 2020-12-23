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
% DateTime   : Thu Dec  3 10:56:04 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   46 (  86 expanded)
%              Number of clauses        :   21 (  35 expanded)
%              Number of leaves         :   12 (  25 expanded)
%              Depth                    :    7
%              Number of atoms          :  152 ( 192 expanded)
%              Number of equality atoms :  100 ( 140 expanded)
%              Maximal formula depth    :   47 (   5 average)
%              Maximal clause size      :   68 (   1 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t93_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_enumset1)).

fof(t10_ordinal1,conjecture,(
    ! [X1] : r2_hidden(X1,k1_ordinal1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).

fof(d1_ordinal1,axiom,(
    ! [X1] : k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(c_0_12,plain,(
    ! [X48,X49] : k3_tarski(k2_tarski(X48,X49)) = k2_xboole_0(X48,X49) ),
    inference(variable_rename,[status(thm)],[t93_zfmisc_1])).

fof(c_0_13,plain,(
    ! [X21,X22] : k1_enumset1(X21,X21,X22) = k2_tarski(X21,X22) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_14,plain,(
    ! [X11,X12,X13,X14,X15,X16,X17,X18] :
      ( ( ~ r2_hidden(X14,X13)
        | r2_hidden(X14,X11)
        | r2_hidden(X14,X12)
        | X13 != k2_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X15,X11)
        | r2_hidden(X15,X13)
        | X13 != k2_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X15,X12)
        | r2_hidden(X15,X13)
        | X13 != k2_xboole_0(X11,X12) )
      & ( ~ r2_hidden(esk1_3(X16,X17,X18),X16)
        | ~ r2_hidden(esk1_3(X16,X17,X18),X18)
        | X18 = k2_xboole_0(X16,X17) )
      & ( ~ r2_hidden(esk1_3(X16,X17,X18),X17)
        | ~ r2_hidden(esk1_3(X16,X17,X18),X18)
        | X18 = k2_xboole_0(X16,X17) )
      & ( r2_hidden(esk1_3(X16,X17,X18),X18)
        | r2_hidden(esk1_3(X16,X17,X18),X16)
        | r2_hidden(esk1_3(X16,X17,X18),X17)
        | X18 = k2_xboole_0(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

cnf(c_0_15,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_17,plain,(
    ! [X23,X24,X25] : k2_enumset1(X23,X23,X24,X25) = k1_enumset1(X23,X24,X25) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_18,plain,(
    ! [X26,X27,X28,X29] : k3_enumset1(X26,X26,X27,X28,X29) = k2_enumset1(X26,X27,X28,X29) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_19,plain,(
    ! [X30,X31,X32,X33,X34] : k4_enumset1(X30,X30,X31,X32,X33,X34) = k3_enumset1(X30,X31,X32,X33,X34) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_20,plain,(
    ! [X35,X36,X37,X38,X39,X40] : k5_enumset1(X35,X35,X36,X37,X38,X39,X40) = k4_enumset1(X35,X36,X37,X38,X39,X40) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_21,plain,(
    ! [X41,X42,X43,X44,X45,X46,X47] : k6_enumset1(X41,X41,X42,X43,X44,X45,X46,X47) = k5_enumset1(X41,X42,X43,X44,X45,X46,X47) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_22,plain,(
    ! [X50,X51,X52,X53,X54,X55,X56,X57,X58,X59,X60,X61,X62,X63,X64,X65,X66,X67,X68,X69] :
      ( ( ~ r2_hidden(X59,X58)
        | X59 = X50
        | X59 = X51
        | X59 = X52
        | X59 = X53
        | X59 = X54
        | X59 = X55
        | X59 = X56
        | X59 = X57
        | X58 != k6_enumset1(X50,X51,X52,X53,X54,X55,X56,X57) )
      & ( X60 != X50
        | r2_hidden(X60,X58)
        | X58 != k6_enumset1(X50,X51,X52,X53,X54,X55,X56,X57) )
      & ( X60 != X51
        | r2_hidden(X60,X58)
        | X58 != k6_enumset1(X50,X51,X52,X53,X54,X55,X56,X57) )
      & ( X60 != X52
        | r2_hidden(X60,X58)
        | X58 != k6_enumset1(X50,X51,X52,X53,X54,X55,X56,X57) )
      & ( X60 != X53
        | r2_hidden(X60,X58)
        | X58 != k6_enumset1(X50,X51,X52,X53,X54,X55,X56,X57) )
      & ( X60 != X54
        | r2_hidden(X60,X58)
        | X58 != k6_enumset1(X50,X51,X52,X53,X54,X55,X56,X57) )
      & ( X60 != X55
        | r2_hidden(X60,X58)
        | X58 != k6_enumset1(X50,X51,X52,X53,X54,X55,X56,X57) )
      & ( X60 != X56
        | r2_hidden(X60,X58)
        | X58 != k6_enumset1(X50,X51,X52,X53,X54,X55,X56,X57) )
      & ( X60 != X57
        | r2_hidden(X60,X58)
        | X58 != k6_enumset1(X50,X51,X52,X53,X54,X55,X56,X57) )
      & ( esk2_9(X61,X62,X63,X64,X65,X66,X67,X68,X69) != X61
        | ~ r2_hidden(esk2_9(X61,X62,X63,X64,X65,X66,X67,X68,X69),X69)
        | X69 = k6_enumset1(X61,X62,X63,X64,X65,X66,X67,X68) )
      & ( esk2_9(X61,X62,X63,X64,X65,X66,X67,X68,X69) != X62
        | ~ r2_hidden(esk2_9(X61,X62,X63,X64,X65,X66,X67,X68,X69),X69)
        | X69 = k6_enumset1(X61,X62,X63,X64,X65,X66,X67,X68) )
      & ( esk2_9(X61,X62,X63,X64,X65,X66,X67,X68,X69) != X63
        | ~ r2_hidden(esk2_9(X61,X62,X63,X64,X65,X66,X67,X68,X69),X69)
        | X69 = k6_enumset1(X61,X62,X63,X64,X65,X66,X67,X68) )
      & ( esk2_9(X61,X62,X63,X64,X65,X66,X67,X68,X69) != X64
        | ~ r2_hidden(esk2_9(X61,X62,X63,X64,X65,X66,X67,X68,X69),X69)
        | X69 = k6_enumset1(X61,X62,X63,X64,X65,X66,X67,X68) )
      & ( esk2_9(X61,X62,X63,X64,X65,X66,X67,X68,X69) != X65
        | ~ r2_hidden(esk2_9(X61,X62,X63,X64,X65,X66,X67,X68,X69),X69)
        | X69 = k6_enumset1(X61,X62,X63,X64,X65,X66,X67,X68) )
      & ( esk2_9(X61,X62,X63,X64,X65,X66,X67,X68,X69) != X66
        | ~ r2_hidden(esk2_9(X61,X62,X63,X64,X65,X66,X67,X68,X69),X69)
        | X69 = k6_enumset1(X61,X62,X63,X64,X65,X66,X67,X68) )
      & ( esk2_9(X61,X62,X63,X64,X65,X66,X67,X68,X69) != X67
        | ~ r2_hidden(esk2_9(X61,X62,X63,X64,X65,X66,X67,X68,X69),X69)
        | X69 = k6_enumset1(X61,X62,X63,X64,X65,X66,X67,X68) )
      & ( esk2_9(X61,X62,X63,X64,X65,X66,X67,X68,X69) != X68
        | ~ r2_hidden(esk2_9(X61,X62,X63,X64,X65,X66,X67,X68,X69),X69)
        | X69 = k6_enumset1(X61,X62,X63,X64,X65,X66,X67,X68) )
      & ( r2_hidden(esk2_9(X61,X62,X63,X64,X65,X66,X67,X68,X69),X69)
        | esk2_9(X61,X62,X63,X64,X65,X66,X67,X68,X69) = X61
        | esk2_9(X61,X62,X63,X64,X65,X66,X67,X68,X69) = X62
        | esk2_9(X61,X62,X63,X64,X65,X66,X67,X68,X69) = X63
        | esk2_9(X61,X62,X63,X64,X65,X66,X67,X68,X69) = X64
        | esk2_9(X61,X62,X63,X64,X65,X66,X67,X68,X69) = X65
        | esk2_9(X61,X62,X63,X64,X65,X66,X67,X68,X69) = X66
        | esk2_9(X61,X62,X63,X64,X65,X66,X67,X68,X69) = X67
        | esk2_9(X61,X62,X63,X64,X65,X66,X67,X68,X69) = X68
        | X69 = k6_enumset1(X61,X62,X63,X64,X65,X66,X67,X68) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_enumset1])])])])])])).

fof(c_0_23,negated_conjecture,(
    ~ ! [X1] : r2_hidden(X1,k1_ordinal1(X1)) ),
    inference(assume_negation,[status(cth)],[t10_ordinal1])).

fof(c_0_24,plain,(
    ! [X71] : k1_ordinal1(X71) = k2_xboole_0(X71,k1_tarski(X71)) ),
    inference(variable_rename,[status(thm)],[d1_ordinal1])).

fof(c_0_25,plain,(
    ! [X20] : k2_tarski(X20,X20) = k1_tarski(X20) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_27,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_28,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_29,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_30,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_31,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_32,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k6_enumset1(X4,X5,X6,X7,X8,X9,X10,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_34,negated_conjecture,(
    ~ r2_hidden(esk3_0,k1_ordinal1(esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).

cnf(c_0_35,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_36,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,X3)
    | X3 != k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X2))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29]),c_0_30]),c_0_31]),c_0_32])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,X2)
    | X2 != k6_enumset1(X3,X4,X5,X6,X7,X8,X9,X1) ),
    inference(er,[status(thm)],[c_0_33])).

cnf(c_0_39,negated_conjecture,
    ( ~ r2_hidden(esk3_0,k1_ordinal1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_40,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k2_tarski(X1,X1)) ),
    inference(rw,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_37])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X1)) ),
    inference(er,[status(thm)],[c_0_38])).

cnf(c_0_43,negated_conjecture,
    ( ~ r2_hidden(esk3_0,k3_tarski(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_40]),c_0_16]),c_0_27]),c_0_28]),c_0_28]),c_0_29]),c_0_29]),c_0_30]),c_0_30]),c_0_31]),c_0_31]),c_0_32]),c_0_32])).

cnf(c_0_44,plain,
    ( r2_hidden(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k6_enumset1(X3,X4,X5,X6,X7,X8,X9,X1)))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_45,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_44])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:48:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.46  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_S0a
% 0.20/0.46  # and selection function SelectNegativeLiterals.
% 0.20/0.46  #
% 0.20/0.46  # Preprocessing time       : 0.028 s
% 0.20/0.46  
% 0.20/0.46  # Proof found!
% 0.20/0.46  # SZS status Theorem
% 0.20/0.46  # SZS output start CNFRefutation
% 0.20/0.46  fof(t93_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t93_zfmisc_1)).
% 0.20/0.46  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.46  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 0.20/0.46  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.20/0.46  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.20/0.46  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.20/0.46  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.20/0.46  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 0.20/0.46  fof(d6_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:(X9=k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)<=>![X10]:(r2_hidden(X10,X9)<=>~((((((((X10!=X1&X10!=X2)&X10!=X3)&X10!=X4)&X10!=X5)&X10!=X6)&X10!=X7)&X10!=X8)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_enumset1)).
% 0.20/0.46  fof(t10_ordinal1, conjecture, ![X1]:r2_hidden(X1,k1_ordinal1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_ordinal1)).
% 0.20/0.46  fof(d1_ordinal1, axiom, ![X1]:k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_ordinal1)).
% 0.20/0.46  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.20/0.46  fof(c_0_12, plain, ![X48, X49]:k3_tarski(k2_tarski(X48,X49))=k2_xboole_0(X48,X49), inference(variable_rename,[status(thm)],[t93_zfmisc_1])).
% 0.20/0.46  fof(c_0_13, plain, ![X21, X22]:k1_enumset1(X21,X21,X22)=k2_tarski(X21,X22), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.46  fof(c_0_14, plain, ![X11, X12, X13, X14, X15, X16, X17, X18]:(((~r2_hidden(X14,X13)|(r2_hidden(X14,X11)|r2_hidden(X14,X12))|X13!=k2_xboole_0(X11,X12))&((~r2_hidden(X15,X11)|r2_hidden(X15,X13)|X13!=k2_xboole_0(X11,X12))&(~r2_hidden(X15,X12)|r2_hidden(X15,X13)|X13!=k2_xboole_0(X11,X12))))&(((~r2_hidden(esk1_3(X16,X17,X18),X16)|~r2_hidden(esk1_3(X16,X17,X18),X18)|X18=k2_xboole_0(X16,X17))&(~r2_hidden(esk1_3(X16,X17,X18),X17)|~r2_hidden(esk1_3(X16,X17,X18),X18)|X18=k2_xboole_0(X16,X17)))&(r2_hidden(esk1_3(X16,X17,X18),X18)|(r2_hidden(esk1_3(X16,X17,X18),X16)|r2_hidden(esk1_3(X16,X17,X18),X17))|X18=k2_xboole_0(X16,X17)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 0.20/0.46  cnf(c_0_15, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.46  cnf(c_0_16, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.46  fof(c_0_17, plain, ![X23, X24, X25]:k2_enumset1(X23,X23,X24,X25)=k1_enumset1(X23,X24,X25), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.20/0.46  fof(c_0_18, plain, ![X26, X27, X28, X29]:k3_enumset1(X26,X26,X27,X28,X29)=k2_enumset1(X26,X27,X28,X29), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.20/0.46  fof(c_0_19, plain, ![X30, X31, X32, X33, X34]:k4_enumset1(X30,X30,X31,X32,X33,X34)=k3_enumset1(X30,X31,X32,X33,X34), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.20/0.46  fof(c_0_20, plain, ![X35, X36, X37, X38, X39, X40]:k5_enumset1(X35,X35,X36,X37,X38,X39,X40)=k4_enumset1(X35,X36,X37,X38,X39,X40), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.20/0.46  fof(c_0_21, plain, ![X41, X42, X43, X44, X45, X46, X47]:k6_enumset1(X41,X41,X42,X43,X44,X45,X46,X47)=k5_enumset1(X41,X42,X43,X44,X45,X46,X47), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.20/0.46  fof(c_0_22, plain, ![X50, X51, X52, X53, X54, X55, X56, X57, X58, X59, X60, X61, X62, X63, X64, X65, X66, X67, X68, X69]:(((~r2_hidden(X59,X58)|(X59=X50|X59=X51|X59=X52|X59=X53|X59=X54|X59=X55|X59=X56|X59=X57)|X58!=k6_enumset1(X50,X51,X52,X53,X54,X55,X56,X57))&((((((((X60!=X50|r2_hidden(X60,X58)|X58!=k6_enumset1(X50,X51,X52,X53,X54,X55,X56,X57))&(X60!=X51|r2_hidden(X60,X58)|X58!=k6_enumset1(X50,X51,X52,X53,X54,X55,X56,X57)))&(X60!=X52|r2_hidden(X60,X58)|X58!=k6_enumset1(X50,X51,X52,X53,X54,X55,X56,X57)))&(X60!=X53|r2_hidden(X60,X58)|X58!=k6_enumset1(X50,X51,X52,X53,X54,X55,X56,X57)))&(X60!=X54|r2_hidden(X60,X58)|X58!=k6_enumset1(X50,X51,X52,X53,X54,X55,X56,X57)))&(X60!=X55|r2_hidden(X60,X58)|X58!=k6_enumset1(X50,X51,X52,X53,X54,X55,X56,X57)))&(X60!=X56|r2_hidden(X60,X58)|X58!=k6_enumset1(X50,X51,X52,X53,X54,X55,X56,X57)))&(X60!=X57|r2_hidden(X60,X58)|X58!=k6_enumset1(X50,X51,X52,X53,X54,X55,X56,X57))))&(((((((((esk2_9(X61,X62,X63,X64,X65,X66,X67,X68,X69)!=X61|~r2_hidden(esk2_9(X61,X62,X63,X64,X65,X66,X67,X68,X69),X69)|X69=k6_enumset1(X61,X62,X63,X64,X65,X66,X67,X68))&(esk2_9(X61,X62,X63,X64,X65,X66,X67,X68,X69)!=X62|~r2_hidden(esk2_9(X61,X62,X63,X64,X65,X66,X67,X68,X69),X69)|X69=k6_enumset1(X61,X62,X63,X64,X65,X66,X67,X68)))&(esk2_9(X61,X62,X63,X64,X65,X66,X67,X68,X69)!=X63|~r2_hidden(esk2_9(X61,X62,X63,X64,X65,X66,X67,X68,X69),X69)|X69=k6_enumset1(X61,X62,X63,X64,X65,X66,X67,X68)))&(esk2_9(X61,X62,X63,X64,X65,X66,X67,X68,X69)!=X64|~r2_hidden(esk2_9(X61,X62,X63,X64,X65,X66,X67,X68,X69),X69)|X69=k6_enumset1(X61,X62,X63,X64,X65,X66,X67,X68)))&(esk2_9(X61,X62,X63,X64,X65,X66,X67,X68,X69)!=X65|~r2_hidden(esk2_9(X61,X62,X63,X64,X65,X66,X67,X68,X69),X69)|X69=k6_enumset1(X61,X62,X63,X64,X65,X66,X67,X68)))&(esk2_9(X61,X62,X63,X64,X65,X66,X67,X68,X69)!=X66|~r2_hidden(esk2_9(X61,X62,X63,X64,X65,X66,X67,X68,X69),X69)|X69=k6_enumset1(X61,X62,X63,X64,X65,X66,X67,X68)))&(esk2_9(X61,X62,X63,X64,X65,X66,X67,X68,X69)!=X67|~r2_hidden(esk2_9(X61,X62,X63,X64,X65,X66,X67,X68,X69),X69)|X69=k6_enumset1(X61,X62,X63,X64,X65,X66,X67,X68)))&(esk2_9(X61,X62,X63,X64,X65,X66,X67,X68,X69)!=X68|~r2_hidden(esk2_9(X61,X62,X63,X64,X65,X66,X67,X68,X69),X69)|X69=k6_enumset1(X61,X62,X63,X64,X65,X66,X67,X68)))&(r2_hidden(esk2_9(X61,X62,X63,X64,X65,X66,X67,X68,X69),X69)|(esk2_9(X61,X62,X63,X64,X65,X66,X67,X68,X69)=X61|esk2_9(X61,X62,X63,X64,X65,X66,X67,X68,X69)=X62|esk2_9(X61,X62,X63,X64,X65,X66,X67,X68,X69)=X63|esk2_9(X61,X62,X63,X64,X65,X66,X67,X68,X69)=X64|esk2_9(X61,X62,X63,X64,X65,X66,X67,X68,X69)=X65|esk2_9(X61,X62,X63,X64,X65,X66,X67,X68,X69)=X66|esk2_9(X61,X62,X63,X64,X65,X66,X67,X68,X69)=X67|esk2_9(X61,X62,X63,X64,X65,X66,X67,X68,X69)=X68)|X69=k6_enumset1(X61,X62,X63,X64,X65,X66,X67,X68)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_enumset1])])])])])])).
% 0.20/0.46  fof(c_0_23, negated_conjecture, ~(![X1]:r2_hidden(X1,k1_ordinal1(X1))), inference(assume_negation,[status(cth)],[t10_ordinal1])).
% 0.20/0.46  fof(c_0_24, plain, ![X71]:k1_ordinal1(X71)=k2_xboole_0(X71,k1_tarski(X71)), inference(variable_rename,[status(thm)],[d1_ordinal1])).
% 0.20/0.46  fof(c_0_25, plain, ![X20]:k2_tarski(X20,X20)=k1_tarski(X20), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.20/0.46  cnf(c_0_26, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.46  cnf(c_0_27, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_15, c_0_16])).
% 0.20/0.46  cnf(c_0_28, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.46  cnf(c_0_29, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.46  cnf(c_0_30, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.46  cnf(c_0_31, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.46  cnf(c_0_32, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.46  cnf(c_0_33, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k6_enumset1(X4,X5,X6,X7,X8,X9,X10,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.46  fof(c_0_34, negated_conjecture, ~r2_hidden(esk3_0,k1_ordinal1(esk3_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).
% 0.20/0.46  cnf(c_0_35, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.46  cnf(c_0_36, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.46  cnf(c_0_37, plain, (r2_hidden(X1,X3)|X3!=k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X2))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_29]), c_0_30]), c_0_31]), c_0_32])).
% 0.20/0.46  cnf(c_0_38, plain, (r2_hidden(X1,X2)|X2!=k6_enumset1(X3,X4,X5,X6,X7,X8,X9,X1)), inference(er,[status(thm)],[c_0_33])).
% 0.20/0.46  cnf(c_0_39, negated_conjecture, (~r2_hidden(esk3_0,k1_ordinal1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.46  cnf(c_0_40, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k2_tarski(X1,X1))), inference(rw,[status(thm)],[c_0_35, c_0_36])).
% 0.20/0.46  cnf(c_0_41, plain, (r2_hidden(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_37])).
% 0.20/0.46  cnf(c_0_42, plain, (r2_hidden(X1,k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X1))), inference(er,[status(thm)],[c_0_38])).
% 0.20/0.46  cnf(c_0_43, negated_conjecture, (~r2_hidden(esk3_0,k3_tarski(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_40]), c_0_16]), c_0_27]), c_0_28]), c_0_28]), c_0_29]), c_0_29]), c_0_30]), c_0_30]), c_0_31]), c_0_31]), c_0_32]), c_0_32])).
% 0.20/0.46  cnf(c_0_44, plain, (r2_hidden(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k6_enumset1(X3,X4,X5,X6,X7,X8,X9,X1))))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.20/0.46  cnf(c_0_45, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_44])]), ['proof']).
% 0.20/0.46  # SZS output end CNFRefutation
% 0.20/0.46  # Proof object total steps             : 46
% 0.20/0.46  # Proof object clause steps            : 21
% 0.20/0.46  # Proof object formula steps           : 25
% 0.20/0.46  # Proof object conjectures             : 6
% 0.20/0.46  # Proof object clause conjectures      : 3
% 0.20/0.46  # Proof object formula conjectures     : 3
% 0.20/0.46  # Proof object initial clauses used    : 12
% 0.20/0.46  # Proof object initial formulas used   : 12
% 0.20/0.46  # Proof object generating inferences   : 3
% 0.20/0.46  # Proof object simplifying inferences  : 24
% 0.20/0.46  # Training examples: 0 positive, 0 negative
% 0.20/0.46  # Parsed axioms                        : 12
% 0.20/0.46  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.46  # Initial clauses                      : 34
% 0.20/0.46  # Removed in clause preprocessing      : 9
% 0.20/0.46  # Initial clauses in saturation        : 25
% 0.20/0.46  # Processed clauses                    : 128
% 0.20/0.46  # ...of these trivial                  : 0
% 0.20/0.46  # ...subsumed                          : 24
% 0.20/0.46  # ...remaining for further processing  : 104
% 0.20/0.46  # Other redundant clauses eliminated   : 45
% 0.20/0.46  # Clauses deleted for lack of memory   : 0
% 0.20/0.46  # Backward-subsumed                    : 4
% 0.20/0.46  # Backward-rewritten                   : 1
% 0.20/0.46  # Generated clauses                    : 869
% 0.20/0.46  # ...of the previous two non-trivial   : 763
% 0.20/0.46  # Contextual simplify-reflections      : 4
% 0.20/0.46  # Paramodulations                      : 796
% 0.20/0.46  # Factorizations                       : 4
% 0.20/0.46  # Equation resolutions                 : 69
% 0.20/0.46  # Propositional unsat checks           : 0
% 0.20/0.46  #    Propositional check models        : 0
% 0.20/0.46  #    Propositional check unsatisfiable : 0
% 0.20/0.46  #    Propositional clauses             : 0
% 0.20/0.46  #    Propositional clauses after purity: 0
% 0.20/0.46  #    Propositional unsat core size     : 0
% 0.20/0.46  #    Propositional preprocessing time  : 0.000
% 0.20/0.46  #    Propositional encoding time       : 0.000
% 0.20/0.46  #    Propositional solver time         : 0.000
% 0.20/0.46  #    Success case prop preproc time    : 0.000
% 0.20/0.46  #    Success case prop encoding time   : 0.000
% 0.20/0.46  #    Success case prop solver time     : 0.000
% 0.20/0.46  # Current number of processed clauses  : 91
% 0.20/0.46  #    Positive orientable unit clauses  : 9
% 0.20/0.46  #    Positive unorientable unit clauses: 0
% 0.20/0.46  #    Negative unit clauses             : 0
% 0.20/0.46  #    Non-unit-clauses                  : 82
% 0.20/0.46  # Current number of unprocessed clauses: 657
% 0.20/0.46  # ...number of literals in the above   : 3719
% 0.20/0.46  # Current number of archived formulas  : 0
% 0.20/0.46  # Current number of archived clauses   : 14
% 0.20/0.46  # Clause-clause subsumption calls (NU) : 4563
% 0.20/0.46  # Rec. Clause-clause subsumption calls : 1914
% 0.20/0.46  # Non-unit clause-clause subsumptions  : 32
% 0.20/0.46  # Unit Clause-clause subsumption calls : 76
% 0.20/0.46  # Rewrite failures with RHS unbound    : 0
% 0.20/0.46  # BW rewrite match attempts            : 50
% 0.20/0.46  # BW rewrite match successes           : 1
% 0.20/0.46  # Condensation attempts                : 0
% 0.20/0.46  # Condensation successes               : 0
% 0.20/0.46  # Termbank termtop insertions          : 34571
% 0.20/0.46  
% 0.20/0.46  # -------------------------------------------------
% 0.20/0.46  # User time                : 0.118 s
% 0.20/0.46  # System time              : 0.005 s
% 0.20/0.46  # Total time               : 0.123 s
% 0.20/0.46  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
