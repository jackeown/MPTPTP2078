%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:47:10 EST 2020

% Result     : Theorem 2.94s
% Output     : CNFRefutation 2.94s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 349 expanded)
%              Number of clauses        :   37 ( 165 expanded)
%              Number of leaves         :   12 (  90 expanded)
%              Depth                    :   13
%              Number of atoms          :  180 (1059 expanded)
%              Number of equality atoms :   91 ( 622 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t8_setfam_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(k1_setfam_1(X2),X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_setfam_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(t11_setfam_1,conjecture,(
    ! [X1] : k1_setfam_1(k1_tarski(X1)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

fof(t6_setfam_1,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
         => r1_tarski(X2,X3) )
     => ( X1 = k1_xboole_0
        | r1_tarski(X2,k1_setfam_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_setfam_1)).

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

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(c_0_12,plain,(
    ! [X18,X19] :
      ( ( r1_tarski(X18,X19)
        | X18 != X19 )
      & ( r1_tarski(X19,X18)
        | X18 != X19 )
      & ( ~ r1_tarski(X18,X19)
        | ~ r1_tarski(X19,X18)
        | X18 = X19 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_13,plain,(
    ! [X21,X22,X23,X24,X25,X26,X27,X28,X29,X30] :
      ( ( ~ r2_hidden(X25,X24)
        | X25 = X21
        | X25 = X22
        | X25 = X23
        | X24 != k1_enumset1(X21,X22,X23) )
      & ( X26 != X21
        | r2_hidden(X26,X24)
        | X24 != k1_enumset1(X21,X22,X23) )
      & ( X26 != X22
        | r2_hidden(X26,X24)
        | X24 != k1_enumset1(X21,X22,X23) )
      & ( X26 != X23
        | r2_hidden(X26,X24)
        | X24 != k1_enumset1(X21,X22,X23) )
      & ( esk3_4(X27,X28,X29,X30) != X27
        | ~ r2_hidden(esk3_4(X27,X28,X29,X30),X30)
        | X30 = k1_enumset1(X27,X28,X29) )
      & ( esk3_4(X27,X28,X29,X30) != X28
        | ~ r2_hidden(esk3_4(X27,X28,X29,X30),X30)
        | X30 = k1_enumset1(X27,X28,X29) )
      & ( esk3_4(X27,X28,X29,X30) != X29
        | ~ r2_hidden(esk3_4(X27,X28,X29,X30),X30)
        | X30 = k1_enumset1(X27,X28,X29) )
      & ( r2_hidden(esk3_4(X27,X28,X29,X30),X30)
        | esk3_4(X27,X28,X29,X30) = X27
        | esk3_4(X27,X28,X29,X30) = X28
        | esk3_4(X27,X28,X29,X30) = X29
        | X30 = k1_enumset1(X27,X28,X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

fof(c_0_14,plain,(
    ! [X42,X43,X44] : k2_enumset1(X42,X42,X43,X44) = k1_enumset1(X42,X43,X44) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_15,plain,(
    ! [X45,X46,X47,X48] : k3_enumset1(X45,X45,X46,X47,X48) = k2_enumset1(X45,X46,X47,X48) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_16,plain,(
    ! [X6,X7,X8,X9,X10,X11,X12,X13] :
      ( ( r2_hidden(X9,X6)
        | ~ r2_hidden(X9,X8)
        | X8 != k4_xboole_0(X6,X7) )
      & ( ~ r2_hidden(X9,X7)
        | ~ r2_hidden(X9,X8)
        | X8 != k4_xboole_0(X6,X7) )
      & ( ~ r2_hidden(X10,X6)
        | r2_hidden(X10,X7)
        | r2_hidden(X10,X8)
        | X8 != k4_xboole_0(X6,X7) )
      & ( ~ r2_hidden(esk1_3(X11,X12,X13),X13)
        | ~ r2_hidden(esk1_3(X11,X12,X13),X11)
        | r2_hidden(esk1_3(X11,X12,X13),X12)
        | X13 = k4_xboole_0(X11,X12) )
      & ( r2_hidden(esk1_3(X11,X12,X13),X11)
        | r2_hidden(esk1_3(X11,X12,X13),X13)
        | X13 = k4_xboole_0(X11,X12) )
      & ( ~ r2_hidden(esk1_3(X11,X12,X13),X12)
        | r2_hidden(esk1_3(X11,X12,X13),X13)
        | X13 = k4_xboole_0(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_17,plain,(
    ! [X56,X57,X58] :
      ( ~ r2_hidden(X56,X57)
      | ~ r1_tarski(X56,X58)
      | r1_tarski(k1_setfam_1(X57),X58) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_setfam_1])])).

cnf(c_0_18,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X5,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_23,plain,(
    ! [X20] : k4_xboole_0(X20,k1_xboole_0) = X20 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_24,plain,
    ( r1_tarski(k1_setfam_1(X2),X3)
    | ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k3_enumset1(X4,X4,X4,X5,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_20]),c_0_21])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X2,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_28,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_30,negated_conjecture,(
    ~ ! [X1] : k1_setfam_1(k1_tarski(X1)) = X1 ),
    inference(assume_negation,[status(cth)],[t11_setfam_1])).

cnf(c_0_31,plain,
    ( r1_tarski(k1_setfam_1(X1),X2)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,k3_enumset1(X2,X2,X2,X3,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_26])])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k3_enumset1(X2,X2,X2,X4,X5) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_20]),c_0_21])).

fof(c_0_34,plain,(
    ! [X53,X54] :
      ( ( r2_hidden(esk6_2(X53,X54),X53)
        | X53 = k1_xboole_0
        | r1_tarski(X54,k1_setfam_1(X53)) )
      & ( ~ r1_tarski(X54,esk6_2(X53,X54))
        | X53 = k1_xboole_0
        | r1_tarski(X54,k1_setfam_1(X53)) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_setfam_1])])])])).

cnf(c_0_35,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

fof(c_0_36,plain,(
    ! [X32,X33,X34,X35,X36,X37] :
      ( ( ~ r2_hidden(X34,X33)
        | X34 = X32
        | X33 != k1_tarski(X32) )
      & ( X35 != X32
        | r2_hidden(X35,X33)
        | X33 != k1_tarski(X32) )
      & ( ~ r2_hidden(esk4_2(X36,X37),X37)
        | esk4_2(X36,X37) != X36
        | X37 = k1_tarski(X36) )
      & ( r2_hidden(esk4_2(X36,X37),X37)
        | esk4_2(X36,X37) = X36
        | X37 = k1_tarski(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_37,plain,(
    ! [X39] : k2_tarski(X39,X39) = k1_tarski(X39) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_38,plain,(
    ! [X40,X41] : k1_enumset1(X40,X40,X41) = k2_tarski(X40,X41) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_39,negated_conjecture,(
    k1_setfam_1(k1_tarski(esk7_0)) != esk7_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_30])])])).

cnf(c_0_40,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_41,plain,
    ( r1_tarski(k1_setfam_1(k3_enumset1(X1,X1,X1,X2,X3)),X3) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,k3_enumset1(X1,X1,X1,X2,X3)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_33])])).

cnf(c_0_43,plain,
    ( r2_hidden(esk6_2(X1,X2),X1)
    | X1 = k1_xboole_0
    | r1_tarski(X2,k1_setfam_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_44,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_32])).

cnf(c_0_45,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_46,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_47,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_48,negated_conjecture,
    ( k1_setfam_1(k1_tarski(esk7_0)) != esk7_0 ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_49,plain,
    ( k1_setfam_1(k3_enumset1(X1,X1,X1,X2,X3)) = X3
    | ~ r1_tarski(X3,k1_setfam_1(k3_enumset1(X1,X1,X1,X2,X3))) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_50,plain,
    ( r1_tarski(X1,k1_setfam_1(k3_enumset1(X2,X2,X2,X3,X4)))
    | r2_hidden(esk6_2(k3_enumset1(X2,X2,X2,X3,X4),X1),k3_enumset1(X2,X2,X2,X3,X4)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44])).

cnf(c_0_51,plain,
    ( X1 = X3
    | X2 != k3_enumset1(X3,X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_46]),c_0_47]),c_0_20]),c_0_21])).

cnf(c_0_52,negated_conjecture,
    ( k1_setfam_1(k3_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0)) != esk7_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_46]),c_0_47]),c_0_20]),c_0_21])).

cnf(c_0_53,plain,
    ( k1_setfam_1(k3_enumset1(X1,X1,X1,X2,X3)) = X3
    | r2_hidden(esk6_2(k3_enumset1(X1,X1,X1,X2,X3),X3),k3_enumset1(X1,X1,X1,X2,X3)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_54,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k3_enumset1(X2,X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_51])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(esk6_2(k3_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0),esk7_0),k3_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_56,plain,
    ( X2 = k1_xboole_0
    | r1_tarski(X1,k1_setfam_1(X2))
    | ~ r1_tarski(X1,esk6_2(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_57,negated_conjecture,
    ( esk6_2(k3_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0),esk7_0) = esk7_0 ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_58,negated_conjecture,
    ( k3_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0) = k1_xboole_0
    | r1_tarski(esk7_0,k1_setfam_1(k3_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_25])])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(esk7_0,k1_setfam_1(k3_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0)))
    | k1_setfam_1(k1_xboole_0) != esk7_0 ),
    inference(spm,[status(thm)],[c_0_52,c_0_58])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(esk7_0,k1_setfam_1(k3_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0))) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_58]),c_0_44]),c_0_59])).

cnf(c_0_61,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_60]),c_0_52]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:05:29 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 2.94/3.11  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 2.94/3.11  # and selection function SelectNegativeLiterals.
% 2.94/3.11  #
% 2.94/3.11  # Preprocessing time       : 0.029 s
% 2.94/3.11  # Presaturation interreduction done
% 2.94/3.11  
% 2.94/3.11  # Proof found!
% 2.94/3.11  # SZS status Theorem
% 2.94/3.11  # SZS output start CNFRefutation
% 2.94/3.11  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.94/3.11  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.94/3.11  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.94/3.11  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 2.94/3.11  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.94/3.11  fof(t8_setfam_1, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(k1_setfam_1(X2),X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_setfam_1)).
% 2.94/3.11  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.94/3.11  fof(t11_setfam_1, conjecture, ![X1]:k1_setfam_1(k1_tarski(X1))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_setfam_1)).
% 2.94/3.11  fof(t6_setfam_1, axiom, ![X1, X2]:(![X3]:(r2_hidden(X3,X1)=>r1_tarski(X2,X3))=>(X1=k1_xboole_0|r1_tarski(X2,k1_setfam_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_setfam_1)).
% 2.94/3.11  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.94/3.11  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.94/3.11  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.94/3.11  fof(c_0_12, plain, ![X18, X19]:(((r1_tarski(X18,X19)|X18!=X19)&(r1_tarski(X19,X18)|X18!=X19))&(~r1_tarski(X18,X19)|~r1_tarski(X19,X18)|X18=X19)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 2.94/3.11  fof(c_0_13, plain, ![X21, X22, X23, X24, X25, X26, X27, X28, X29, X30]:(((~r2_hidden(X25,X24)|(X25=X21|X25=X22|X25=X23)|X24!=k1_enumset1(X21,X22,X23))&(((X26!=X21|r2_hidden(X26,X24)|X24!=k1_enumset1(X21,X22,X23))&(X26!=X22|r2_hidden(X26,X24)|X24!=k1_enumset1(X21,X22,X23)))&(X26!=X23|r2_hidden(X26,X24)|X24!=k1_enumset1(X21,X22,X23))))&((((esk3_4(X27,X28,X29,X30)!=X27|~r2_hidden(esk3_4(X27,X28,X29,X30),X30)|X30=k1_enumset1(X27,X28,X29))&(esk3_4(X27,X28,X29,X30)!=X28|~r2_hidden(esk3_4(X27,X28,X29,X30),X30)|X30=k1_enumset1(X27,X28,X29)))&(esk3_4(X27,X28,X29,X30)!=X29|~r2_hidden(esk3_4(X27,X28,X29,X30),X30)|X30=k1_enumset1(X27,X28,X29)))&(r2_hidden(esk3_4(X27,X28,X29,X30),X30)|(esk3_4(X27,X28,X29,X30)=X27|esk3_4(X27,X28,X29,X30)=X28|esk3_4(X27,X28,X29,X30)=X29)|X30=k1_enumset1(X27,X28,X29)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 2.94/3.11  fof(c_0_14, plain, ![X42, X43, X44]:k2_enumset1(X42,X42,X43,X44)=k1_enumset1(X42,X43,X44), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 2.94/3.11  fof(c_0_15, plain, ![X45, X46, X47, X48]:k3_enumset1(X45,X45,X46,X47,X48)=k2_enumset1(X45,X46,X47,X48), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 2.94/3.11  fof(c_0_16, plain, ![X6, X7, X8, X9, X10, X11, X12, X13]:((((r2_hidden(X9,X6)|~r2_hidden(X9,X8)|X8!=k4_xboole_0(X6,X7))&(~r2_hidden(X9,X7)|~r2_hidden(X9,X8)|X8!=k4_xboole_0(X6,X7)))&(~r2_hidden(X10,X6)|r2_hidden(X10,X7)|r2_hidden(X10,X8)|X8!=k4_xboole_0(X6,X7)))&((~r2_hidden(esk1_3(X11,X12,X13),X13)|(~r2_hidden(esk1_3(X11,X12,X13),X11)|r2_hidden(esk1_3(X11,X12,X13),X12))|X13=k4_xboole_0(X11,X12))&((r2_hidden(esk1_3(X11,X12,X13),X11)|r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k4_xboole_0(X11,X12))&(~r2_hidden(esk1_3(X11,X12,X13),X12)|r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k4_xboole_0(X11,X12))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 2.94/3.11  fof(c_0_17, plain, ![X56, X57, X58]:(~r2_hidden(X56,X57)|~r1_tarski(X56,X58)|r1_tarski(k1_setfam_1(X57),X58)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_setfam_1])])).
% 2.94/3.11  cnf(c_0_18, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_12])).
% 2.94/3.11  cnf(c_0_19, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X5,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 2.94/3.11  cnf(c_0_20, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.94/3.11  cnf(c_0_21, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 2.94/3.11  cnf(c_0_22, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 2.94/3.11  fof(c_0_23, plain, ![X20]:k4_xboole_0(X20,k1_xboole_0)=X20, inference(variable_rename,[status(thm)],[t3_boole])).
% 2.94/3.11  cnf(c_0_24, plain, (r1_tarski(k1_setfam_1(X2),X3)|~r2_hidden(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 2.94/3.11  cnf(c_0_25, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_18])).
% 2.94/3.11  cnf(c_0_26, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k3_enumset1(X4,X4,X4,X5,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_20]), c_0_21])).
% 2.94/3.11  cnf(c_0_27, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X2,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 2.94/3.11  cnf(c_0_28, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_22])).
% 2.94/3.11  cnf(c_0_29, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_23])).
% 2.94/3.11  fof(c_0_30, negated_conjecture, ~(![X1]:k1_setfam_1(k1_tarski(X1))=X1), inference(assume_negation,[status(cth)],[t11_setfam_1])).
% 2.94/3.11  cnf(c_0_31, plain, (r1_tarski(k1_setfam_1(X1),X2)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 2.94/3.11  cnf(c_0_32, plain, (r2_hidden(X1,k3_enumset1(X2,X2,X2,X3,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_26])])).
% 2.94/3.11  cnf(c_0_33, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k3_enumset1(X2,X2,X2,X4,X5)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_20]), c_0_21])).
% 2.94/3.11  fof(c_0_34, plain, ![X53, X54]:((r2_hidden(esk6_2(X53,X54),X53)|(X53=k1_xboole_0|r1_tarski(X54,k1_setfam_1(X53))))&(~r1_tarski(X54,esk6_2(X53,X54))|(X53=k1_xboole_0|r1_tarski(X54,k1_setfam_1(X53))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_setfam_1])])])])).
% 2.94/3.11  cnf(c_0_35, plain, (~r2_hidden(X1,k1_xboole_0)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 2.94/3.11  fof(c_0_36, plain, ![X32, X33, X34, X35, X36, X37]:(((~r2_hidden(X34,X33)|X34=X32|X33!=k1_tarski(X32))&(X35!=X32|r2_hidden(X35,X33)|X33!=k1_tarski(X32)))&((~r2_hidden(esk4_2(X36,X37),X37)|esk4_2(X36,X37)!=X36|X37=k1_tarski(X36))&(r2_hidden(esk4_2(X36,X37),X37)|esk4_2(X36,X37)=X36|X37=k1_tarski(X36)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 2.94/3.11  fof(c_0_37, plain, ![X39]:k2_tarski(X39,X39)=k1_tarski(X39), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 2.94/3.11  fof(c_0_38, plain, ![X40, X41]:k1_enumset1(X40,X40,X41)=k2_tarski(X40,X41), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 2.94/3.11  fof(c_0_39, negated_conjecture, k1_setfam_1(k1_tarski(esk7_0))!=esk7_0, inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_30])])])).
% 2.94/3.11  cnf(c_0_40, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 2.94/3.11  cnf(c_0_41, plain, (r1_tarski(k1_setfam_1(k3_enumset1(X1,X1,X1,X2,X3)),X3)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 2.94/3.11  cnf(c_0_42, plain, (r2_hidden(X1,k3_enumset1(X1,X1,X1,X2,X3))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_33])])).
% 2.94/3.11  cnf(c_0_43, plain, (r2_hidden(esk6_2(X1,X2),X1)|X1=k1_xboole_0|r1_tarski(X2,k1_setfam_1(X1))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 2.94/3.11  cnf(c_0_44, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_35, c_0_32])).
% 2.94/3.11  cnf(c_0_45, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 2.94/3.11  cnf(c_0_46, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 2.94/3.11  cnf(c_0_47, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 2.94/3.11  cnf(c_0_48, negated_conjecture, (k1_setfam_1(k1_tarski(esk7_0))!=esk7_0), inference(split_conjunct,[status(thm)],[c_0_39])).
% 2.94/3.11  cnf(c_0_49, plain, (k1_setfam_1(k3_enumset1(X1,X1,X1,X2,X3))=X3|~r1_tarski(X3,k1_setfam_1(k3_enumset1(X1,X1,X1,X2,X3)))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 2.94/3.11  cnf(c_0_50, plain, (r1_tarski(X1,k1_setfam_1(k3_enumset1(X2,X2,X2,X3,X4)))|r2_hidden(esk6_2(k3_enumset1(X2,X2,X2,X3,X4),X1),k3_enumset1(X2,X2,X2,X3,X4))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44])).
% 2.94/3.11  cnf(c_0_51, plain, (X1=X3|X2!=k3_enumset1(X3,X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_46]), c_0_47]), c_0_20]), c_0_21])).
% 2.94/3.11  cnf(c_0_52, negated_conjecture, (k1_setfam_1(k3_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0))!=esk7_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_46]), c_0_47]), c_0_20]), c_0_21])).
% 2.94/3.11  cnf(c_0_53, plain, (k1_setfam_1(k3_enumset1(X1,X1,X1,X2,X3))=X3|r2_hidden(esk6_2(k3_enumset1(X1,X1,X1,X2,X3),X3),k3_enumset1(X1,X1,X1,X2,X3))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 2.94/3.11  cnf(c_0_54, plain, (X1=X2|~r2_hidden(X1,k3_enumset1(X2,X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_51])).
% 2.94/3.11  cnf(c_0_55, negated_conjecture, (r2_hidden(esk6_2(k3_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0),esk7_0),k3_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 2.94/3.11  cnf(c_0_56, plain, (X2=k1_xboole_0|r1_tarski(X1,k1_setfam_1(X2))|~r1_tarski(X1,esk6_2(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 2.94/3.11  cnf(c_0_57, negated_conjecture, (esk6_2(k3_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0),esk7_0)=esk7_0), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 2.94/3.11  cnf(c_0_58, negated_conjecture, (k3_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0)=k1_xboole_0|r1_tarski(esk7_0,k1_setfam_1(k3_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_25])])).
% 2.94/3.11  cnf(c_0_59, negated_conjecture, (r1_tarski(esk7_0,k1_setfam_1(k3_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0)))|k1_setfam_1(k1_xboole_0)!=esk7_0), inference(spm,[status(thm)],[c_0_52, c_0_58])).
% 2.94/3.11  cnf(c_0_60, negated_conjecture, (r1_tarski(esk7_0,k1_setfam_1(k3_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0)))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_58]), c_0_44]), c_0_59])).
% 2.94/3.11  cnf(c_0_61, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_60]), c_0_52]), ['proof']).
% 2.94/3.11  # SZS output end CNFRefutation
% 2.94/3.11  # Proof object total steps             : 62
% 2.94/3.11  # Proof object clause steps            : 37
% 2.94/3.11  # Proof object formula steps           : 25
% 2.94/3.11  # Proof object conjectures             : 11
% 2.94/3.11  # Proof object clause conjectures      : 8
% 2.94/3.11  # Proof object formula conjectures     : 3
% 2.94/3.11  # Proof object initial clauses used    : 15
% 2.94/3.11  # Proof object initial formulas used   : 12
% 2.94/3.11  # Proof object generating inferences   : 13
% 2.94/3.11  # Proof object simplifying inferences  : 25
% 2.94/3.11  # Training examples: 0 positive, 0 negative
% 2.94/3.11  # Parsed axioms                        : 14
% 2.94/3.11  # Removed by relevancy pruning/SinE    : 0
% 2.94/3.11  # Initial clauses                      : 34
% 2.94/3.11  # Removed in clause preprocessing      : 4
% 2.94/3.11  # Initial clauses in saturation        : 30
% 2.94/3.11  # Processed clauses                    : 3725
% 2.94/3.11  # ...of these trivial                  : 31
% 2.94/3.11  # ...subsumed                          : 2640
% 2.94/3.11  # ...remaining for further processing  : 1054
% 2.94/3.11  # Other redundant clauses eliminated   : 12982
% 2.94/3.11  # Clauses deleted for lack of memory   : 0
% 2.94/3.11  # Backward-subsumed                    : 15
% 2.94/3.11  # Backward-rewritten                   : 8
% 2.94/3.11  # Generated clauses                    : 352376
% 2.94/3.11  # ...of the previous two non-trivial   : 333633
% 2.94/3.11  # Contextual simplify-reflections      : 8
% 2.94/3.11  # Paramodulations                      : 339282
% 2.94/3.11  # Factorizations                       : 116
% 2.94/3.11  # Equation resolutions                 : 12982
% 2.94/3.11  # Propositional unsat checks           : 0
% 2.94/3.11  #    Propositional check models        : 0
% 2.94/3.11  #    Propositional check unsatisfiable : 0
% 2.94/3.11  #    Propositional clauses             : 0
% 2.94/3.11  #    Propositional clauses after purity: 0
% 2.94/3.11  #    Propositional unsat core size     : 0
% 2.94/3.11  #    Propositional preprocessing time  : 0.000
% 2.94/3.11  #    Propositional encoding time       : 0.000
% 2.94/3.11  #    Propositional solver time         : 0.000
% 2.94/3.11  #    Success case prop preproc time    : 0.000
% 2.94/3.11  #    Success case prop encoding time   : 0.000
% 2.94/3.11  #    Success case prop solver time     : 0.000
% 2.94/3.11  # Current number of processed clauses  : 992
% 2.94/3.11  #    Positive orientable unit clauses  : 35
% 2.94/3.11  #    Positive unorientable unit clauses: 0
% 2.94/3.11  #    Negative unit clauses             : 3
% 2.94/3.11  #    Non-unit-clauses                  : 954
% 2.94/3.11  # Current number of unprocessed clauses: 329753
% 2.94/3.11  # ...number of literals in the above   : 1862739
% 2.94/3.11  # Current number of archived formulas  : 0
% 2.94/3.11  # Current number of archived clauses   : 55
% 2.94/3.11  # Clause-clause subsumption calls (NU) : 94534
% 2.94/3.11  # Rec. Clause-clause subsumption calls : 27075
% 2.94/3.11  # Non-unit clause-clause subsumptions  : 2456
% 2.94/3.11  # Unit Clause-clause subsumption calls : 2680
% 2.94/3.11  # Rewrite failures with RHS unbound    : 0
% 2.94/3.11  # BW rewrite match attempts            : 86
% 2.94/3.11  # BW rewrite match successes           : 7
% 2.94/3.11  # Condensation attempts                : 0
% 2.94/3.11  # Condensation successes               : 0
% 2.94/3.11  # Termbank termtop insertions          : 10093192
% 2.94/3.12  
% 2.94/3.12  # -------------------------------------------------
% 2.94/3.12  # User time                : 2.647 s
% 2.94/3.12  # System time              : 0.135 s
% 2.94/3.12  # Total time               : 2.782 s
% 2.94/3.12  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
