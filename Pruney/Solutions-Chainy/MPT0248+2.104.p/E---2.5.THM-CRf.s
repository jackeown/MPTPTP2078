%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:39:53 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   98 (1058 expanded)
%              Number of clauses        :   59 ( 433 expanded)
%              Number of leaves         :   19 ( 291 expanded)
%              Depth                    :   11
%              Number of atoms          :  224 (2372 expanded)
%              Number of equality atoms :  112 (1973 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(t72_xboole_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( k2_xboole_0(X1,X2) = k2_xboole_0(X3,X4)
        & r1_xboole_0(X3,X1)
        & r1_xboole_0(X4,X2) )
     => X3 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_xboole_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t77_enumset1,axiom,(
    ! [X1,X2] : k2_enumset1(X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t37_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(t4_boole,axiom,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(l45_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k2_tarski(X2,X3))
    <=> ~ ( X1 != k1_xboole_0
          & X1 != k1_tarski(X2)
          & X1 != k1_tarski(X3)
          & X1 != k2_tarski(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

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

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t9_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_xboole_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( k1_tarski(X1) = k2_xboole_0(X2,X3)
          & ~ ( X2 = k1_tarski(X1)
              & X3 = k1_tarski(X1) )
          & ~ ( X2 = k1_xboole_0
              & X3 = k1_tarski(X1) )
          & ~ ( X2 = k1_tarski(X1)
              & X3 = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t43_zfmisc_1])).

fof(c_0_20,plain,(
    ! [X37,X38,X39,X40] :
      ( k2_xboole_0(X37,X38) != k2_xboole_0(X39,X40)
      | ~ r1_xboole_0(X39,X37)
      | ~ r1_xboole_0(X40,X38)
      | X39 = X38 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t72_xboole_1])])).

fof(c_0_21,plain,(
    ! [X25] : k2_xboole_0(X25,k1_xboole_0) = X25 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_22,plain,(
    ! [X36] : r1_xboole_0(X36,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

fof(c_0_23,plain,(
    ! [X23,X24] :
      ( ( r1_tarski(X23,X24)
        | X23 != X24 )
      & ( r1_tarski(X24,X23)
        | X23 != X24 )
      & ( ~ r1_tarski(X23,X24)
        | ~ r1_tarski(X24,X23)
        | X23 = X24 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_24,negated_conjecture,
    ( k1_tarski(esk4_0) = k2_xboole_0(esk5_0,esk6_0)
    & ( esk5_0 != k1_tarski(esk4_0)
      | esk6_0 != k1_tarski(esk4_0) )
    & ( esk5_0 != k1_xboole_0
      | esk6_0 != k1_tarski(esk4_0) )
    & ( esk5_0 != k1_tarski(esk4_0)
      | esk6_0 != k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

fof(c_0_25,plain,(
    ! [X51] : k2_tarski(X51,X51) = k1_tarski(X51) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_26,plain,(
    ! [X52,X53] : k2_enumset1(X52,X52,X52,X53) = k2_tarski(X52,X53) ),
    inference(variable_rename,[status(thm)],[t77_enumset1])).

cnf(c_0_27,plain,
    ( X3 = X2
    | k2_xboole_0(X1,X2) != k2_xboole_0(X3,X4)
    | ~ r1_xboole_0(X3,X1)
    | ~ r1_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_30,plain,(
    ! [X17,X18,X20,X21,X22] :
      ( ( r1_xboole_0(X17,X18)
        | r2_hidden(esk3_2(X17,X18),k3_xboole_0(X17,X18)) )
      & ( ~ r2_hidden(X22,k3_xboole_0(X20,X21))
        | ~ r1_xboole_0(X20,X21) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_31,plain,(
    ! [X33,X34] : k4_xboole_0(X33,k4_xboole_0(X33,X34)) = k3_xboole_0(X33,X34) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_32,plain,(
    ! [X30,X31] :
      ( ( k4_xboole_0(X30,X31) != k1_xboole_0
        | r1_tarski(X30,X31) )
      & ( ~ r1_tarski(X30,X31)
        | k4_xboole_0(X30,X31) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_xboole_1])])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_34,plain,(
    ! [X41,X42] : r1_xboole_0(k4_xboole_0(X41,X42),X42) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

fof(c_0_35,plain,(
    ! [X35] : k4_xboole_0(k1_xboole_0,X35) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

cnf(c_0_36,negated_conjecture,
    ( esk5_0 != k1_xboole_0
    | esk6_0 != k1_tarski(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_37,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_38,plain,
    ( k2_enumset1(X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_39,negated_conjecture,
    ( k1_tarski(esk4_0) = k2_xboole_0(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_40,plain,
    ( k1_xboole_0 = X1
    | ~ r1_xboole_0(X1,k2_xboole_0(X1,X2)) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])])])).

cnf(c_0_41,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk3_2(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_42,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_43,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_44,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_33])).

fof(c_0_45,plain,(
    ! [X32] : k4_xboole_0(X32,k1_xboole_0) = X32 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_46,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_47,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_48,negated_conjecture,
    ( esk5_0 != k1_xboole_0
    | esk6_0 != k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_37]),c_0_38])).

cnf(c_0_49,negated_conjecture,
    ( k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0) = k2_xboole_0(esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_37]),c_0_38])).

cnf(c_0_50,plain,
    ( k1_xboole_0 = X1
    | ~ r1_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_28])).

cnf(c_0_51,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk3_2(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_52,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_53,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_54,plain,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

fof(c_0_55,plain,(
    ! [X54,X55,X56] :
      ( ( ~ r1_tarski(X54,k2_tarski(X55,X56))
        | X54 = k1_xboole_0
        | X54 = k1_tarski(X55)
        | X54 = k1_tarski(X56)
        | X54 = k2_tarski(X55,X56) )
      & ( X54 != k1_xboole_0
        | r1_tarski(X54,k2_tarski(X55,X56)) )
      & ( X54 != k1_tarski(X55)
        | r1_tarski(X54,k2_tarski(X55,X56)) )
      & ( X54 != k1_tarski(X56)
        | r1_tarski(X54,k2_tarski(X55,X56)) )
      & ( X54 != k2_tarski(X55,X56)
        | r1_tarski(X54,k2_tarski(X55,X56)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l45_zfmisc_1])])])).

cnf(c_0_56,negated_conjecture,
    ( k2_xboole_0(esk5_0,esk6_0) != esk6_0
    | esk5_0 != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_57,plain,
    ( k1_xboole_0 = X1
    | r2_hidden(esk3_2(X1,X1),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52]),c_0_53])).

cnf(c_0_58,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_xboole_0(k2_xboole_0(X1,X2),X1) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_54])])])).

cnf(c_0_59,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_tarski(X2)
    | X1 = k1_tarski(X3)
    | X1 = k2_tarski(X2,X3)
    | ~ r1_tarski(X1,k2_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

fof(c_0_60,plain,(
    ! [X11,X12,X14,X15,X16] :
      ( ( r2_hidden(esk2_2(X11,X12),X11)
        | r1_xboole_0(X11,X12) )
      & ( r2_hidden(esk2_2(X11,X12),X12)
        | r1_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X16,X14)
        | ~ r2_hidden(X16,X15)
        | ~ r1_xboole_0(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_61,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(esk3_2(esk5_0,esk5_0),esk5_0)
    | k2_xboole_0(k1_xboole_0,esk6_0) != esk6_0 ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_63,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_58,c_0_29])).

fof(c_0_64,plain,(
    ! [X48,X49,X50] :
      ( ~ r1_tarski(X48,X49)
      | r1_tarski(k2_xboole_0(X48,X50),k2_xboole_0(X49,X50)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_xboole_1])])).

fof(c_0_65,plain,(
    ! [X29] : r1_tarski(k1_xboole_0,X29) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_66,negated_conjecture,
    ( esk5_0 != k1_tarski(esk4_0)
    | esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_67,plain,
    ( X1 = k1_xboole_0
    | X1 = k2_enumset1(X3,X3,X3,X3)
    | X1 = k2_enumset1(X2,X2,X2,X3)
    | X1 = k2_enumset1(X2,X2,X2,X2)
    | ~ r1_tarski(X1,k2_enumset1(X2,X2,X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_38]),c_0_38])).

fof(c_0_68,plain,(
    ! [X43,X44] : r1_tarski(X43,k2_xboole_0(X43,X44)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_69,negated_conjecture,
    ( esk5_0 != k1_tarski(esk4_0)
    | esk6_0 != k1_tarski(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_70,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_71,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_72,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(esk3_2(esk5_0,esk5_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_63])])).

cnf(c_0_74,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_75,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_76,negated_conjecture,
    ( esk6_0 != k1_xboole_0
    | esk5_0 != k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_37]),c_0_38])).

cnf(c_0_77,negated_conjecture,
    ( X1 = k2_xboole_0(esk5_0,esk6_0)
    | X1 = k1_xboole_0
    | ~ r1_tarski(X1,k2_xboole_0(esk5_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_49]),c_0_49])])).

cnf(c_0_78,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_79,negated_conjecture,
    ( esk5_0 != k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)
    | esk6_0 != k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_37]),c_0_37]),c_0_38]),c_0_38])).

cnf(c_0_80,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_81,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_82,negated_conjecture,
    ( r2_hidden(esk3_2(esk5_0,esk5_0),X1)
    | ~ r1_tarski(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_83,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_63])).

cnf(c_0_84,negated_conjecture,
    ( k2_xboole_0(esk5_0,esk6_0) != esk5_0
    | esk6_0 != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_76,c_0_49])).

cnf(c_0_85,negated_conjecture,
    ( k2_xboole_0(esk5_0,esk6_0) = esk5_0
    | esk5_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_86,negated_conjecture,
    ( k2_xboole_0(esk5_0,esk6_0) != esk5_0
    | k2_xboole_0(esk5_0,esk6_0) != esk6_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_49]),c_0_49])).

cnf(c_0_87,plain,
    ( ~ r1_xboole_0(X2,X3)
    | ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_80,c_0_42])).

cnf(c_0_88,negated_conjecture,
    ( r2_hidden(esk2_2(X1,esk5_0),esk5_0)
    | ~ r2_hidden(esk3_2(esk5_0,esk5_0),X1) ),
    inference(spm,[status(thm)],[c_0_81,c_0_73])).

cnf(c_0_89,negated_conjecture,
    ( r2_hidden(esk3_2(esk5_0,esk5_0),k2_xboole_0(esk5_0,X1)) ),
    inference(spm,[status(thm)],[c_0_82,c_0_78])).

cnf(c_0_90,negated_conjecture,
    ( k2_xboole_0(esk5_0,esk6_0) = esk6_0
    | esk6_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_77,c_0_83])).

cnf(c_0_91,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk6_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_92,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk6_0 != esk5_0 ),
    inference(spm,[status(thm)],[c_0_86,c_0_85])).

cnf(c_0_93,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_29]),c_0_53])).

cnf(c_0_94,negated_conjecture,
    ( r2_hidden(esk2_2(k2_xboole_0(esk5_0,X1),esk5_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_95,negated_conjecture,
    ( esk5_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_90]),c_0_91]),c_0_92])).

cnf(c_0_96,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_93,c_0_47])).

cnf(c_0_97,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_94,c_0_95]),c_0_63]),c_0_95]),c_0_95]),c_0_96]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:15:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.40  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.12/0.40  # and selection function SelectNegativeLiterals.
% 0.12/0.40  #
% 0.12/0.40  # Preprocessing time       : 0.028 s
% 0.12/0.40  # Presaturation interreduction done
% 0.12/0.40  
% 0.12/0.40  # Proof found!
% 0.12/0.40  # SZS status Theorem
% 0.12/0.40  # SZS output start CNFRefutation
% 0.12/0.40  fof(t43_zfmisc_1, conjecture, ![X1, X2, X3]:~((((k1_tarski(X1)=k2_xboole_0(X2,X3)&~((X2=k1_tarski(X1)&X3=k1_tarski(X1))))&~((X2=k1_xboole_0&X3=k1_tarski(X1))))&~((X2=k1_tarski(X1)&X3=k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 0.12/0.40  fof(t72_xboole_1, axiom, ![X1, X2, X3, X4]:(((k2_xboole_0(X1,X2)=k2_xboole_0(X3,X4)&r1_xboole_0(X3,X1))&r1_xboole_0(X4,X2))=>X3=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_xboole_1)).
% 0.12/0.40  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 0.12/0.40  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.12/0.40  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.12/0.40  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.12/0.40  fof(t77_enumset1, axiom, ![X1, X2]:k2_enumset1(X1,X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_enumset1)).
% 0.12/0.40  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.12/0.40  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.12/0.40  fof(t37_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_xboole_1)).
% 0.12/0.40  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 0.12/0.40  fof(t4_boole, axiom, ![X1]:k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 0.12/0.40  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 0.12/0.40  fof(l45_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k2_tarski(X2,X3))<=>~((((X1!=k1_xboole_0&X1!=k1_tarski(X2))&X1!=k1_tarski(X3))&X1!=k2_tarski(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 0.12/0.40  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.12/0.40  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.12/0.40  fof(t9_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_xboole_1)).
% 0.12/0.40  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.12/0.40  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.12/0.40  fof(c_0_19, negated_conjecture, ~(![X1, X2, X3]:~((((k1_tarski(X1)=k2_xboole_0(X2,X3)&~((X2=k1_tarski(X1)&X3=k1_tarski(X1))))&~((X2=k1_xboole_0&X3=k1_tarski(X1))))&~((X2=k1_tarski(X1)&X3=k1_xboole_0))))), inference(assume_negation,[status(cth)],[t43_zfmisc_1])).
% 0.12/0.40  fof(c_0_20, plain, ![X37, X38, X39, X40]:(k2_xboole_0(X37,X38)!=k2_xboole_0(X39,X40)|~r1_xboole_0(X39,X37)|~r1_xboole_0(X40,X38)|X39=X38), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t72_xboole_1])])).
% 0.12/0.40  fof(c_0_21, plain, ![X25]:k2_xboole_0(X25,k1_xboole_0)=X25, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.12/0.40  fof(c_0_22, plain, ![X36]:r1_xboole_0(X36,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.12/0.40  fof(c_0_23, plain, ![X23, X24]:(((r1_tarski(X23,X24)|X23!=X24)&(r1_tarski(X24,X23)|X23!=X24))&(~r1_tarski(X23,X24)|~r1_tarski(X24,X23)|X23=X24)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.12/0.40  fof(c_0_24, negated_conjecture, (((k1_tarski(esk4_0)=k2_xboole_0(esk5_0,esk6_0)&(esk5_0!=k1_tarski(esk4_0)|esk6_0!=k1_tarski(esk4_0)))&(esk5_0!=k1_xboole_0|esk6_0!=k1_tarski(esk4_0)))&(esk5_0!=k1_tarski(esk4_0)|esk6_0!=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).
% 0.12/0.40  fof(c_0_25, plain, ![X51]:k2_tarski(X51,X51)=k1_tarski(X51), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.12/0.40  fof(c_0_26, plain, ![X52, X53]:k2_enumset1(X52,X52,X52,X53)=k2_tarski(X52,X53), inference(variable_rename,[status(thm)],[t77_enumset1])).
% 0.12/0.40  cnf(c_0_27, plain, (X3=X2|k2_xboole_0(X1,X2)!=k2_xboole_0(X3,X4)|~r1_xboole_0(X3,X1)|~r1_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.40  cnf(c_0_28, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.12/0.40  cnf(c_0_29, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.12/0.40  fof(c_0_30, plain, ![X17, X18, X20, X21, X22]:((r1_xboole_0(X17,X18)|r2_hidden(esk3_2(X17,X18),k3_xboole_0(X17,X18)))&(~r2_hidden(X22,k3_xboole_0(X20,X21))|~r1_xboole_0(X20,X21))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.12/0.40  fof(c_0_31, plain, ![X33, X34]:k4_xboole_0(X33,k4_xboole_0(X33,X34))=k3_xboole_0(X33,X34), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.12/0.40  fof(c_0_32, plain, ![X30, X31]:((k4_xboole_0(X30,X31)!=k1_xboole_0|r1_tarski(X30,X31))&(~r1_tarski(X30,X31)|k4_xboole_0(X30,X31)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_xboole_1])])).
% 0.12/0.40  cnf(c_0_33, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.12/0.40  fof(c_0_34, plain, ![X41, X42]:r1_xboole_0(k4_xboole_0(X41,X42),X42), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 0.12/0.40  fof(c_0_35, plain, ![X35]:k4_xboole_0(k1_xboole_0,X35)=k1_xboole_0, inference(variable_rename,[status(thm)],[t4_boole])).
% 0.12/0.40  cnf(c_0_36, negated_conjecture, (esk5_0!=k1_xboole_0|esk6_0!=k1_tarski(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.12/0.40  cnf(c_0_37, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.12/0.40  cnf(c_0_38, plain, (k2_enumset1(X1,X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.12/0.40  cnf(c_0_39, negated_conjecture, (k1_tarski(esk4_0)=k2_xboole_0(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.12/0.40  cnf(c_0_40, plain, (k1_xboole_0=X1|~r1_xboole_0(X1,k2_xboole_0(X1,X2))), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29])])])).
% 0.12/0.40  cnf(c_0_41, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk3_2(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.12/0.40  cnf(c_0_42, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.12/0.40  cnf(c_0_43, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.12/0.40  cnf(c_0_44, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_33])).
% 0.12/0.40  fof(c_0_45, plain, ![X32]:k4_xboole_0(X32,k1_xboole_0)=X32, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.12/0.40  cnf(c_0_46, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.12/0.40  cnf(c_0_47, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.12/0.40  cnf(c_0_48, negated_conjecture, (esk5_0!=k1_xboole_0|esk6_0!=k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_37]), c_0_38])).
% 0.12/0.40  cnf(c_0_49, negated_conjecture, (k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)=k2_xboole_0(esk5_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_37]), c_0_38])).
% 0.12/0.40  cnf(c_0_50, plain, (k1_xboole_0=X1|~r1_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_40, c_0_28])).
% 0.12/0.40  cnf(c_0_51, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk3_2(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))), inference(rw,[status(thm)],[c_0_41, c_0_42])).
% 0.12/0.40  cnf(c_0_52, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.12/0.40  cnf(c_0_53, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.12/0.40  cnf(c_0_54, plain, (r1_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.12/0.40  fof(c_0_55, plain, ![X54, X55, X56]:((~r1_tarski(X54,k2_tarski(X55,X56))|(X54=k1_xboole_0|X54=k1_tarski(X55)|X54=k1_tarski(X56)|X54=k2_tarski(X55,X56)))&((((X54!=k1_xboole_0|r1_tarski(X54,k2_tarski(X55,X56)))&(X54!=k1_tarski(X55)|r1_tarski(X54,k2_tarski(X55,X56))))&(X54!=k1_tarski(X56)|r1_tarski(X54,k2_tarski(X55,X56))))&(X54!=k2_tarski(X55,X56)|r1_tarski(X54,k2_tarski(X55,X56))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l45_zfmisc_1])])])).
% 0.12/0.40  cnf(c_0_56, negated_conjecture, (k2_xboole_0(esk5_0,esk6_0)!=esk6_0|esk5_0!=k1_xboole_0), inference(rw,[status(thm)],[c_0_48, c_0_49])).
% 0.12/0.40  cnf(c_0_57, plain, (k1_xboole_0=X1|r2_hidden(esk3_2(X1,X1),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52]), c_0_53])).
% 0.12/0.40  cnf(c_0_58, plain, (k2_xboole_0(X1,X2)=X2|~r1_xboole_0(k2_xboole_0(X1,X2),X1)), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_54])])])).
% 0.12/0.40  cnf(c_0_59, plain, (X1=k1_xboole_0|X1=k1_tarski(X2)|X1=k1_tarski(X3)|X1=k2_tarski(X2,X3)|~r1_tarski(X1,k2_tarski(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.12/0.40  fof(c_0_60, plain, ![X11, X12, X14, X15, X16]:(((r2_hidden(esk2_2(X11,X12),X11)|r1_xboole_0(X11,X12))&(r2_hidden(esk2_2(X11,X12),X12)|r1_xboole_0(X11,X12)))&(~r2_hidden(X16,X14)|~r2_hidden(X16,X15)|~r1_xboole_0(X14,X15))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.12/0.40  fof(c_0_61, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.12/0.40  cnf(c_0_62, negated_conjecture, (r2_hidden(esk3_2(esk5_0,esk5_0),esk5_0)|k2_xboole_0(k1_xboole_0,esk6_0)!=esk6_0), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.12/0.40  cnf(c_0_63, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_58, c_0_29])).
% 0.12/0.40  fof(c_0_64, plain, ![X48, X49, X50]:(~r1_tarski(X48,X49)|r1_tarski(k2_xboole_0(X48,X50),k2_xboole_0(X49,X50))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_xboole_1])])).
% 0.12/0.40  fof(c_0_65, plain, ![X29]:r1_tarski(k1_xboole_0,X29), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.12/0.40  cnf(c_0_66, negated_conjecture, (esk5_0!=k1_tarski(esk4_0)|esk6_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.12/0.40  cnf(c_0_67, plain, (X1=k1_xboole_0|X1=k2_enumset1(X3,X3,X3,X3)|X1=k2_enumset1(X2,X2,X2,X3)|X1=k2_enumset1(X2,X2,X2,X2)|~r1_tarski(X1,k2_enumset1(X2,X2,X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_38]), c_0_38])).
% 0.12/0.40  fof(c_0_68, plain, ![X43, X44]:r1_tarski(X43,k2_xboole_0(X43,X44)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.12/0.40  cnf(c_0_69, negated_conjecture, (esk5_0!=k1_tarski(esk4_0)|esk6_0!=k1_tarski(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.12/0.40  cnf(c_0_70, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.12/0.40  cnf(c_0_71, plain, (r2_hidden(esk2_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.12/0.40  cnf(c_0_72, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.12/0.40  cnf(c_0_73, negated_conjecture, (r2_hidden(esk3_2(esk5_0,esk5_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_63])])).
% 0.12/0.40  cnf(c_0_74, plain, (r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X3))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.12/0.40  cnf(c_0_75, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.12/0.40  cnf(c_0_76, negated_conjecture, (esk6_0!=k1_xboole_0|esk5_0!=k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_37]), c_0_38])).
% 0.12/0.40  cnf(c_0_77, negated_conjecture, (X1=k2_xboole_0(esk5_0,esk6_0)|X1=k1_xboole_0|~r1_tarski(X1,k2_xboole_0(esk5_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_49]), c_0_49])])).
% 0.12/0.40  cnf(c_0_78, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.12/0.40  cnf(c_0_79, negated_conjecture, (esk5_0!=k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)|esk6_0!=k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69, c_0_37]), c_0_37]), c_0_38]), c_0_38])).
% 0.12/0.40  cnf(c_0_80, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.12/0.40  cnf(c_0_81, plain, (r2_hidden(esk2_2(X1,X2),X2)|~r2_hidden(X3,X2)|~r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 0.12/0.40  cnf(c_0_82, negated_conjecture, (r2_hidden(esk3_2(esk5_0,esk5_0),X1)|~r1_tarski(esk5_0,X1)), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.12/0.40  cnf(c_0_83, plain, (r1_tarski(X1,k2_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_63])).
% 0.12/0.40  cnf(c_0_84, negated_conjecture, (k2_xboole_0(esk5_0,esk6_0)!=esk5_0|esk6_0!=k1_xboole_0), inference(rw,[status(thm)],[c_0_76, c_0_49])).
% 0.12/0.40  cnf(c_0_85, negated_conjecture, (k2_xboole_0(esk5_0,esk6_0)=esk5_0|esk5_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 0.12/0.40  cnf(c_0_86, negated_conjecture, (k2_xboole_0(esk5_0,esk6_0)!=esk5_0|k2_xboole_0(esk5_0,esk6_0)!=esk6_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79, c_0_49]), c_0_49])).
% 0.12/0.40  cnf(c_0_87, plain, (~r1_xboole_0(X2,X3)|~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_80, c_0_42])).
% 0.12/0.40  cnf(c_0_88, negated_conjecture, (r2_hidden(esk2_2(X1,esk5_0),esk5_0)|~r2_hidden(esk3_2(esk5_0,esk5_0),X1)), inference(spm,[status(thm)],[c_0_81, c_0_73])).
% 0.12/0.40  cnf(c_0_89, negated_conjecture, (r2_hidden(esk3_2(esk5_0,esk5_0),k2_xboole_0(esk5_0,X1))), inference(spm,[status(thm)],[c_0_82, c_0_78])).
% 0.12/0.40  cnf(c_0_90, negated_conjecture, (k2_xboole_0(esk5_0,esk6_0)=esk6_0|esk6_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_77, c_0_83])).
% 0.12/0.40  cnf(c_0_91, negated_conjecture, (esk5_0=k1_xboole_0|esk6_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_84, c_0_85])).
% 0.12/0.40  cnf(c_0_92, negated_conjecture, (esk5_0=k1_xboole_0|esk6_0!=esk5_0), inference(spm,[status(thm)],[c_0_86, c_0_85])).
% 0.12/0.40  cnf(c_0_93, plain, (~r2_hidden(X1,k4_xboole_0(X2,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_29]), c_0_53])).
% 0.12/0.40  cnf(c_0_94, negated_conjecture, (r2_hidden(esk2_2(k2_xboole_0(esk5_0,X1),esk5_0),esk5_0)), inference(spm,[status(thm)],[c_0_88, c_0_89])).
% 0.12/0.40  cnf(c_0_95, negated_conjecture, (esk5_0=k1_xboole_0), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_90]), c_0_91]), c_0_92])).
% 0.12/0.40  cnf(c_0_96, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_93, c_0_47])).
% 0.12/0.40  cnf(c_0_97, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_94, c_0_95]), c_0_63]), c_0_95]), c_0_95]), c_0_96]), ['proof']).
% 0.12/0.40  # SZS output end CNFRefutation
% 0.12/0.40  # Proof object total steps             : 98
% 0.12/0.40  # Proof object clause steps            : 59
% 0.12/0.40  # Proof object formula steps           : 39
% 0.12/0.40  # Proof object conjectures             : 27
% 0.12/0.40  # Proof object clause conjectures      : 24
% 0.12/0.40  # Proof object formula conjectures     : 3
% 0.12/0.40  # Proof object initial clauses used    : 24
% 0.12/0.40  # Proof object initial formulas used   : 19
% 0.12/0.40  # Proof object generating inferences   : 22
% 0.12/0.40  # Proof object simplifying inferences  : 44
% 0.12/0.40  # Training examples: 0 positive, 0 negative
% 0.12/0.40  # Parsed axioms                        : 25
% 0.12/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.40  # Initial clauses                      : 45
% 0.12/0.40  # Removed in clause preprocessing      : 3
% 0.12/0.40  # Initial clauses in saturation        : 42
% 0.12/0.40  # Processed clauses                    : 412
% 0.12/0.40  # ...of these trivial                  : 23
% 0.12/0.40  # ...subsumed                          : 159
% 0.12/0.40  # ...remaining for further processing  : 230
% 0.12/0.40  # Other redundant clauses eliminated   : 16
% 0.12/0.40  # Clauses deleted for lack of memory   : 0
% 0.12/0.40  # Backward-subsumed                    : 1
% 0.12/0.40  # Backward-rewritten                   : 94
% 0.12/0.40  # Generated clauses                    : 2217
% 0.12/0.40  # ...of the previous two non-trivial   : 1564
% 0.12/0.40  # Contextual simplify-reflections      : 4
% 0.12/0.40  # Paramodulations                      : 2200
% 0.12/0.40  # Factorizations                       : 0
% 0.12/0.40  # Equation resolutions                 : 17
% 0.12/0.40  # Propositional unsat checks           : 0
% 0.12/0.40  #    Propositional check models        : 0
% 0.12/0.40  #    Propositional check unsatisfiable : 0
% 0.12/0.40  #    Propositional clauses             : 0
% 0.12/0.40  #    Propositional clauses after purity: 0
% 0.12/0.40  #    Propositional unsat core size     : 0
% 0.12/0.40  #    Propositional preprocessing time  : 0.000
% 0.12/0.40  #    Propositional encoding time       : 0.000
% 0.12/0.40  #    Propositional solver time         : 0.000
% 0.12/0.40  #    Success case prop preproc time    : 0.000
% 0.12/0.40  #    Success case prop encoding time   : 0.000
% 0.12/0.40  #    Success case prop solver time     : 0.000
% 0.12/0.40  # Current number of processed clauses  : 91
% 0.12/0.40  #    Positive orientable unit clauses  : 26
% 0.12/0.40  #    Positive unorientable unit clauses: 0
% 0.12/0.40  #    Negative unit clauses             : 3
% 0.12/0.40  #    Non-unit-clauses                  : 62
% 0.12/0.40  # Current number of unprocessed clauses: 1197
% 0.12/0.40  # ...number of literals in the above   : 2746
% 0.12/0.40  # Current number of archived formulas  : 0
% 0.12/0.40  # Current number of archived clauses   : 131
% 0.12/0.40  # Clause-clause subsumption calls (NU) : 1402
% 0.12/0.40  # Rec. Clause-clause subsumption calls : 1151
% 0.12/0.40  # Non-unit clause-clause subsumptions  : 91
% 0.12/0.40  # Unit Clause-clause subsumption calls : 181
% 0.12/0.40  # Rewrite failures with RHS unbound    : 0
% 0.12/0.40  # BW rewrite match attempts            : 38
% 0.12/0.40  # BW rewrite match successes           : 16
% 0.12/0.40  # Condensation attempts                : 0
% 0.12/0.40  # Condensation successes               : 0
% 0.12/0.40  # Termbank termtop insertions          : 26233
% 0.12/0.40  
% 0.12/0.40  # -------------------------------------------------
% 0.12/0.40  # User time                : 0.058 s
% 0.12/0.40  # System time              : 0.004 s
% 0.12/0.40  # Total time               : 0.062 s
% 0.12/0.40  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
