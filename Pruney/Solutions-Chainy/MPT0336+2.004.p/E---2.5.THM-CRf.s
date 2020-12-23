%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:44:48 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 177 expanded)
%              Number of clauses        :   43 (  72 expanded)
%              Number of leaves         :   17 (  50 expanded)
%              Depth                    :   10
%              Number of atoms          :  198 ( 340 expanded)
%              Number of equality atoms :   99 ( 183 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   25 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t149_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))
        & r2_hidden(X4,X3)
        & r1_xboole_0(X3,X2) )
     => r1_xboole_0(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t77_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( ~ r1_xboole_0(X1,X2)
        & r1_tarski(X1,X3)
        & r1_xboole_0(X1,k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(t142_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r1_tarski(X4,k1_enumset1(X1,X2,X3))
    <=> ~ ( X4 != k1_xboole_0
          & X4 != k1_tarski(X1)
          & X4 != k1_tarski(X2)
          & X4 != k1_tarski(X3)
          & X4 != k2_tarski(X1,X2)
          & X4 != k2_tarski(X2,X3)
          & X4 != k2_tarski(X1,X3)
          & X4 != k1_enumset1(X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_zfmisc_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(t78_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_xboole_0(X1,X2)
     => k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k3_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_xboole_1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

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

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))
          & r2_hidden(X4,X3)
          & r1_xboole_0(X3,X2) )
       => r1_xboole_0(k2_xboole_0(X1,X3),X2) ) ),
    inference(assume_negation,[status(cth)],[t149_zfmisc_1])).

fof(c_0_18,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk3_0,esk4_0),k1_tarski(esk6_0))
    & r2_hidden(esk6_0,esk5_0)
    & r1_xboole_0(esk5_0,esk4_0)
    & ~ r1_xboole_0(k2_xboole_0(esk3_0,esk5_0),esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

fof(c_0_19,plain,(
    ! [X41] : k2_tarski(X41,X41) = k1_tarski(X41) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_20,plain,(
    ! [X42,X43] : k1_enumset1(X42,X42,X43) = k2_tarski(X42,X43) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_21,plain,(
    ! [X44,X45,X46] : k2_enumset1(X44,X44,X45,X46) = k1_enumset1(X44,X45,X46) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_22,plain,(
    ! [X24,X25,X26] :
      ( r1_xboole_0(X24,X25)
      | ~ r1_tarski(X24,X26)
      | ~ r1_xboole_0(X24,k3_xboole_0(X25,X26)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t77_xboole_1])])])).

fof(c_0_23,plain,(
    ! [X21,X22] : r1_tarski(k3_xboole_0(X21,X22),X21) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

fof(c_0_24,plain,(
    ! [X9,X10] :
      ( ( ~ r1_xboole_0(X9,X10)
        | k3_xboole_0(X9,X10) = k1_xboole_0 )
      & ( k3_xboole_0(X9,X10) != k1_xboole_0
        | r1_xboole_0(X9,X10) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

fof(c_0_25,plain,(
    ! [X32,X33,X34,X35,X36,X37,X38,X39] :
      ( ( ~ r2_hidden(X35,X34)
        | X35 = X32
        | X35 = X33
        | X34 != k2_tarski(X32,X33) )
      & ( X36 != X32
        | r2_hidden(X36,X34)
        | X34 != k2_tarski(X32,X33) )
      & ( X36 != X33
        | r2_hidden(X36,X34)
        | X34 != k2_tarski(X32,X33) )
      & ( esk2_3(X37,X38,X39) != X37
        | ~ r2_hidden(esk2_3(X37,X38,X39),X39)
        | X39 = k2_tarski(X37,X38) )
      & ( esk2_3(X37,X38,X39) != X38
        | ~ r2_hidden(esk2_3(X37,X38,X39),X39)
        | X39 = k2_tarski(X37,X38) )
      & ( r2_hidden(esk2_3(X37,X38,X39),X39)
        | esk2_3(X37,X38,X39) = X37
        | esk2_3(X37,X38,X39) = X38
        | X39 = k2_tarski(X37,X38) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

fof(c_0_26,plain,(
    ! [X47,X48,X49,X50] :
      ( ( ~ r1_tarski(X50,k1_enumset1(X47,X48,X49))
        | X50 = k1_xboole_0
        | X50 = k1_tarski(X47)
        | X50 = k1_tarski(X48)
        | X50 = k1_tarski(X49)
        | X50 = k2_tarski(X47,X48)
        | X50 = k2_tarski(X48,X49)
        | X50 = k2_tarski(X47,X49)
        | X50 = k1_enumset1(X47,X48,X49) )
      & ( X50 != k1_xboole_0
        | r1_tarski(X50,k1_enumset1(X47,X48,X49)) )
      & ( X50 != k1_tarski(X47)
        | r1_tarski(X50,k1_enumset1(X47,X48,X49)) )
      & ( X50 != k1_tarski(X48)
        | r1_tarski(X50,k1_enumset1(X47,X48,X49)) )
      & ( X50 != k1_tarski(X49)
        | r1_tarski(X50,k1_enumset1(X47,X48,X49)) )
      & ( X50 != k2_tarski(X47,X48)
        | r1_tarski(X50,k1_enumset1(X47,X48,X49)) )
      & ( X50 != k2_tarski(X48,X49)
        | r1_tarski(X50,k1_enumset1(X47,X48,X49)) )
      & ( X50 != k2_tarski(X47,X49)
        | r1_tarski(X50,k1_enumset1(X47,X48,X49)) )
      & ( X50 != k1_enumset1(X47,X48,X49)
        | r1_tarski(X50,k1_enumset1(X47,X48,X49)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t142_zfmisc_1])])])).

cnf(c_0_27,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk3_0,esk4_0),k1_tarski(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_31,plain,(
    ! [X7,X8] : k3_xboole_0(X7,X8) = k3_xboole_0(X8,X7) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_32,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X3)
    | ~ r1_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_35,negated_conjecture,
    ( r1_xboole_0(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_36,plain,(
    ! [X23] : r1_xboole_0(X23,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

fof(c_0_37,plain,(
    ! [X27,X28,X29] :
      ( ~ r1_xboole_0(X27,X28)
      | k3_xboole_0(X27,k2_xboole_0(X28,X29)) = k3_xboole_0(X27,X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t78_xboole_1])])).

fof(c_0_38,plain,(
    ! [X30,X31] : k2_xboole_0(X30,X31) = k5_xboole_0(X30,k4_xboole_0(X31,X30)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_39,plain,(
    ! [X19,X20] : k4_xboole_0(X19,X20) = k5_xboole_0(X19,k3_xboole_0(X19,X20)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_40,plain,(
    ! [X11,X12] :
      ( ~ r1_xboole_0(X11,X12)
      | r1_xboole_0(X12,X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_42,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_tarski(X2)
    | X1 = k1_tarski(X3)
    | X1 = k1_tarski(X4)
    | X1 = k2_tarski(X2,X3)
    | X1 = k2_tarski(X3,X4)
    | X1 = k2_tarski(X2,X4)
    | X1 = k1_enumset1(X2,X3,X4)
    | ~ r1_tarski(X1,k1_enumset1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk3_0,esk4_0),k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_28]),c_0_29]),c_0_30])).

cnf(c_0_44,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_45,plain,(
    ! [X13,X14,X16,X17,X18] :
      ( ( r2_hidden(esk1_2(X13,X14),X13)
        | r1_xboole_0(X13,X14) )
      & ( r2_hidden(esk1_2(X13,X14),X14)
        | r1_xboole_0(X13,X14) )
      & ( ~ r2_hidden(X18,X16)
        | ~ r2_hidden(X18,X17)
        | ~ r1_xboole_0(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_46,plain,
    ( r1_xboole_0(k3_xboole_0(X1,X2),X3)
    | ~ r1_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X1)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_47,negated_conjecture,
    ( k3_xboole_0(esk5_0,esk4_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_48,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_49,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k3_xboole_0(X1,X3)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_50,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_51,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_52,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_53,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X2,X2,X2,X4) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_29]),c_0_30])).

cnf(c_0_54,plain,
    ( X1 = k1_xboole_0
    | X1 = k2_enumset1(X4,X4,X4,X4)
    | X1 = k2_enumset1(X3,X3,X3,X4)
    | X1 = k2_enumset1(X3,X3,X3,X3)
    | X1 = k2_enumset1(X2,X2,X3,X4)
    | X1 = k2_enumset1(X2,X2,X2,X4)
    | X1 = k2_enumset1(X2,X2,X2,X3)
    | X1 = k2_enumset1(X2,X2,X2,X2)
    | ~ r1_tarski(X1,k2_enumset1(X2,X2,X3,X4)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_28]),c_0_28]),c_0_28]),c_0_29]),c_0_29]),c_0_29]),c_0_29]),c_0_29]),c_0_29]),c_0_30]),c_0_30]),c_0_30]),c_0_30]),c_0_30]),c_0_30]),c_0_30]),c_0_30])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk4_0,esk3_0),k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)) ),
    inference(rw,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_56,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_57,negated_conjecture,
    ( r1_xboole_0(k3_xboole_0(esk4_0,X1),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48])])).

cnf(c_0_58,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2)))) = k3_xboole_0(X1,X3)
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_50]),c_0_51])).

cnf(c_0_59,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_35])).

cnf(c_0_60,plain,
    ( r2_hidden(X1,k2_enumset1(X1,X1,X1,X2)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_53])])).

cnf(c_0_61,negated_conjecture,
    ( k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0) = k3_xboole_0(esk4_0,esk3_0)
    | k3_xboole_0(esk4_0,esk3_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_62,negated_conjecture,
    ( ~ r2_hidden(X1,k3_xboole_0(esk4_0,X2))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_64,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_65,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_66,negated_conjecture,
    ( k3_xboole_0(esk4_0,k5_xboole_0(esk5_0,k5_xboole_0(X1,k3_xboole_0(X1,esk5_0)))) = k3_xboole_0(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_67,negated_conjecture,
    ( k3_xboole_0(esk4_0,esk3_0) = k1_xboole_0
    | r2_hidden(esk6_0,k3_xboole_0(esk4_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_68,negated_conjecture,
    ( ~ r2_hidden(esk6_0,k3_xboole_0(esk4_0,X1)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_69,negated_conjecture,
    ( ~ r1_xboole_0(k2_xboole_0(esk3_0,esk5_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_70,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_71,negated_conjecture,
    ( r1_xboole_0(esk4_0,k5_xboole_0(esk5_0,k5_xboole_0(X1,k3_xboole_0(X1,esk5_0))))
    | k3_xboole_0(esk4_0,X1) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_72,negated_conjecture,
    ( k3_xboole_0(esk4_0,esk3_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_73,negated_conjecture,
    ( ~ r1_xboole_0(k5_xboole_0(esk3_0,k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,esk3_0))),esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_50]),c_0_51])).

cnf(c_0_74,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_50]),c_0_50]),c_0_51]),c_0_51])).

cnf(c_0_75,negated_conjecture,
    ( r1_xboole_0(esk4_0,k5_xboole_0(esk5_0,k5_xboole_0(esk3_0,k3_xboole_0(esk5_0,esk3_0)))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_44])).

cnf(c_0_76,negated_conjecture,
    ( ~ r1_xboole_0(k5_xboole_0(esk5_0,k5_xboole_0(esk3_0,k3_xboole_0(esk5_0,esk3_0))),esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_74]),c_0_44])).

cnf(c_0_77,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_75]),c_0_76]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:42:10 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.54  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_S2mI
% 0.19/0.54  # and selection function SelectCQArNTNpEqFirst.
% 0.19/0.54  #
% 0.19/0.54  # Preprocessing time       : 0.028 s
% 0.19/0.54  # Presaturation interreduction done
% 0.19/0.54  
% 0.19/0.54  # Proof found!
% 0.19/0.54  # SZS status Theorem
% 0.19/0.54  # SZS output start CNFRefutation
% 0.19/0.54  fof(t149_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(((r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))&r2_hidden(X4,X3))&r1_xboole_0(X3,X2))=>r1_xboole_0(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 0.19/0.54  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.54  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.54  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.54  fof(t77_xboole_1, axiom, ![X1, X2, X3]:~(((~(r1_xboole_0(X1,X2))&r1_tarski(X1,X3))&r1_xboole_0(X1,k3_xboole_0(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_xboole_1)).
% 0.19/0.54  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.19/0.54  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.19/0.54  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 0.19/0.54  fof(t142_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r1_tarski(X4,k1_enumset1(X1,X2,X3))<=>~((((((((X4!=k1_xboole_0&X4!=k1_tarski(X1))&X4!=k1_tarski(X2))&X4!=k1_tarski(X3))&X4!=k2_tarski(X1,X2))&X4!=k2_tarski(X2,X3))&X4!=k2_tarski(X1,X3))&X4!=k1_enumset1(X1,X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_zfmisc_1)).
% 0.19/0.54  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.19/0.54  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.19/0.54  fof(t78_xboole_1, axiom, ![X1, X2, X3]:(r1_xboole_0(X1,X2)=>k3_xboole_0(X1,k2_xboole_0(X2,X3))=k3_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_xboole_1)).
% 0.19/0.54  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.19/0.54  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.19/0.54  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.19/0.54  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.19/0.54  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.19/0.54  fof(c_0_17, negated_conjecture, ~(![X1, X2, X3, X4]:(((r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))&r2_hidden(X4,X3))&r1_xboole_0(X3,X2))=>r1_xboole_0(k2_xboole_0(X1,X3),X2))), inference(assume_negation,[status(cth)],[t149_zfmisc_1])).
% 0.19/0.54  fof(c_0_18, negated_conjecture, (((r1_tarski(k3_xboole_0(esk3_0,esk4_0),k1_tarski(esk6_0))&r2_hidden(esk6_0,esk5_0))&r1_xboole_0(esk5_0,esk4_0))&~r1_xboole_0(k2_xboole_0(esk3_0,esk5_0),esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).
% 0.19/0.54  fof(c_0_19, plain, ![X41]:k2_tarski(X41,X41)=k1_tarski(X41), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.54  fof(c_0_20, plain, ![X42, X43]:k1_enumset1(X42,X42,X43)=k2_tarski(X42,X43), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.54  fof(c_0_21, plain, ![X44, X45, X46]:k2_enumset1(X44,X44,X45,X46)=k1_enumset1(X44,X45,X46), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.19/0.54  fof(c_0_22, plain, ![X24, X25, X26]:(r1_xboole_0(X24,X25)|~r1_tarski(X24,X26)|~r1_xboole_0(X24,k3_xboole_0(X25,X26))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t77_xboole_1])])])).
% 0.19/0.54  fof(c_0_23, plain, ![X21, X22]:r1_tarski(k3_xboole_0(X21,X22),X21), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.19/0.54  fof(c_0_24, plain, ![X9, X10]:((~r1_xboole_0(X9,X10)|k3_xboole_0(X9,X10)=k1_xboole_0)&(k3_xboole_0(X9,X10)!=k1_xboole_0|r1_xboole_0(X9,X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.19/0.54  fof(c_0_25, plain, ![X32, X33, X34, X35, X36, X37, X38, X39]:(((~r2_hidden(X35,X34)|(X35=X32|X35=X33)|X34!=k2_tarski(X32,X33))&((X36!=X32|r2_hidden(X36,X34)|X34!=k2_tarski(X32,X33))&(X36!=X33|r2_hidden(X36,X34)|X34!=k2_tarski(X32,X33))))&(((esk2_3(X37,X38,X39)!=X37|~r2_hidden(esk2_3(X37,X38,X39),X39)|X39=k2_tarski(X37,X38))&(esk2_3(X37,X38,X39)!=X38|~r2_hidden(esk2_3(X37,X38,X39),X39)|X39=k2_tarski(X37,X38)))&(r2_hidden(esk2_3(X37,X38,X39),X39)|(esk2_3(X37,X38,X39)=X37|esk2_3(X37,X38,X39)=X38)|X39=k2_tarski(X37,X38)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.19/0.54  fof(c_0_26, plain, ![X47, X48, X49, X50]:((~r1_tarski(X50,k1_enumset1(X47,X48,X49))|(X50=k1_xboole_0|X50=k1_tarski(X47)|X50=k1_tarski(X48)|X50=k1_tarski(X49)|X50=k2_tarski(X47,X48)|X50=k2_tarski(X48,X49)|X50=k2_tarski(X47,X49)|X50=k1_enumset1(X47,X48,X49)))&((((((((X50!=k1_xboole_0|r1_tarski(X50,k1_enumset1(X47,X48,X49)))&(X50!=k1_tarski(X47)|r1_tarski(X50,k1_enumset1(X47,X48,X49))))&(X50!=k1_tarski(X48)|r1_tarski(X50,k1_enumset1(X47,X48,X49))))&(X50!=k1_tarski(X49)|r1_tarski(X50,k1_enumset1(X47,X48,X49))))&(X50!=k2_tarski(X47,X48)|r1_tarski(X50,k1_enumset1(X47,X48,X49))))&(X50!=k2_tarski(X48,X49)|r1_tarski(X50,k1_enumset1(X47,X48,X49))))&(X50!=k2_tarski(X47,X49)|r1_tarski(X50,k1_enumset1(X47,X48,X49))))&(X50!=k1_enumset1(X47,X48,X49)|r1_tarski(X50,k1_enumset1(X47,X48,X49))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t142_zfmisc_1])])])).
% 0.19/0.54  cnf(c_0_27, negated_conjecture, (r1_tarski(k3_xboole_0(esk3_0,esk4_0),k1_tarski(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.54  cnf(c_0_28, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.54  cnf(c_0_29, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.54  cnf(c_0_30, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.54  fof(c_0_31, plain, ![X7, X8]:k3_xboole_0(X7,X8)=k3_xboole_0(X8,X7), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.19/0.54  cnf(c_0_32, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X1,X3)|~r1_xboole_0(X1,k3_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.54  cnf(c_0_33, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.54  cnf(c_0_34, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.54  cnf(c_0_35, negated_conjecture, (r1_xboole_0(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.54  fof(c_0_36, plain, ![X23]:r1_xboole_0(X23,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.19/0.54  fof(c_0_37, plain, ![X27, X28, X29]:(~r1_xboole_0(X27,X28)|k3_xboole_0(X27,k2_xboole_0(X28,X29))=k3_xboole_0(X27,X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t78_xboole_1])])).
% 0.19/0.54  fof(c_0_38, plain, ![X30, X31]:k2_xboole_0(X30,X31)=k5_xboole_0(X30,k4_xboole_0(X31,X30)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.19/0.54  fof(c_0_39, plain, ![X19, X20]:k4_xboole_0(X19,X20)=k5_xboole_0(X19,k3_xboole_0(X19,X20)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.19/0.54  fof(c_0_40, plain, ![X11, X12]:(~r1_xboole_0(X11,X12)|r1_xboole_0(X12,X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.19/0.54  cnf(c_0_41, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.54  cnf(c_0_42, plain, (X1=k1_xboole_0|X1=k1_tarski(X2)|X1=k1_tarski(X3)|X1=k1_tarski(X4)|X1=k2_tarski(X2,X3)|X1=k2_tarski(X3,X4)|X1=k2_tarski(X2,X4)|X1=k1_enumset1(X2,X3,X4)|~r1_tarski(X1,k1_enumset1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.54  cnf(c_0_43, negated_conjecture, (r1_tarski(k3_xboole_0(esk3_0,esk4_0),k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_28]), c_0_29]), c_0_30])).
% 0.19/0.54  cnf(c_0_44, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.54  fof(c_0_45, plain, ![X13, X14, X16, X17, X18]:(((r2_hidden(esk1_2(X13,X14),X13)|r1_xboole_0(X13,X14))&(r2_hidden(esk1_2(X13,X14),X14)|r1_xboole_0(X13,X14)))&(~r2_hidden(X18,X16)|~r2_hidden(X18,X17)|~r1_xboole_0(X16,X17))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.19/0.54  cnf(c_0_46, plain, (r1_xboole_0(k3_xboole_0(X1,X2),X3)|~r1_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X1))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.19/0.54  cnf(c_0_47, negated_conjecture, (k3_xboole_0(esk5_0,esk4_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.19/0.54  cnf(c_0_48, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.54  cnf(c_0_49, plain, (k3_xboole_0(X1,k2_xboole_0(X2,X3))=k3_xboole_0(X1,X3)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.54  cnf(c_0_50, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.54  cnf(c_0_51, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.54  cnf(c_0_52, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.54  cnf(c_0_53, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X2,X2,X2,X4)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_29]), c_0_30])).
% 0.19/0.54  cnf(c_0_54, plain, (X1=k1_xboole_0|X1=k2_enumset1(X4,X4,X4,X4)|X1=k2_enumset1(X3,X3,X3,X4)|X1=k2_enumset1(X3,X3,X3,X3)|X1=k2_enumset1(X2,X2,X3,X4)|X1=k2_enumset1(X2,X2,X2,X4)|X1=k2_enumset1(X2,X2,X2,X3)|X1=k2_enumset1(X2,X2,X2,X2)|~r1_tarski(X1,k2_enumset1(X2,X2,X3,X4))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_28]), c_0_28]), c_0_28]), c_0_29]), c_0_29]), c_0_29]), c_0_29]), c_0_29]), c_0_29]), c_0_30]), c_0_30]), c_0_30]), c_0_30]), c_0_30]), c_0_30]), c_0_30]), c_0_30])).
% 0.19/0.54  cnf(c_0_55, negated_conjecture, (r1_tarski(k3_xboole_0(esk4_0,esk3_0),k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0))), inference(rw,[status(thm)],[c_0_43, c_0_44])).
% 0.19/0.54  cnf(c_0_56, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.19/0.54  cnf(c_0_57, negated_conjecture, (r1_xboole_0(k3_xboole_0(esk4_0,X1),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48])])).
% 0.19/0.54  cnf(c_0_58, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))))=k3_xboole_0(X1,X3)|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_50]), c_0_51])).
% 0.19/0.54  cnf(c_0_59, negated_conjecture, (r1_xboole_0(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_52, c_0_35])).
% 0.19/0.54  cnf(c_0_60, plain, (r2_hidden(X1,k2_enumset1(X1,X1,X1,X2))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_53])])).
% 0.19/0.54  cnf(c_0_61, negated_conjecture, (k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)=k3_xboole_0(esk4_0,esk3_0)|k3_xboole_0(esk4_0,esk3_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.19/0.54  cnf(c_0_62, negated_conjecture, (~r2_hidden(X1,k3_xboole_0(esk4_0,X2))|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.19/0.54  cnf(c_0_63, negated_conjecture, (r2_hidden(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.54  fof(c_0_64, plain, ![X5, X6]:k2_xboole_0(X5,X6)=k2_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.19/0.54  cnf(c_0_65, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.54  cnf(c_0_66, negated_conjecture, (k3_xboole_0(esk4_0,k5_xboole_0(esk5_0,k5_xboole_0(X1,k3_xboole_0(X1,esk5_0))))=k3_xboole_0(esk4_0,X1)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.19/0.54  cnf(c_0_67, negated_conjecture, (k3_xboole_0(esk4_0,esk3_0)=k1_xboole_0|r2_hidden(esk6_0,k3_xboole_0(esk4_0,esk3_0))), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.19/0.54  cnf(c_0_68, negated_conjecture, (~r2_hidden(esk6_0,k3_xboole_0(esk4_0,X1))), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.19/0.54  cnf(c_0_69, negated_conjecture, (~r1_xboole_0(k2_xboole_0(esk3_0,esk5_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.54  cnf(c_0_70, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.19/0.54  cnf(c_0_71, negated_conjecture, (r1_xboole_0(esk4_0,k5_xboole_0(esk5_0,k5_xboole_0(X1,k3_xboole_0(X1,esk5_0))))|k3_xboole_0(esk4_0,X1)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.19/0.54  cnf(c_0_72, negated_conjecture, (k3_xboole_0(esk4_0,esk3_0)=k1_xboole_0), inference(sr,[status(thm)],[c_0_67, c_0_68])).
% 0.19/0.54  cnf(c_0_73, negated_conjecture, (~r1_xboole_0(k5_xboole_0(esk3_0,k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,esk3_0))),esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69, c_0_50]), c_0_51])).
% 0.19/0.54  cnf(c_0_74, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))=k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_50]), c_0_50]), c_0_51]), c_0_51])).
% 0.19/0.54  cnf(c_0_75, negated_conjecture, (r1_xboole_0(esk4_0,k5_xboole_0(esk5_0,k5_xboole_0(esk3_0,k3_xboole_0(esk5_0,esk3_0))))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_44])).
% 0.19/0.54  cnf(c_0_76, negated_conjecture, (~r1_xboole_0(k5_xboole_0(esk5_0,k5_xboole_0(esk3_0,k3_xboole_0(esk5_0,esk3_0))),esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73, c_0_74]), c_0_44])).
% 0.19/0.54  cnf(c_0_77, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_75]), c_0_76]), ['proof']).
% 0.19/0.54  # SZS output end CNFRefutation
% 0.19/0.54  # Proof object total steps             : 78
% 0.19/0.54  # Proof object clause steps            : 43
% 0.19/0.54  # Proof object formula steps           : 35
% 0.19/0.54  # Proof object conjectures             : 23
% 0.19/0.54  # Proof object clause conjectures      : 20
% 0.19/0.54  # Proof object formula conjectures     : 3
% 0.19/0.54  # Proof object initial clauses used    : 21
% 0.19/0.54  # Proof object initial formulas used   : 17
% 0.19/0.54  # Proof object generating inferences   : 12
% 0.19/0.54  # Proof object simplifying inferences  : 40
% 0.19/0.54  # Training examples: 0 positive, 0 negative
% 0.19/0.54  # Parsed axioms                        : 17
% 0.19/0.54  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.54  # Initial clauses                      : 36
% 0.19/0.54  # Removed in clause preprocessing      : 5
% 0.19/0.54  # Initial clauses in saturation        : 31
% 0.19/0.54  # Processed clauses                    : 1112
% 0.19/0.54  # ...of these trivial                  : 175
% 0.19/0.54  # ...subsumed                          : 546
% 0.19/0.54  # ...remaining for further processing  : 391
% 0.19/0.54  # Other redundant clauses eliminated   : 39
% 0.19/0.54  # Clauses deleted for lack of memory   : 0
% 0.19/0.54  # Backward-subsumed                    : 4
% 0.19/0.54  # Backward-rewritten                   : 27
% 0.19/0.54  # Generated clauses                    : 7376
% 0.19/0.54  # ...of the previous two non-trivial   : 5109
% 0.19/0.54  # Contextual simplify-reflections      : 0
% 0.19/0.54  # Paramodulations                      : 7182
% 0.19/0.54  # Factorizations                       : 156
% 0.19/0.54  # Equation resolutions                 : 39
% 0.19/0.54  # Propositional unsat checks           : 0
% 0.19/0.54  #    Propositional check models        : 0
% 0.19/0.54  #    Propositional check unsatisfiable : 0
% 0.19/0.54  #    Propositional clauses             : 0
% 0.19/0.54  #    Propositional clauses after purity: 0
% 0.19/0.54  #    Propositional unsat core size     : 0
% 0.19/0.54  #    Propositional preprocessing time  : 0.000
% 0.19/0.54  #    Propositional encoding time       : 0.000
% 0.19/0.54  #    Propositional solver time         : 0.000
% 0.19/0.54  #    Success case prop preproc time    : 0.000
% 0.19/0.54  #    Success case prop encoding time   : 0.000
% 0.19/0.54  #    Success case prop solver time     : 0.000
% 0.19/0.54  # Current number of processed clauses  : 317
% 0.19/0.54  #    Positive orientable unit clauses  : 163
% 0.19/0.54  #    Positive unorientable unit clauses: 4
% 0.19/0.54  #    Negative unit clauses             : 13
% 0.19/0.54  #    Non-unit-clauses                  : 137
% 0.19/0.54  # Current number of unprocessed clauses: 4020
% 0.19/0.54  # ...number of literals in the above   : 25880
% 0.19/0.54  # Current number of archived formulas  : 0
% 0.19/0.54  # Current number of archived clauses   : 68
% 0.19/0.54  # Clause-clause subsumption calls (NU) : 3844
% 0.19/0.54  # Rec. Clause-clause subsumption calls : 3718
% 0.19/0.54  # Non-unit clause-clause subsumptions  : 263
% 0.19/0.54  # Unit Clause-clause subsumption calls : 462
% 0.19/0.54  # Rewrite failures with RHS unbound    : 0
% 0.19/0.54  # BW rewrite match attempts            : 170
% 0.19/0.54  # BW rewrite match successes           : 33
% 0.19/0.54  # Condensation attempts                : 0
% 0.19/0.54  # Condensation successes               : 0
% 0.19/0.54  # Termbank termtop insertions          : 128754
% 0.19/0.54  
% 0.19/0.54  # -------------------------------------------------
% 0.19/0.54  # User time                : 0.183 s
% 0.19/0.54  # System time              : 0.013 s
% 0.19/0.54  # Total time               : 0.196 s
% 0.19/0.54  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
