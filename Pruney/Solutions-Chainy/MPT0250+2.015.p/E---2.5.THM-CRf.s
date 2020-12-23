%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:40:09 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 325 expanded)
%              Number of clauses        :   47 ( 142 expanded)
%              Number of leaves         :   12 (  90 expanded)
%              Depth                    :   14
%              Number of atoms          :  177 ( 750 expanded)
%              Number of equality atoms :   71 ( 424 expanded)
%              Maximal formula depth    :   22 (   3 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t45_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( r1_tarski(k2_xboole_0(k1_tarski(X1),X2),X2)
     => r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_zfmisc_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t70_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ~ ( ~ r1_xboole_0(X1,k2_xboole_0(X2,X3))
          & r1_xboole_0(X1,X2)
          & r1_xboole_0(X1,X3) )
      & ~ ( ~ ( r1_xboole_0(X1,X2)
              & r1_xboole_0(X1,X3) )
          & r1_xboole_0(X1,k2_xboole_0(X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

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

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2] :
        ( r1_tarski(k2_xboole_0(k1_tarski(X1),X2),X2)
       => r2_hidden(X1,X2) ) ),
    inference(assume_negation,[status(cth)],[t45_zfmisc_1])).

fof(c_0_13,plain,(
    ! [X58,X59] : k3_tarski(k2_tarski(X58,X59)) = k2_xboole_0(X58,X59) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_14,plain,(
    ! [X49,X50] : k1_enumset1(X49,X49,X50) = k2_tarski(X49,X50) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_15,negated_conjecture,
    ( r1_tarski(k2_xboole_0(k1_tarski(esk4_0),esk5_0),esk5_0)
    & ~ r2_hidden(esk4_0,esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

fof(c_0_16,plain,(
    ! [X48] : k2_tarski(X48,X48) = k1_tarski(X48) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_17,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_19,plain,(
    ! [X51,X52,X53] : k2_enumset1(X51,X51,X52,X53) = k1_enumset1(X51,X52,X53) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_20,plain,(
    ! [X54,X55,X56,X57] : k3_enumset1(X54,X54,X55,X56,X57) = k2_enumset1(X54,X55,X56,X57) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_21,plain,(
    ! [X35,X36] : k2_tarski(X35,X36) = k2_tarski(X36,X35) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_22,negated_conjecture,
    ( r1_tarski(k2_xboole_0(k1_tarski(esk4_0),esk5_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_25,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_28,plain,(
    ! [X24,X25] :
      ( ( r1_tarski(X24,X25)
        | X24 != X25 )
      & ( r1_tarski(X25,X24)
        | X24 != X25 )
      & ( ~ r1_tarski(X24,X25)
        | ~ r1_tarski(X25,X24)
        | X24 = X25 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_29,negated_conjecture,
    ( r1_tarski(k3_tarski(k3_enumset1(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),esk5_0)),esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_23]),c_0_18]),c_0_24]),c_0_25]),c_0_25]),c_0_25]),c_0_26]),c_0_26]),c_0_26]),c_0_26])).

cnf(c_0_30,plain,
    ( k3_enumset1(X1,X1,X1,X1,X2) = k3_enumset1(X2,X2,X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_18]),c_0_18]),c_0_25]),c_0_25]),c_0_26]),c_0_26])).

fof(c_0_31,plain,(
    ! [X33,X34] : r1_tarski(X33,k2_xboole_0(X33,X34)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_32,plain,(
    ! [X28,X29,X30] :
      ( ( r1_xboole_0(X28,k2_xboole_0(X29,X30))
        | ~ r1_xboole_0(X28,X29)
        | ~ r1_xboole_0(X28,X30) )
      & ( r1_xboole_0(X28,X29)
        | ~ r1_xboole_0(X28,k2_xboole_0(X29,X30)) )
      & ( r1_xboole_0(X28,X30)
        | ~ r1_xboole_0(X28,k2_xboole_0(X29,X30)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).

cnf(c_0_33,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(k3_tarski(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))),esk5_0) ),
    inference(rw,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_36,plain,(
    ! [X37,X38,X39,X40,X41,X42,X43,X44,X45,X46] :
      ( ( ~ r2_hidden(X41,X40)
        | X41 = X37
        | X41 = X38
        | X41 = X39
        | X40 != k1_enumset1(X37,X38,X39) )
      & ( X42 != X37
        | r2_hidden(X42,X40)
        | X40 != k1_enumset1(X37,X38,X39) )
      & ( X42 != X38
        | r2_hidden(X42,X40)
        | X40 != k1_enumset1(X37,X38,X39) )
      & ( X42 != X39
        | r2_hidden(X42,X40)
        | X40 != k1_enumset1(X37,X38,X39) )
      & ( esk3_4(X43,X44,X45,X46) != X43
        | ~ r2_hidden(esk3_4(X43,X44,X45,X46),X46)
        | X46 = k1_enumset1(X43,X44,X45) )
      & ( esk3_4(X43,X44,X45,X46) != X44
        | ~ r2_hidden(esk3_4(X43,X44,X45,X46),X46)
        | X46 = k1_enumset1(X43,X44,X45) )
      & ( esk3_4(X43,X44,X45,X46) != X45
        | ~ r2_hidden(esk3_4(X43,X44,X45,X46),X46)
        | X46 = k1_enumset1(X43,X44,X45) )
      & ( r2_hidden(esk3_4(X43,X44,X45,X46),X46)
        | esk3_4(X43,X44,X45,X46) = X43
        | esk3_4(X43,X44,X45,X46) = X44
        | esk3_4(X43,X44,X45,X46) = X45
        | X46 = k1_enumset1(X43,X44,X45) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

cnf(c_0_37,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,k2_xboole_0(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_38,negated_conjecture,
    ( k3_tarski(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))) = esk5_0
    | ~ r1_tarski(esk5_0,k3_tarski(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_24]),c_0_25]),c_0_26])).

fof(c_0_40,plain,(
    ! [X18,X19,X21,X22,X23] :
      ( ( r2_hidden(esk2_2(X18,X19),X18)
        | r1_xboole_0(X18,X19) )
      & ( r2_hidden(esk2_2(X18,X19),X19)
        | r1_xboole_0(X18,X19) )
      & ( ~ r2_hidden(X23,X21)
        | ~ r2_hidden(X23,X22)
        | ~ r1_xboole_0(X21,X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X2,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_42,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,k3_tarski(k3_enumset1(X3,X3,X3,X3,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_24]),c_0_25]),c_0_26])).

cnf(c_0_43,negated_conjecture,
    ( k3_tarski(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_39])])).

cnf(c_0_44,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_45,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k3_enumset1(X2,X2,X2,X4,X5) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_25]),c_0_26])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X5,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_48,negated_conjecture,
    ( r1_xboole_0(X1,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))
    | ~ r1_xboole_0(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_49,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_50,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_51,plain,
    ( r2_hidden(X1,k3_enumset1(X1,X1,X1,X2,X3)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_46])])).

cnf(c_0_52,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k3_enumset1(X4,X4,X4,X5,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_25]),c_0_26])).

cnf(c_0_53,negated_conjecture,
    ( r1_xboole_0(X1,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))
    | r2_hidden(esk2_2(X1,esk5_0),X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_54,plain,
    ( r2_hidden(esk2_2(k3_enumset1(X1,X1,X1,X2,X3),X4),X4)
    | ~ r2_hidden(X1,X4) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_55,plain,
    ( r2_hidden(X1,k3_enumset1(X2,X2,X2,X3,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_52])])).

cnf(c_0_56,negated_conjecture,
    ( r1_xboole_0(X1,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))
    | r2_hidden(esk2_2(X1,esk5_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_45])).

cnf(c_0_57,plain,
    ( X1 = X3
    | X1 = X4
    | X1 = X5
    | ~ r2_hidden(X1,X2)
    | X2 != k1_enumset1(X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(esk2_2(X1,esk5_0),X1)
    | ~ r2_hidden(X2,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_53])).

cnf(c_0_59,plain,
    ( r2_hidden(esk2_2(k3_enumset1(X1,X1,X1,X2,X3),k3_enumset1(X4,X4,X4,X5,X1)),k3_enumset1(X4,X4,X4,X5,X1)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_60,plain,
    ( r2_hidden(esk2_2(k3_enumset1(X1,X1,X1,X2,X3),X4),X4)
    | ~ r2_hidden(X3,X4) ),
    inference(spm,[status(thm)],[c_0_50,c_0_55])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(esk2_2(X1,esk5_0),esk5_0)
    | ~ r2_hidden(X2,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_56])).

cnf(c_0_62,plain,
    ( X1 = X5
    | X1 = X4
    | X1 = X3
    | X2 != k3_enumset1(X3,X3,X3,X4,X5)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_25]),c_0_26])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(esk2_2(X1,esk5_0),X1)
    | ~ r2_hidden(esk2_2(k3_enumset1(esk4_0,esk4_0,esk4_0,X2,X3),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)),X1) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_64,plain,
    ( r2_hidden(esk2_2(k3_enumset1(X1,X1,X1,X2,X3),k3_enumset1(X4,X4,X4,X5,X3)),k3_enumset1(X4,X4,X4,X5,X3)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_55])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(esk2_2(X1,esk5_0),esk5_0)
    | ~ r2_hidden(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_61,c_0_55])).

cnf(c_0_66,plain,
    ( X1 = X2
    | X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,k3_enumset1(X4,X4,X4,X3,X2)) ),
    inference(er,[status(thm)],[c_0_62])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(esk2_2(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),esk5_0),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_68,negated_conjecture,
    ( r2_hidden(esk2_2(k3_enumset1(X1,X1,X1,X2,esk4_0),esk5_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_55])).

cnf(c_0_69,negated_conjecture,
    ( esk2_2(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),esk5_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_70,negated_conjecture,
    ( ~ r2_hidden(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_71,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_70]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:10:00 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.19/0.52  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.19/0.52  # and selection function SelectNegativeLiterals.
% 0.19/0.52  #
% 0.19/0.52  # Preprocessing time       : 0.028 s
% 0.19/0.52  # Presaturation interreduction done
% 0.19/0.52  
% 0.19/0.52  # Proof found!
% 0.19/0.52  # SZS status Theorem
% 0.19/0.52  # SZS output start CNFRefutation
% 0.19/0.52  fof(t45_zfmisc_1, conjecture, ![X1, X2]:(r1_tarski(k2_xboole_0(k1_tarski(X1),X2),X2)=>r2_hidden(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 0.19/0.52  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.19/0.52  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.52  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.52  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.52  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.19/0.52  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.19/0.52  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.52  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.19/0.52  fof(t70_xboole_1, axiom, ![X1, X2, X3]:(~(((~(r1_xboole_0(X1,k2_xboole_0(X2,X3)))&r1_xboole_0(X1,X2))&r1_xboole_0(X1,X3)))&~((~((r1_xboole_0(X1,X2)&r1_xboole_0(X1,X3)))&r1_xboole_0(X1,k2_xboole_0(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 0.19/0.52  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 0.19/0.52  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.19/0.52  fof(c_0_12, negated_conjecture, ~(![X1, X2]:(r1_tarski(k2_xboole_0(k1_tarski(X1),X2),X2)=>r2_hidden(X1,X2))), inference(assume_negation,[status(cth)],[t45_zfmisc_1])).
% 0.19/0.52  fof(c_0_13, plain, ![X58, X59]:k3_tarski(k2_tarski(X58,X59))=k2_xboole_0(X58,X59), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.19/0.52  fof(c_0_14, plain, ![X49, X50]:k1_enumset1(X49,X49,X50)=k2_tarski(X49,X50), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.52  fof(c_0_15, negated_conjecture, (r1_tarski(k2_xboole_0(k1_tarski(esk4_0),esk5_0),esk5_0)&~r2_hidden(esk4_0,esk5_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 0.19/0.52  fof(c_0_16, plain, ![X48]:k2_tarski(X48,X48)=k1_tarski(X48), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.52  cnf(c_0_17, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.52  cnf(c_0_18, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.52  fof(c_0_19, plain, ![X51, X52, X53]:k2_enumset1(X51,X51,X52,X53)=k1_enumset1(X51,X52,X53), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.19/0.52  fof(c_0_20, plain, ![X54, X55, X56, X57]:k3_enumset1(X54,X54,X55,X56,X57)=k2_enumset1(X54,X55,X56,X57), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.19/0.52  fof(c_0_21, plain, ![X35, X36]:k2_tarski(X35,X36)=k2_tarski(X36,X35), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.19/0.52  cnf(c_0_22, negated_conjecture, (r1_tarski(k2_xboole_0(k1_tarski(esk4_0),esk5_0),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.52  cnf(c_0_23, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.52  cnf(c_0_24, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 0.19/0.52  cnf(c_0_25, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.52  cnf(c_0_26, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.52  cnf(c_0_27, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.52  fof(c_0_28, plain, ![X24, X25]:(((r1_tarski(X24,X25)|X24!=X25)&(r1_tarski(X25,X24)|X24!=X25))&(~r1_tarski(X24,X25)|~r1_tarski(X25,X24)|X24=X25)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.52  cnf(c_0_29, negated_conjecture, (r1_tarski(k3_tarski(k3_enumset1(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),esk5_0)),esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_23]), c_0_18]), c_0_24]), c_0_25]), c_0_25]), c_0_25]), c_0_26]), c_0_26]), c_0_26]), c_0_26])).
% 0.19/0.52  cnf(c_0_30, plain, (k3_enumset1(X1,X1,X1,X1,X2)=k3_enumset1(X2,X2,X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_18]), c_0_18]), c_0_25]), c_0_25]), c_0_26]), c_0_26])).
% 0.19/0.52  fof(c_0_31, plain, ![X33, X34]:r1_tarski(X33,k2_xboole_0(X33,X34)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.19/0.52  fof(c_0_32, plain, ![X28, X29, X30]:((r1_xboole_0(X28,k2_xboole_0(X29,X30))|~r1_xboole_0(X28,X29)|~r1_xboole_0(X28,X30))&((r1_xboole_0(X28,X29)|~r1_xboole_0(X28,k2_xboole_0(X29,X30)))&(r1_xboole_0(X28,X30)|~r1_xboole_0(X28,k2_xboole_0(X29,X30))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).
% 0.19/0.52  cnf(c_0_33, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.52  cnf(c_0_34, negated_conjecture, (r1_tarski(k3_tarski(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))),esk5_0)), inference(rw,[status(thm)],[c_0_29, c_0_30])).
% 0.19/0.52  cnf(c_0_35, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.52  fof(c_0_36, plain, ![X37, X38, X39, X40, X41, X42, X43, X44, X45, X46]:(((~r2_hidden(X41,X40)|(X41=X37|X41=X38|X41=X39)|X40!=k1_enumset1(X37,X38,X39))&(((X42!=X37|r2_hidden(X42,X40)|X40!=k1_enumset1(X37,X38,X39))&(X42!=X38|r2_hidden(X42,X40)|X40!=k1_enumset1(X37,X38,X39)))&(X42!=X39|r2_hidden(X42,X40)|X40!=k1_enumset1(X37,X38,X39))))&((((esk3_4(X43,X44,X45,X46)!=X43|~r2_hidden(esk3_4(X43,X44,X45,X46),X46)|X46=k1_enumset1(X43,X44,X45))&(esk3_4(X43,X44,X45,X46)!=X44|~r2_hidden(esk3_4(X43,X44,X45,X46),X46)|X46=k1_enumset1(X43,X44,X45)))&(esk3_4(X43,X44,X45,X46)!=X45|~r2_hidden(esk3_4(X43,X44,X45,X46),X46)|X46=k1_enumset1(X43,X44,X45)))&(r2_hidden(esk3_4(X43,X44,X45,X46),X46)|(esk3_4(X43,X44,X45,X46)=X43|esk3_4(X43,X44,X45,X46)=X44|esk3_4(X43,X44,X45,X46)=X45)|X46=k1_enumset1(X43,X44,X45)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 0.19/0.52  cnf(c_0_37, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X1,k2_xboole_0(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.52  cnf(c_0_38, negated_conjecture, (k3_tarski(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)))=esk5_0|~r1_tarski(esk5_0,k3_tarski(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.19/0.52  cnf(c_0_39, plain, (r1_tarski(X1,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_24]), c_0_25]), c_0_26])).
% 0.19/0.52  fof(c_0_40, plain, ![X18, X19, X21, X22, X23]:(((r2_hidden(esk2_2(X18,X19),X18)|r1_xboole_0(X18,X19))&(r2_hidden(esk2_2(X18,X19),X19)|r1_xboole_0(X18,X19)))&(~r2_hidden(X23,X21)|~r2_hidden(X23,X22)|~r1_xboole_0(X21,X22))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.19/0.52  cnf(c_0_41, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X2,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.52  cnf(c_0_42, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X1,k3_tarski(k3_enumset1(X3,X3,X3,X3,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_24]), c_0_25]), c_0_26])).
% 0.19/0.52  cnf(c_0_43, negated_conjecture, (k3_tarski(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)))=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_39])])).
% 0.19/0.52  cnf(c_0_44, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.52  cnf(c_0_45, plain, (r2_hidden(esk2_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.52  cnf(c_0_46, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k3_enumset1(X2,X2,X2,X4,X5)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_25]), c_0_26])).
% 0.19/0.52  cnf(c_0_47, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X5,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.52  cnf(c_0_48, negated_conjecture, (r1_xboole_0(X1,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))|~r1_xboole_0(X1,esk5_0)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.19/0.52  cnf(c_0_49, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.52  cnf(c_0_50, plain, (r2_hidden(esk2_2(X1,X2),X2)|~r2_hidden(X3,X2)|~r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.19/0.52  cnf(c_0_51, plain, (r2_hidden(X1,k3_enumset1(X1,X1,X1,X2,X3))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_46])])).
% 0.19/0.52  cnf(c_0_52, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k3_enumset1(X4,X4,X4,X5,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_25]), c_0_26])).
% 0.19/0.52  cnf(c_0_53, negated_conjecture, (r1_xboole_0(X1,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))|r2_hidden(esk2_2(X1,esk5_0),X1)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.19/0.52  cnf(c_0_54, plain, (r2_hidden(esk2_2(k3_enumset1(X1,X1,X1,X2,X3),X4),X4)|~r2_hidden(X1,X4)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.19/0.52  cnf(c_0_55, plain, (r2_hidden(X1,k3_enumset1(X2,X2,X2,X3,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_52])])).
% 0.19/0.52  cnf(c_0_56, negated_conjecture, (r1_xboole_0(X1,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))|r2_hidden(esk2_2(X1,esk5_0),esk5_0)), inference(spm,[status(thm)],[c_0_48, c_0_45])).
% 0.19/0.52  cnf(c_0_57, plain, (X1=X3|X1=X4|X1=X5|~r2_hidden(X1,X2)|X2!=k1_enumset1(X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.52  cnf(c_0_58, negated_conjecture, (r2_hidden(esk2_2(X1,esk5_0),X1)|~r2_hidden(X2,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_44, c_0_53])).
% 0.19/0.52  cnf(c_0_59, plain, (r2_hidden(esk2_2(k3_enumset1(X1,X1,X1,X2,X3),k3_enumset1(X4,X4,X4,X5,X1)),k3_enumset1(X4,X4,X4,X5,X1))), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.19/0.52  cnf(c_0_60, plain, (r2_hidden(esk2_2(k3_enumset1(X1,X1,X1,X2,X3),X4),X4)|~r2_hidden(X3,X4)), inference(spm,[status(thm)],[c_0_50, c_0_55])).
% 0.19/0.52  cnf(c_0_61, negated_conjecture, (r2_hidden(esk2_2(X1,esk5_0),esk5_0)|~r2_hidden(X2,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_44, c_0_56])).
% 0.19/0.52  cnf(c_0_62, plain, (X1=X5|X1=X4|X1=X3|X2!=k3_enumset1(X3,X3,X3,X4,X5)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_25]), c_0_26])).
% 0.19/0.52  cnf(c_0_63, negated_conjecture, (r2_hidden(esk2_2(X1,esk5_0),X1)|~r2_hidden(esk2_2(k3_enumset1(esk4_0,esk4_0,esk4_0,X2,X3),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)),X1)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.19/0.52  cnf(c_0_64, plain, (r2_hidden(esk2_2(k3_enumset1(X1,X1,X1,X2,X3),k3_enumset1(X4,X4,X4,X5,X3)),k3_enumset1(X4,X4,X4,X5,X3))), inference(spm,[status(thm)],[c_0_60, c_0_55])).
% 0.19/0.52  cnf(c_0_65, negated_conjecture, (r2_hidden(esk2_2(X1,esk5_0),esk5_0)|~r2_hidden(esk4_0,X1)), inference(spm,[status(thm)],[c_0_61, c_0_55])).
% 0.19/0.52  cnf(c_0_66, plain, (X1=X2|X1=X3|X1=X4|~r2_hidden(X1,k3_enumset1(X4,X4,X4,X3,X2))), inference(er,[status(thm)],[c_0_62])).
% 0.19/0.52  cnf(c_0_67, negated_conjecture, (r2_hidden(esk2_2(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),esk5_0),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.19/0.52  cnf(c_0_68, negated_conjecture, (r2_hidden(esk2_2(k3_enumset1(X1,X1,X1,X2,esk4_0),esk5_0),esk5_0)), inference(spm,[status(thm)],[c_0_65, c_0_55])).
% 0.19/0.52  cnf(c_0_69, negated_conjecture, (esk2_2(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),esk5_0)=esk4_0), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.19/0.52  cnf(c_0_70, negated_conjecture, (~r2_hidden(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.52  cnf(c_0_71, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_70]), ['proof']).
% 0.19/0.52  # SZS output end CNFRefutation
% 0.19/0.52  # Proof object total steps             : 72
% 0.19/0.52  # Proof object clause steps            : 47
% 0.19/0.52  # Proof object formula steps           : 25
% 0.19/0.52  # Proof object conjectures             : 20
% 0.19/0.52  # Proof object clause conjectures      : 17
% 0.19/0.52  # Proof object formula conjectures     : 3
% 0.19/0.52  # Proof object initial clauses used    : 17
% 0.19/0.52  # Proof object initial formulas used   : 12
% 0.19/0.52  # Proof object generating inferences   : 17
% 0.19/0.52  # Proof object simplifying inferences  : 38
% 0.19/0.52  # Training examples: 0 positive, 0 negative
% 0.19/0.52  # Parsed axioms                        : 16
% 0.19/0.52  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.52  # Initial clauses                      : 38
% 0.19/0.52  # Removed in clause preprocessing      : 6
% 0.19/0.52  # Initial clauses in saturation        : 32
% 0.19/0.52  # Processed clauses                    : 742
% 0.19/0.52  # ...of these trivial                  : 49
% 0.19/0.52  # ...subsumed                          : 207
% 0.19/0.52  # ...remaining for further processing  : 486
% 0.19/0.52  # Other redundant clauses eliminated   : 33
% 0.19/0.52  # Clauses deleted for lack of memory   : 0
% 0.19/0.52  # Backward-subsumed                    : 4
% 0.19/0.52  # Backward-rewritten                   : 15
% 0.19/0.52  # Generated clauses                    : 12482
% 0.19/0.52  # ...of the previous two non-trivial   : 11647
% 0.19/0.52  # Contextual simplify-reflections      : 0
% 0.19/0.52  # Paramodulations                      : 12446
% 0.19/0.52  # Factorizations                       : 6
% 0.19/0.52  # Equation resolutions                 : 33
% 0.19/0.52  # Propositional unsat checks           : 0
% 0.19/0.52  #    Propositional check models        : 0
% 0.19/0.52  #    Propositional check unsatisfiable : 0
% 0.19/0.52  #    Propositional clauses             : 0
% 0.19/0.52  #    Propositional clauses after purity: 0
% 0.19/0.52  #    Propositional unsat core size     : 0
% 0.19/0.52  #    Propositional preprocessing time  : 0.000
% 0.19/0.52  #    Propositional encoding time       : 0.000
% 0.19/0.52  #    Propositional solver time         : 0.000
% 0.19/0.52  #    Success case prop preproc time    : 0.000
% 0.19/0.52  #    Success case prop encoding time   : 0.000
% 0.19/0.52  #    Success case prop solver time     : 0.000
% 0.19/0.52  # Current number of processed clauses  : 427
% 0.19/0.52  #    Positive orientable unit clauses  : 124
% 0.19/0.52  #    Positive unorientable unit clauses: 1
% 0.19/0.52  #    Negative unit clauses             : 9
% 0.19/0.52  #    Non-unit-clauses                  : 293
% 0.19/0.52  # Current number of unprocessed clauses: 10954
% 0.19/0.52  # ...number of literals in the above   : 27158
% 0.19/0.52  # Current number of archived formulas  : 0
% 0.19/0.52  # Current number of archived clauses   : 56
% 0.19/0.52  # Clause-clause subsumption calls (NU) : 14606
% 0.19/0.52  # Rec. Clause-clause subsumption calls : 14393
% 0.19/0.52  # Non-unit clause-clause subsumptions  : 174
% 0.19/0.52  # Unit Clause-clause subsumption calls : 384
% 0.19/0.52  # Rewrite failures with RHS unbound    : 0
% 0.19/0.52  # BW rewrite match attempts            : 511
% 0.19/0.52  # BW rewrite match successes           : 34
% 0.19/0.52  # Condensation attempts                : 0
% 0.19/0.52  # Condensation successes               : 0
% 0.19/0.52  # Termbank termtop insertions          : 253019
% 0.19/0.52  
% 0.19/0.52  # -------------------------------------------------
% 0.19/0.52  # User time                : 0.179 s
% 0.19/0.52  # System time              : 0.011 s
% 0.19/0.52  # Total time               : 0.191 s
% 0.19/0.52  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
