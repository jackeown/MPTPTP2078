%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:44:52 EST 2020

% Result     : Theorem 0.61s
% Output     : CNFRefutation 0.61s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 181 expanded)
%              Number of clauses        :   40 (  82 expanded)
%              Number of leaves         :   12 (  44 expanded)
%              Depth                    :   13
%              Number of atoms          :  175 ( 530 expanded)
%              Number of equality atoms :   36 (  51 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t149_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))
        & r2_hidden(X4,X3)
        & r1_xboole_0(X3,X2) )
     => r1_xboole_0(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t70_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ~ ( ~ r1_xboole_0(X1,k2_xboole_0(X2,X3))
          & r1_xboole_0(X1,X2)
          & r1_xboole_0(X1,X3) )
      & ~ ( ~ ( r1_xboole_0(X1,X2)
              & r1_xboole_0(X1,X3) )
          & r1_xboole_0(X1,k2_xboole_0(X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

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

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

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

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))
          & r2_hidden(X4,X3)
          & r1_xboole_0(X3,X2) )
       => r1_xboole_0(k2_xboole_0(X1,X3),X2) ) ),
    inference(assume_negation,[status(cth)],[t149_zfmisc_1])).

fof(c_0_13,plain,(
    ! [X22,X23] :
      ( ~ r1_xboole_0(X22,X23)
      | r1_xboole_0(X23,X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

fof(c_0_14,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk6_0,esk7_0),k1_tarski(esk9_0))
    & r2_hidden(esk9_0,esk8_0)
    & r1_xboole_0(esk8_0,esk7_0)
    & ~ r1_xboole_0(k2_xboole_0(esk6_0,esk8_0),esk7_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

fof(c_0_15,plain,(
    ! [X36,X37,X38] :
      ( ( r1_xboole_0(X36,k2_xboole_0(X37,X38))
        | ~ r1_xboole_0(X36,X37)
        | ~ r1_xboole_0(X36,X38) )
      & ( r1_xboole_0(X36,X37)
        | ~ r1_xboole_0(X36,k2_xboole_0(X37,X38)) )
      & ( r1_xboole_0(X36,X38)
        | ~ r1_xboole_0(X36,k2_xboole_0(X37,X38)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).

cnf(c_0_16,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( r1_xboole_0(esk8_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( r1_xboole_0(X1,k2_xboole_0(X2,X3))
    | ~ r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( r1_xboole_0(esk7_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

fof(c_0_20,plain,(
    ! [X24,X25,X27,X28,X29] :
      ( ( r2_hidden(esk3_2(X24,X25),X24)
        | r1_xboole_0(X24,X25) )
      & ( r2_hidden(esk3_2(X24,X25),X25)
        | r1_xboole_0(X24,X25) )
      & ( ~ r2_hidden(X29,X27)
        | ~ r2_hidden(X29,X28)
        | ~ r1_xboole_0(X27,X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_21,negated_conjecture,
    ( r1_xboole_0(esk7_0,k2_xboole_0(X1,esk8_0))
    | ~ r1_xboole_0(esk7_0,X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_22,plain,
    ( r2_hidden(esk3_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_23,plain,(
    ! [X30,X31,X33,X34,X35] :
      ( ( r1_xboole_0(X30,X31)
        | r2_hidden(esk4_2(X30,X31),k3_xboole_0(X30,X31)) )
      & ( ~ r2_hidden(X35,k3_xboole_0(X33,X34))
        | ~ r1_xboole_0(X33,X34) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

cnf(c_0_24,negated_conjecture,
    ( r1_xboole_0(esk7_0,k2_xboole_0(X1,esk8_0))
    | r2_hidden(esk3_2(esk7_0,X1),esk7_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_25,plain,
    ( r2_hidden(esk3_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_26,plain,(
    ! [X46] : k2_tarski(X46,X46) = k1_tarski(X46) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_27,plain,(
    ! [X47,X48] : k1_enumset1(X47,X47,X48) = k2_tarski(X47,X48) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_28,plain,(
    ! [X49,X50,X51] : k2_enumset1(X49,X49,X50,X51) = k1_enumset1(X49,X50,X51) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

cnf(c_0_29,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk4_2(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,negated_conjecture,
    ( ~ r1_xboole_0(k2_xboole_0(esk6_0,esk8_0),esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_32,negated_conjecture,
    ( r1_xboole_0(k2_xboole_0(X1,esk8_0),esk7_0)
    | r2_hidden(esk3_2(esk7_0,X1),esk7_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_24])).

cnf(c_0_33,negated_conjecture,
    ( r1_xboole_0(esk7_0,k2_xboole_0(X1,esk8_0))
    | r2_hidden(esk3_2(esk7_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_25])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk6_0,esk7_0),k1_tarski(esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_35,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_38,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_39,plain,(
    ! [X13,X14,X15,X16,X17,X18,X19,X20] :
      ( ( r2_hidden(X16,X13)
        | ~ r2_hidden(X16,X15)
        | X15 != k3_xboole_0(X13,X14) )
      & ( r2_hidden(X16,X14)
        | ~ r2_hidden(X16,X15)
        | X15 != k3_xboole_0(X13,X14) )
      & ( ~ r2_hidden(X17,X13)
        | ~ r2_hidden(X17,X14)
        | r2_hidden(X17,X15)
        | X15 != k3_xboole_0(X13,X14) )
      & ( ~ r2_hidden(esk2_3(X18,X19,X20),X20)
        | ~ r2_hidden(esk2_3(X18,X19,X20),X18)
        | ~ r2_hidden(esk2_3(X18,X19,X20),X19)
        | X20 = k3_xboole_0(X18,X19) )
      & ( r2_hidden(esk2_3(X18,X19,X20),X18)
        | r2_hidden(esk2_3(X18,X19,X20),X20)
        | X20 = k3_xboole_0(X18,X19) )
      & ( r2_hidden(esk2_3(X18,X19,X20),X19)
        | r2_hidden(esk2_3(X18,X19,X20),X20)
        | X20 = k3_xboole_0(X18,X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_40,plain,
    ( r2_hidden(esk4_2(X1,X2),k3_xboole_0(X1,X2))
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk3_2(esk7_0,esk6_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_42,negated_conjecture,
    ( r1_xboole_0(k2_xboole_0(X1,esk8_0),esk7_0)
    | r2_hidden(esk3_2(esk7_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_33])).

fof(c_0_43,plain,(
    ! [X39,X40,X41,X42,X43,X44] :
      ( ( ~ r2_hidden(X41,X40)
        | X41 = X39
        | X40 != k1_tarski(X39) )
      & ( X42 != X39
        | r2_hidden(X42,X40)
        | X40 != k1_tarski(X39) )
      & ( ~ r2_hidden(esk5_2(X43,X44),X44)
        | esk5_2(X43,X44) != X43
        | X44 = k1_tarski(X43) )
      & ( r2_hidden(esk5_2(X43,X44),X44)
        | esk5_2(X43,X44) = X43
        | X44 = k1_tarski(X43) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_44,plain,(
    ! [X7,X8,X9,X10,X11] :
      ( ( ~ r1_tarski(X7,X8)
        | ~ r2_hidden(X9,X7)
        | r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_2(X10,X11),X10)
        | r1_tarski(X10,X11) )
      & ( ~ r2_hidden(esk1_2(X10,X11),X11)
        | r1_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk6_0,esk7_0),k2_enumset1(esk9_0,esk9_0,esk9_0,esk9_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_35]),c_0_36]),c_0_37])).

cnf(c_0_46,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk4_2(X1,esk7_0),k3_xboole_0(X1,esk7_0))
    | ~ r2_hidden(esk3_2(esk7_0,esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk3_2(esk7_0,esk6_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_42])).

cnf(c_0_50,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_51,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk7_0,esk6_0),k2_enumset1(esk9_0,esk9_0,esk9_0,esk9_0)) ),
    inference(rw,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_53,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_47])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk4_2(esk6_0,esk7_0),k3_xboole_0(esk7_0,esk6_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_46])).

cnf(c_0_55,plain,
    ( X1 = X3
    | X2 != k2_enumset1(X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_35]),c_0_36]),c_0_37])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(X1,k2_enumset1(esk9_0,esk9_0,esk9_0,esk9_0))
    | ~ r2_hidden(X1,k3_xboole_0(esk7_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_57,negated_conjecture,
    ( ~ r2_hidden(X1,esk7_0)
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_17])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(esk4_2(esk6_0,esk7_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_59,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k2_enumset1(X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_55])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(esk4_2(esk6_0,esk7_0),k2_enumset1(esk9_0,esk9_0,esk9_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_54])).

cnf(c_0_61,negated_conjecture,
    ( ~ r2_hidden(esk4_2(esk6_0,esk7_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_62,negated_conjecture,
    ( esk4_2(esk6_0,esk7_0) = esk9_0 ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(esk9_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_64,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_62]),c_0_63])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:51:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.61/0.79  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_S2mI
% 0.61/0.79  # and selection function SelectCQArNTNpEqFirst.
% 0.61/0.79  #
% 0.61/0.79  # Preprocessing time       : 0.030 s
% 0.61/0.79  # Presaturation interreduction done
% 0.61/0.79  
% 0.61/0.79  # Proof found!
% 0.61/0.79  # SZS status Theorem
% 0.61/0.79  # SZS output start CNFRefutation
% 0.61/0.79  fof(t149_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(((r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))&r2_hidden(X4,X3))&r1_xboole_0(X3,X2))=>r1_xboole_0(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 0.61/0.79  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.61/0.79  fof(t70_xboole_1, axiom, ![X1, X2, X3]:(~(((~(r1_xboole_0(X1,k2_xboole_0(X2,X3)))&r1_xboole_0(X1,X2))&r1_xboole_0(X1,X3)))&~((~((r1_xboole_0(X1,X2)&r1_xboole_0(X1,X3)))&r1_xboole_0(X1,k2_xboole_0(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 0.61/0.79  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.61/0.79  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.61/0.79  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.61/0.79  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.61/0.79  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.61/0.79  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.61/0.79  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.61/0.79  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 0.61/0.79  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.61/0.79  fof(c_0_12, negated_conjecture, ~(![X1, X2, X3, X4]:(((r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))&r2_hidden(X4,X3))&r1_xboole_0(X3,X2))=>r1_xboole_0(k2_xboole_0(X1,X3),X2))), inference(assume_negation,[status(cth)],[t149_zfmisc_1])).
% 0.61/0.79  fof(c_0_13, plain, ![X22, X23]:(~r1_xboole_0(X22,X23)|r1_xboole_0(X23,X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.61/0.79  fof(c_0_14, negated_conjecture, (((r1_tarski(k3_xboole_0(esk6_0,esk7_0),k1_tarski(esk9_0))&r2_hidden(esk9_0,esk8_0))&r1_xboole_0(esk8_0,esk7_0))&~r1_xboole_0(k2_xboole_0(esk6_0,esk8_0),esk7_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 0.61/0.79  fof(c_0_15, plain, ![X36, X37, X38]:((r1_xboole_0(X36,k2_xboole_0(X37,X38))|~r1_xboole_0(X36,X37)|~r1_xboole_0(X36,X38))&((r1_xboole_0(X36,X37)|~r1_xboole_0(X36,k2_xboole_0(X37,X38)))&(r1_xboole_0(X36,X38)|~r1_xboole_0(X36,k2_xboole_0(X37,X38))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).
% 0.61/0.79  cnf(c_0_16, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.61/0.79  cnf(c_0_17, negated_conjecture, (r1_xboole_0(esk8_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.61/0.79  cnf(c_0_18, plain, (r1_xboole_0(X1,k2_xboole_0(X2,X3))|~r1_xboole_0(X1,X2)|~r1_xboole_0(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.61/0.79  cnf(c_0_19, negated_conjecture, (r1_xboole_0(esk7_0,esk8_0)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.61/0.79  fof(c_0_20, plain, ![X24, X25, X27, X28, X29]:(((r2_hidden(esk3_2(X24,X25),X24)|r1_xboole_0(X24,X25))&(r2_hidden(esk3_2(X24,X25),X25)|r1_xboole_0(X24,X25)))&(~r2_hidden(X29,X27)|~r2_hidden(X29,X28)|~r1_xboole_0(X27,X28))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.61/0.79  cnf(c_0_21, negated_conjecture, (r1_xboole_0(esk7_0,k2_xboole_0(X1,esk8_0))|~r1_xboole_0(esk7_0,X1)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.61/0.79  cnf(c_0_22, plain, (r2_hidden(esk3_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.61/0.79  fof(c_0_23, plain, ![X30, X31, X33, X34, X35]:((r1_xboole_0(X30,X31)|r2_hidden(esk4_2(X30,X31),k3_xboole_0(X30,X31)))&(~r2_hidden(X35,k3_xboole_0(X33,X34))|~r1_xboole_0(X33,X34))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.61/0.79  cnf(c_0_24, negated_conjecture, (r1_xboole_0(esk7_0,k2_xboole_0(X1,esk8_0))|r2_hidden(esk3_2(esk7_0,X1),esk7_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.61/0.79  cnf(c_0_25, plain, (r2_hidden(esk3_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.61/0.79  fof(c_0_26, plain, ![X46]:k2_tarski(X46,X46)=k1_tarski(X46), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.61/0.79  fof(c_0_27, plain, ![X47, X48]:k1_enumset1(X47,X47,X48)=k2_tarski(X47,X48), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.61/0.79  fof(c_0_28, plain, ![X49, X50, X51]:k2_enumset1(X49,X49,X50,X51)=k1_enumset1(X49,X50,X51), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.61/0.79  cnf(c_0_29, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.61/0.79  cnf(c_0_30, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk4_2(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.61/0.79  cnf(c_0_31, negated_conjecture, (~r1_xboole_0(k2_xboole_0(esk6_0,esk8_0),esk7_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.61/0.79  cnf(c_0_32, negated_conjecture, (r1_xboole_0(k2_xboole_0(X1,esk8_0),esk7_0)|r2_hidden(esk3_2(esk7_0,X1),esk7_0)), inference(spm,[status(thm)],[c_0_16, c_0_24])).
% 0.61/0.79  cnf(c_0_33, negated_conjecture, (r1_xboole_0(esk7_0,k2_xboole_0(X1,esk8_0))|r2_hidden(esk3_2(esk7_0,X1),X1)), inference(spm,[status(thm)],[c_0_21, c_0_25])).
% 0.61/0.79  cnf(c_0_34, negated_conjecture, (r1_tarski(k3_xboole_0(esk6_0,esk7_0),k1_tarski(esk9_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.61/0.79  cnf(c_0_35, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.61/0.79  cnf(c_0_36, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.61/0.79  cnf(c_0_37, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.61/0.79  fof(c_0_38, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.61/0.79  fof(c_0_39, plain, ![X13, X14, X15, X16, X17, X18, X19, X20]:((((r2_hidden(X16,X13)|~r2_hidden(X16,X15)|X15!=k3_xboole_0(X13,X14))&(r2_hidden(X16,X14)|~r2_hidden(X16,X15)|X15!=k3_xboole_0(X13,X14)))&(~r2_hidden(X17,X13)|~r2_hidden(X17,X14)|r2_hidden(X17,X15)|X15!=k3_xboole_0(X13,X14)))&((~r2_hidden(esk2_3(X18,X19,X20),X20)|(~r2_hidden(esk2_3(X18,X19,X20),X18)|~r2_hidden(esk2_3(X18,X19,X20),X19))|X20=k3_xboole_0(X18,X19))&((r2_hidden(esk2_3(X18,X19,X20),X18)|r2_hidden(esk2_3(X18,X19,X20),X20)|X20=k3_xboole_0(X18,X19))&(r2_hidden(esk2_3(X18,X19,X20),X19)|r2_hidden(esk2_3(X18,X19,X20),X20)|X20=k3_xboole_0(X18,X19))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.61/0.79  cnf(c_0_40, plain, (r2_hidden(esk4_2(X1,X2),k3_xboole_0(X1,X2))|~r2_hidden(X3,X2)|~r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.61/0.79  cnf(c_0_41, negated_conjecture, (r2_hidden(esk3_2(esk7_0,esk6_0),esk7_0)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.61/0.79  cnf(c_0_42, negated_conjecture, (r1_xboole_0(k2_xboole_0(X1,esk8_0),esk7_0)|r2_hidden(esk3_2(esk7_0,X1),X1)), inference(spm,[status(thm)],[c_0_16, c_0_33])).
% 0.61/0.79  fof(c_0_43, plain, ![X39, X40, X41, X42, X43, X44]:(((~r2_hidden(X41,X40)|X41=X39|X40!=k1_tarski(X39))&(X42!=X39|r2_hidden(X42,X40)|X40!=k1_tarski(X39)))&((~r2_hidden(esk5_2(X43,X44),X44)|esk5_2(X43,X44)!=X43|X44=k1_tarski(X43))&(r2_hidden(esk5_2(X43,X44),X44)|esk5_2(X43,X44)=X43|X44=k1_tarski(X43)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.61/0.79  fof(c_0_44, plain, ![X7, X8, X9, X10, X11]:((~r1_tarski(X7,X8)|(~r2_hidden(X9,X7)|r2_hidden(X9,X8)))&((r2_hidden(esk1_2(X10,X11),X10)|r1_tarski(X10,X11))&(~r2_hidden(esk1_2(X10,X11),X11)|r1_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.61/0.79  cnf(c_0_45, negated_conjecture, (r1_tarski(k3_xboole_0(esk6_0,esk7_0),k2_enumset1(esk9_0,esk9_0,esk9_0,esk9_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_35]), c_0_36]), c_0_37])).
% 0.61/0.79  cnf(c_0_46, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.61/0.79  cnf(c_0_47, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.61/0.79  cnf(c_0_48, negated_conjecture, (r2_hidden(esk4_2(X1,esk7_0),k3_xboole_0(X1,esk7_0))|~r2_hidden(esk3_2(esk7_0,esk6_0),X1)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.61/0.79  cnf(c_0_49, negated_conjecture, (r2_hidden(esk3_2(esk7_0,esk6_0),esk6_0)), inference(spm,[status(thm)],[c_0_31, c_0_42])).
% 0.61/0.79  cnf(c_0_50, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.61/0.79  cnf(c_0_51, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.61/0.79  cnf(c_0_52, negated_conjecture, (r1_tarski(k3_xboole_0(esk7_0,esk6_0),k2_enumset1(esk9_0,esk9_0,esk9_0,esk9_0))), inference(rw,[status(thm)],[c_0_45, c_0_46])).
% 0.61/0.79  cnf(c_0_53, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_47])).
% 0.61/0.79  cnf(c_0_54, negated_conjecture, (r2_hidden(esk4_2(esk6_0,esk7_0),k3_xboole_0(esk7_0,esk6_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_46])).
% 0.61/0.79  cnf(c_0_55, plain, (X1=X3|X2!=k2_enumset1(X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_35]), c_0_36]), c_0_37])).
% 0.61/0.79  cnf(c_0_56, negated_conjecture, (r2_hidden(X1,k2_enumset1(esk9_0,esk9_0,esk9_0,esk9_0))|~r2_hidden(X1,k3_xboole_0(esk7_0,esk6_0))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.61/0.79  cnf(c_0_57, negated_conjecture, (~r2_hidden(X1,esk7_0)|~r2_hidden(X1,esk8_0)), inference(spm,[status(thm)],[c_0_29, c_0_17])).
% 0.61/0.79  cnf(c_0_58, negated_conjecture, (r2_hidden(esk4_2(esk6_0,esk7_0),esk7_0)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.61/0.79  cnf(c_0_59, plain, (X1=X2|~r2_hidden(X1,k2_enumset1(X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_55])).
% 0.61/0.79  cnf(c_0_60, negated_conjecture, (r2_hidden(esk4_2(esk6_0,esk7_0),k2_enumset1(esk9_0,esk9_0,esk9_0,esk9_0))), inference(spm,[status(thm)],[c_0_56, c_0_54])).
% 0.61/0.79  cnf(c_0_61, negated_conjecture, (~r2_hidden(esk4_2(esk6_0,esk7_0),esk8_0)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.61/0.79  cnf(c_0_62, negated_conjecture, (esk4_2(esk6_0,esk7_0)=esk9_0), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.61/0.79  cnf(c_0_63, negated_conjecture, (r2_hidden(esk9_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.61/0.79  cnf(c_0_64, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_62]), c_0_63])]), ['proof']).
% 0.61/0.79  # SZS output end CNFRefutation
% 0.61/0.79  # Proof object total steps             : 65
% 0.61/0.79  # Proof object clause steps            : 40
% 0.61/0.79  # Proof object formula steps           : 25
% 0.61/0.79  # Proof object conjectures             : 26
% 0.61/0.79  # Proof object clause conjectures      : 23
% 0.61/0.79  # Proof object formula conjectures     : 3
% 0.61/0.79  # Proof object initial clauses used    : 17
% 0.61/0.79  # Proof object initial formulas used   : 12
% 0.61/0.79  # Proof object generating inferences   : 17
% 0.61/0.79  # Proof object simplifying inferences  : 13
% 0.61/0.79  # Training examples: 0 positive, 0 negative
% 0.61/0.79  # Parsed axioms                        : 12
% 0.61/0.79  # Removed by relevancy pruning/SinE    : 0
% 0.61/0.79  # Initial clauses                      : 30
% 0.61/0.79  # Removed in clause preprocessing      : 3
% 0.61/0.79  # Initial clauses in saturation        : 27
% 0.61/0.79  # Processed clauses                    : 2939
% 0.61/0.79  # ...of these trivial                  : 94
% 0.61/0.79  # ...subsumed                          : 987
% 0.61/0.79  # ...remaining for further processing  : 1858
% 0.61/0.79  # Other redundant clauses eliminated   : 9
% 0.61/0.79  # Clauses deleted for lack of memory   : 0
% 0.61/0.79  # Backward-subsumed                    : 4
% 0.61/0.79  # Backward-rewritten                   : 99
% 0.61/0.79  # Generated clauses                    : 38791
% 0.61/0.79  # ...of the previous two non-trivial   : 36042
% 0.61/0.79  # Contextual simplify-reflections      : 0
% 0.61/0.79  # Paramodulations                      : 38745
% 0.61/0.79  # Factorizations                       : 38
% 0.61/0.79  # Equation resolutions                 : 9
% 0.61/0.79  # Propositional unsat checks           : 0
% 0.61/0.79  #    Propositional check models        : 0
% 0.61/0.79  #    Propositional check unsatisfiable : 0
% 0.61/0.79  #    Propositional clauses             : 0
% 0.61/0.79  #    Propositional clauses after purity: 0
% 0.61/0.79  #    Propositional unsat core size     : 0
% 0.61/0.79  #    Propositional preprocessing time  : 0.000
% 0.61/0.79  #    Propositional encoding time       : 0.000
% 0.61/0.79  #    Propositional solver time         : 0.000
% 0.61/0.79  #    Success case prop preproc time    : 0.000
% 0.61/0.79  #    Success case prop encoding time   : 0.000
% 0.61/0.79  #    Success case prop solver time     : 0.000
% 0.61/0.79  # Current number of processed clauses  : 1723
% 0.61/0.79  #    Positive orientable unit clauses  : 499
% 0.61/0.79  #    Positive unorientable unit clauses: 1
% 0.61/0.79  #    Negative unit clauses             : 538
% 0.61/0.79  #    Non-unit-clauses                  : 685
% 0.61/0.79  # Current number of unprocessed clauses: 33037
% 0.61/0.79  # ...number of literals in the above   : 79853
% 0.61/0.79  # Current number of archived formulas  : 0
% 0.61/0.79  # Current number of archived clauses   : 133
% 0.61/0.79  # Clause-clause subsumption calls (NU) : 65794
% 0.61/0.79  # Rec. Clause-clause subsumption calls : 55121
% 0.61/0.79  # Non-unit clause-clause subsumptions  : 310
% 0.61/0.79  # Unit Clause-clause subsumption calls : 121489
% 0.61/0.79  # Rewrite failures with RHS unbound    : 0
% 0.61/0.79  # BW rewrite match attempts            : 2698
% 0.61/0.79  # BW rewrite match successes           : 73
% 0.61/0.79  # Condensation attempts                : 0
% 0.61/0.79  # Condensation successes               : 0
% 0.61/0.79  # Termbank termtop insertions          : 725795
% 0.61/0.79  
% 0.61/0.79  # -------------------------------------------------
% 0.61/0.79  # User time                : 0.424 s
% 0.61/0.79  # System time              : 0.023 s
% 0.61/0.79  # Total time               : 0.447 s
% 0.61/0.79  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
