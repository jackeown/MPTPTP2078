%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:52:12 EST 2020

% Result     : Theorem 0.39s
% Output     : CNFRefutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 212 expanded)
%              Number of clauses        :   33 (  89 expanded)
%              Number of leaves         :   10 (  54 expanded)
%              Depth                    :   10
%              Number of atoms          :  189 ( 686 expanded)
%              Number of equality atoms :   81 ( 265 expanded)
%              Maximal formula depth    :   37 (   5 average)
%              Maximal clause size      :   52 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t204_relat_1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> r2_hidden(X2,k11_relat_1(X3,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

fof(d16_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] : k11_relat_1(X1,X2) = k9_relat_1(X1,k1_tarski(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(t143_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k9_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k1_relat_1(X3))
            & r2_hidden(k4_tarski(X4,X1),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(t20_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X1,X2),X3)
       => ( r2_hidden(X1,k1_relat_1(X3))
          & r2_hidden(X2,k2_relat_1(X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_enumset1)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ( r2_hidden(k4_tarski(X1,X2),X3)
        <=> r2_hidden(X2,k11_relat_1(X3,X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t204_relat_1])).

fof(c_0_11,plain,(
    ! [X50,X51] :
      ( ~ v1_relat_1(X50)
      | k11_relat_1(X50,X51) = k9_relat_1(X50,k1_tarski(X51)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_relat_1])])])).

fof(c_0_12,plain,(
    ! [X18] : k2_tarski(X18,X18) = k1_tarski(X18) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_13,plain,(
    ! [X19,X20] : k1_enumset1(X19,X19,X20) = k2_tarski(X19,X20) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_14,plain,(
    ! [X21,X22,X23] : k2_enumset1(X21,X21,X22,X23) = k1_enumset1(X21,X22,X23) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_15,plain,(
    ! [X24,X25,X26,X27] : k3_enumset1(X24,X24,X25,X26,X27) = k2_enumset1(X24,X25,X26,X27) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_16,plain,(
    ! [X28,X29,X30,X31,X32] : k4_enumset1(X28,X28,X29,X30,X31,X32) = k3_enumset1(X28,X29,X30,X31,X32) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_17,plain,(
    ! [X52,X53,X54,X56] :
      ( ( r2_hidden(esk3_3(X52,X53,X54),k1_relat_1(X54))
        | ~ r2_hidden(X52,k9_relat_1(X54,X53))
        | ~ v1_relat_1(X54) )
      & ( r2_hidden(k4_tarski(esk3_3(X52,X53,X54),X52),X54)
        | ~ r2_hidden(X52,k9_relat_1(X54,X53))
        | ~ v1_relat_1(X54) )
      & ( r2_hidden(esk3_3(X52,X53,X54),X53)
        | ~ r2_hidden(X52,k9_relat_1(X54,X53))
        | ~ v1_relat_1(X54) )
      & ( ~ r2_hidden(X56,k1_relat_1(X54))
        | ~ r2_hidden(k4_tarski(X56,X52),X54)
        | ~ r2_hidden(X56,X53)
        | r2_hidden(X52,k9_relat_1(X54,X53))
        | ~ v1_relat_1(X54) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).

fof(c_0_18,negated_conjecture,
    ( v1_relat_1(esk6_0)
    & ( ~ r2_hidden(k4_tarski(esk4_0,esk5_0),esk6_0)
      | ~ r2_hidden(esk5_0,k11_relat_1(esk6_0,esk4_0)) )
    & ( r2_hidden(k4_tarski(esk4_0,esk5_0),esk6_0)
      | r2_hidden(esk5_0,k11_relat_1(esk6_0,esk4_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

cnf(c_0_19,plain,
    ( k11_relat_1(X1,X2) = k9_relat_1(X1,k1_tarski(X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),X2)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( k11_relat_1(X1,X2) = k9_relat_1(X1,k4_enumset1(X2,X2,X2,X2,X2,X2))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_22]),c_0_23]),c_0_24])).

fof(c_0_28,plain,(
    ! [X57,X58,X59] :
      ( ( r2_hidden(X57,k1_relat_1(X59))
        | ~ r2_hidden(k4_tarski(X57,X58),X59)
        | ~ v1_relat_1(X59) )
      & ( r2_hidden(X58,k2_relat_1(X59))
        | ~ r2_hidden(k4_tarski(X57,X58),X59)
        | ~ v1_relat_1(X59) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_relat_1])])])).

cnf(c_0_29,plain,
    ( r2_hidden(k4_tarski(esk3_3(X1,X2,X3),X1),X3)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_30,plain,(
    ! [X33,X34,X35,X36,X37,X38,X39,X40,X41,X42,X43,X44,X45,X46,X47,X48] :
      ( ( ~ r2_hidden(X40,X39)
        | X40 = X33
        | X40 = X34
        | X40 = X35
        | X40 = X36
        | X40 = X37
        | X40 = X38
        | X39 != k4_enumset1(X33,X34,X35,X36,X37,X38) )
      & ( X41 != X33
        | r2_hidden(X41,X39)
        | X39 != k4_enumset1(X33,X34,X35,X36,X37,X38) )
      & ( X41 != X34
        | r2_hidden(X41,X39)
        | X39 != k4_enumset1(X33,X34,X35,X36,X37,X38) )
      & ( X41 != X35
        | r2_hidden(X41,X39)
        | X39 != k4_enumset1(X33,X34,X35,X36,X37,X38) )
      & ( X41 != X36
        | r2_hidden(X41,X39)
        | X39 != k4_enumset1(X33,X34,X35,X36,X37,X38) )
      & ( X41 != X37
        | r2_hidden(X41,X39)
        | X39 != k4_enumset1(X33,X34,X35,X36,X37,X38) )
      & ( X41 != X38
        | r2_hidden(X41,X39)
        | X39 != k4_enumset1(X33,X34,X35,X36,X37,X38) )
      & ( esk2_7(X42,X43,X44,X45,X46,X47,X48) != X42
        | ~ r2_hidden(esk2_7(X42,X43,X44,X45,X46,X47,X48),X48)
        | X48 = k4_enumset1(X42,X43,X44,X45,X46,X47) )
      & ( esk2_7(X42,X43,X44,X45,X46,X47,X48) != X43
        | ~ r2_hidden(esk2_7(X42,X43,X44,X45,X46,X47,X48),X48)
        | X48 = k4_enumset1(X42,X43,X44,X45,X46,X47) )
      & ( esk2_7(X42,X43,X44,X45,X46,X47,X48) != X44
        | ~ r2_hidden(esk2_7(X42,X43,X44,X45,X46,X47,X48),X48)
        | X48 = k4_enumset1(X42,X43,X44,X45,X46,X47) )
      & ( esk2_7(X42,X43,X44,X45,X46,X47,X48) != X45
        | ~ r2_hidden(esk2_7(X42,X43,X44,X45,X46,X47,X48),X48)
        | X48 = k4_enumset1(X42,X43,X44,X45,X46,X47) )
      & ( esk2_7(X42,X43,X44,X45,X46,X47,X48) != X46
        | ~ r2_hidden(esk2_7(X42,X43,X44,X45,X46,X47,X48),X48)
        | X48 = k4_enumset1(X42,X43,X44,X45,X46,X47) )
      & ( esk2_7(X42,X43,X44,X45,X46,X47,X48) != X47
        | ~ r2_hidden(esk2_7(X42,X43,X44,X45,X46,X47,X48),X48)
        | X48 = k4_enumset1(X42,X43,X44,X45,X46,X47) )
      & ( r2_hidden(esk2_7(X42,X43,X44,X45,X46,X47,X48),X48)
        | esk2_7(X42,X43,X44,X45,X46,X47,X48) = X42
        | esk2_7(X42,X43,X44,X45,X46,X47,X48) = X43
        | esk2_7(X42,X43,X44,X45,X46,X47,X48) = X44
        | esk2_7(X42,X43,X44,X45,X46,X47,X48) = X45
        | esk2_7(X42,X43,X44,X45,X46,X47,X48) = X46
        | esk2_7(X42,X43,X44,X45,X46,X47,X48) = X47
        | X48 = k4_enumset1(X42,X43,X44,X45,X46,X47) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_enumset1])])])])])])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk3_3(X1,X2,esk6_0),X2)
    | ~ r2_hidden(X1,k9_relat_1(esk6_0,X2)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( k9_relat_1(esk6_0,k4_enumset1(X1,X1,X1,X1,X1,X1)) = k11_relat_1(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_26])).

cnf(c_0_33,plain,
    ( r2_hidden(X3,k9_relat_1(X2,X4))
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,X4)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_3(X1,X2,esk6_0),X1),esk6_0)
    | ~ r2_hidden(X1,k9_relat_1(esk6_0,X2)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_26])).

cnf(c_0_36,plain,
    ( X1 = X3
    | X1 = X4
    | X1 = X5
    | X1 = X6
    | X1 = X7
    | X1 = X8
    | ~ r2_hidden(X1,X2)
    | X2 != k4_enumset1(X3,X4,X5,X6,X7,X8) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk3_3(X1,k4_enumset1(X2,X2,X2,X2,X2,X2),esk6_0),k4_enumset1(X2,X2,X2,X2,X2,X2))
    | ~ r2_hidden(X1,k11_relat_1(esk6_0,X2)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(k4_tarski(esk4_0,esk5_0),esk6_0)
    | r2_hidden(esk5_0,k11_relat_1(esk6_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,k9_relat_1(X2,X3))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X4,X1),X2)
    | ~ r2_hidden(X4,X3) ),
    inference(csr,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k4_enumset1(X2,X4,X5,X6,X7,X8) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_3(X1,k4_enumset1(X2,X2,X2,X2,X2,X2),esk6_0),X1),esk6_0)
    | ~ r2_hidden(X1,k11_relat_1(esk6_0,X2)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_32])).

cnf(c_0_42,plain,
    ( X1 = X2
    | X1 = X3
    | X1 = X4
    | X1 = X5
    | X1 = X6
    | X1 = X7
    | ~ r2_hidden(X1,k4_enumset1(X7,X6,X5,X4,X3,X2)) ),
    inference(er,[status(thm)],[c_0_36])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk3_3(esk5_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),esk6_0),k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))
    | r2_hidden(k4_tarski(esk4_0,esk5_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(X1,k9_relat_1(esk6_0,X2))
    | ~ r2_hidden(k4_tarski(X3,X1),esk6_0)
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_39,c_0_26])).

cnf(c_0_45,plain,
    ( r2_hidden(X1,k4_enumset1(X1,X2,X3,X4,X5,X6)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_40])])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_3(esk5_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),esk6_0),esk5_0),esk6_0)
    | r2_hidden(k4_tarski(esk4_0,esk5_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_38])).

cnf(c_0_47,negated_conjecture,
    ( esk3_3(esk5_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),esk6_0) = esk4_0
    | r2_hidden(k4_tarski(esk4_0,esk5_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(X1,k9_relat_1(esk6_0,k4_enumset1(X2,X3,X4,X5,X6,X7)))
    | ~ r2_hidden(k4_tarski(X2,X1),esk6_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(k4_tarski(esk4_0,esk5_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_50,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk4_0,esk5_0),esk6_0)
    | ~ r2_hidden(esk5_0,k11_relat_1(esk6_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(esk5_0,k9_relat_1(esk6_0,k4_enumset1(esk4_0,X1,X2,X3,X4,X5))) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_52,negated_conjecture,
    ( ~ r2_hidden(esk5_0,k11_relat_1(esk6_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_49])])).

cnf(c_0_53,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_32]),c_0_52]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:35:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.39/0.61  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S054N
% 0.39/0.61  # and selection function GSelectMinInfpos.
% 0.39/0.61  #
% 0.39/0.61  # Preprocessing time       : 0.028 s
% 0.39/0.61  # Presaturation interreduction done
% 0.39/0.61  
% 0.39/0.61  # Proof found!
% 0.39/0.61  # SZS status Theorem
% 0.39/0.61  # SZS output start CNFRefutation
% 0.39/0.61  fof(t204_relat_1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)<=>r2_hidden(X2,k11_relat_1(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t204_relat_1)).
% 0.39/0.61  fof(d16_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:k11_relat_1(X1,X2)=k9_relat_1(X1,k1_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_relat_1)).
% 0.39/0.61  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.39/0.61  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.39/0.61  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.39/0.61  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.39/0.61  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.39/0.61  fof(t143_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k9_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k1_relat_1(X3))&r2_hidden(k4_tarski(X4,X1),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 0.39/0.61  fof(t20_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)=>(r2_hidden(X1,k1_relat_1(X3))&r2_hidden(X2,k2_relat_1(X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_relat_1)).
% 0.39/0.61  fof(d4_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:(X7=k4_enumset1(X1,X2,X3,X4,X5,X6)<=>![X8]:(r2_hidden(X8,X7)<=>~((((((X8!=X1&X8!=X2)&X8!=X3)&X8!=X4)&X8!=X5)&X8!=X6)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_enumset1)).
% 0.39/0.61  fof(c_0_10, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)<=>r2_hidden(X2,k11_relat_1(X3,X1))))), inference(assume_negation,[status(cth)],[t204_relat_1])).
% 0.39/0.61  fof(c_0_11, plain, ![X50, X51]:(~v1_relat_1(X50)|k11_relat_1(X50,X51)=k9_relat_1(X50,k1_tarski(X51))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_relat_1])])])).
% 0.39/0.61  fof(c_0_12, plain, ![X18]:k2_tarski(X18,X18)=k1_tarski(X18), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.39/0.61  fof(c_0_13, plain, ![X19, X20]:k1_enumset1(X19,X19,X20)=k2_tarski(X19,X20), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.39/0.61  fof(c_0_14, plain, ![X21, X22, X23]:k2_enumset1(X21,X21,X22,X23)=k1_enumset1(X21,X22,X23), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.39/0.61  fof(c_0_15, plain, ![X24, X25, X26, X27]:k3_enumset1(X24,X24,X25,X26,X27)=k2_enumset1(X24,X25,X26,X27), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.39/0.61  fof(c_0_16, plain, ![X28, X29, X30, X31, X32]:k4_enumset1(X28,X28,X29,X30,X31,X32)=k3_enumset1(X28,X29,X30,X31,X32), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.39/0.61  fof(c_0_17, plain, ![X52, X53, X54, X56]:((((r2_hidden(esk3_3(X52,X53,X54),k1_relat_1(X54))|~r2_hidden(X52,k9_relat_1(X54,X53))|~v1_relat_1(X54))&(r2_hidden(k4_tarski(esk3_3(X52,X53,X54),X52),X54)|~r2_hidden(X52,k9_relat_1(X54,X53))|~v1_relat_1(X54)))&(r2_hidden(esk3_3(X52,X53,X54),X53)|~r2_hidden(X52,k9_relat_1(X54,X53))|~v1_relat_1(X54)))&(~r2_hidden(X56,k1_relat_1(X54))|~r2_hidden(k4_tarski(X56,X52),X54)|~r2_hidden(X56,X53)|r2_hidden(X52,k9_relat_1(X54,X53))|~v1_relat_1(X54))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).
% 0.39/0.61  fof(c_0_18, negated_conjecture, (v1_relat_1(esk6_0)&((~r2_hidden(k4_tarski(esk4_0,esk5_0),esk6_0)|~r2_hidden(esk5_0,k11_relat_1(esk6_0,esk4_0)))&(r2_hidden(k4_tarski(esk4_0,esk5_0),esk6_0)|r2_hidden(esk5_0,k11_relat_1(esk6_0,esk4_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).
% 0.39/0.61  cnf(c_0_19, plain, (k11_relat_1(X1,X2)=k9_relat_1(X1,k1_tarski(X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.39/0.61  cnf(c_0_20, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.39/0.61  cnf(c_0_21, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.39/0.61  cnf(c_0_22, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.39/0.61  cnf(c_0_23, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.39/0.61  cnf(c_0_24, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.39/0.61  cnf(c_0_25, plain, (r2_hidden(esk3_3(X1,X2,X3),X2)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.39/0.61  cnf(c_0_26, negated_conjecture, (v1_relat_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.39/0.61  cnf(c_0_27, plain, (k11_relat_1(X1,X2)=k9_relat_1(X1,k4_enumset1(X2,X2,X2,X2,X2,X2))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_20]), c_0_21]), c_0_22]), c_0_23]), c_0_24])).
% 0.39/0.61  fof(c_0_28, plain, ![X57, X58, X59]:((r2_hidden(X57,k1_relat_1(X59))|~r2_hidden(k4_tarski(X57,X58),X59)|~v1_relat_1(X59))&(r2_hidden(X58,k2_relat_1(X59))|~r2_hidden(k4_tarski(X57,X58),X59)|~v1_relat_1(X59))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_relat_1])])])).
% 0.39/0.61  cnf(c_0_29, plain, (r2_hidden(k4_tarski(esk3_3(X1,X2,X3),X1),X3)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.39/0.61  fof(c_0_30, plain, ![X33, X34, X35, X36, X37, X38, X39, X40, X41, X42, X43, X44, X45, X46, X47, X48]:(((~r2_hidden(X40,X39)|(X40=X33|X40=X34|X40=X35|X40=X36|X40=X37|X40=X38)|X39!=k4_enumset1(X33,X34,X35,X36,X37,X38))&((((((X41!=X33|r2_hidden(X41,X39)|X39!=k4_enumset1(X33,X34,X35,X36,X37,X38))&(X41!=X34|r2_hidden(X41,X39)|X39!=k4_enumset1(X33,X34,X35,X36,X37,X38)))&(X41!=X35|r2_hidden(X41,X39)|X39!=k4_enumset1(X33,X34,X35,X36,X37,X38)))&(X41!=X36|r2_hidden(X41,X39)|X39!=k4_enumset1(X33,X34,X35,X36,X37,X38)))&(X41!=X37|r2_hidden(X41,X39)|X39!=k4_enumset1(X33,X34,X35,X36,X37,X38)))&(X41!=X38|r2_hidden(X41,X39)|X39!=k4_enumset1(X33,X34,X35,X36,X37,X38))))&(((((((esk2_7(X42,X43,X44,X45,X46,X47,X48)!=X42|~r2_hidden(esk2_7(X42,X43,X44,X45,X46,X47,X48),X48)|X48=k4_enumset1(X42,X43,X44,X45,X46,X47))&(esk2_7(X42,X43,X44,X45,X46,X47,X48)!=X43|~r2_hidden(esk2_7(X42,X43,X44,X45,X46,X47,X48),X48)|X48=k4_enumset1(X42,X43,X44,X45,X46,X47)))&(esk2_7(X42,X43,X44,X45,X46,X47,X48)!=X44|~r2_hidden(esk2_7(X42,X43,X44,X45,X46,X47,X48),X48)|X48=k4_enumset1(X42,X43,X44,X45,X46,X47)))&(esk2_7(X42,X43,X44,X45,X46,X47,X48)!=X45|~r2_hidden(esk2_7(X42,X43,X44,X45,X46,X47,X48),X48)|X48=k4_enumset1(X42,X43,X44,X45,X46,X47)))&(esk2_7(X42,X43,X44,X45,X46,X47,X48)!=X46|~r2_hidden(esk2_7(X42,X43,X44,X45,X46,X47,X48),X48)|X48=k4_enumset1(X42,X43,X44,X45,X46,X47)))&(esk2_7(X42,X43,X44,X45,X46,X47,X48)!=X47|~r2_hidden(esk2_7(X42,X43,X44,X45,X46,X47,X48),X48)|X48=k4_enumset1(X42,X43,X44,X45,X46,X47)))&(r2_hidden(esk2_7(X42,X43,X44,X45,X46,X47,X48),X48)|(esk2_7(X42,X43,X44,X45,X46,X47,X48)=X42|esk2_7(X42,X43,X44,X45,X46,X47,X48)=X43|esk2_7(X42,X43,X44,X45,X46,X47,X48)=X44|esk2_7(X42,X43,X44,X45,X46,X47,X48)=X45|esk2_7(X42,X43,X44,X45,X46,X47,X48)=X46|esk2_7(X42,X43,X44,X45,X46,X47,X48)=X47)|X48=k4_enumset1(X42,X43,X44,X45,X46,X47)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_enumset1])])])])])])).
% 0.39/0.61  cnf(c_0_31, negated_conjecture, (r2_hidden(esk3_3(X1,X2,esk6_0),X2)|~r2_hidden(X1,k9_relat_1(esk6_0,X2))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.39/0.61  cnf(c_0_32, negated_conjecture, (k9_relat_1(esk6_0,k4_enumset1(X1,X1,X1,X1,X1,X1))=k11_relat_1(esk6_0,X1)), inference(spm,[status(thm)],[c_0_27, c_0_26])).
% 0.39/0.61  cnf(c_0_33, plain, (r2_hidden(X3,k9_relat_1(X2,X4))|~r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)|~r2_hidden(X1,X4)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.39/0.61  cnf(c_0_34, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.39/0.61  cnf(c_0_35, negated_conjecture, (r2_hidden(k4_tarski(esk3_3(X1,X2,esk6_0),X1),esk6_0)|~r2_hidden(X1,k9_relat_1(esk6_0,X2))), inference(spm,[status(thm)],[c_0_29, c_0_26])).
% 0.39/0.61  cnf(c_0_36, plain, (X1=X3|X1=X4|X1=X5|X1=X6|X1=X7|X1=X8|~r2_hidden(X1,X2)|X2!=k4_enumset1(X3,X4,X5,X6,X7,X8)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.39/0.61  cnf(c_0_37, negated_conjecture, (r2_hidden(esk3_3(X1,k4_enumset1(X2,X2,X2,X2,X2,X2),esk6_0),k4_enumset1(X2,X2,X2,X2,X2,X2))|~r2_hidden(X1,k11_relat_1(esk6_0,X2))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.39/0.61  cnf(c_0_38, negated_conjecture, (r2_hidden(k4_tarski(esk4_0,esk5_0),esk6_0)|r2_hidden(esk5_0,k11_relat_1(esk6_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.39/0.61  cnf(c_0_39, plain, (r2_hidden(X1,k9_relat_1(X2,X3))|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X4,X1),X2)|~r2_hidden(X4,X3)), inference(csr,[status(thm)],[c_0_33, c_0_34])).
% 0.39/0.61  cnf(c_0_40, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k4_enumset1(X2,X4,X5,X6,X7,X8)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.39/0.61  cnf(c_0_41, negated_conjecture, (r2_hidden(k4_tarski(esk3_3(X1,k4_enumset1(X2,X2,X2,X2,X2,X2),esk6_0),X1),esk6_0)|~r2_hidden(X1,k11_relat_1(esk6_0,X2))), inference(spm,[status(thm)],[c_0_35, c_0_32])).
% 0.39/0.61  cnf(c_0_42, plain, (X1=X2|X1=X3|X1=X4|X1=X5|X1=X6|X1=X7|~r2_hidden(X1,k4_enumset1(X7,X6,X5,X4,X3,X2))), inference(er,[status(thm)],[c_0_36])).
% 0.39/0.61  cnf(c_0_43, negated_conjecture, (r2_hidden(esk3_3(esk5_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),esk6_0),k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))|r2_hidden(k4_tarski(esk4_0,esk5_0),esk6_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.39/0.61  cnf(c_0_44, negated_conjecture, (r2_hidden(X1,k9_relat_1(esk6_0,X2))|~r2_hidden(k4_tarski(X3,X1),esk6_0)|~r2_hidden(X3,X2)), inference(spm,[status(thm)],[c_0_39, c_0_26])).
% 0.39/0.61  cnf(c_0_45, plain, (r2_hidden(X1,k4_enumset1(X1,X2,X3,X4,X5,X6))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_40])])).
% 0.39/0.61  cnf(c_0_46, negated_conjecture, (r2_hidden(k4_tarski(esk3_3(esk5_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),esk6_0),esk5_0),esk6_0)|r2_hidden(k4_tarski(esk4_0,esk5_0),esk6_0)), inference(spm,[status(thm)],[c_0_41, c_0_38])).
% 0.39/0.61  cnf(c_0_47, negated_conjecture, (esk3_3(esk5_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),esk6_0)=esk4_0|r2_hidden(k4_tarski(esk4_0,esk5_0),esk6_0)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.39/0.61  cnf(c_0_48, negated_conjecture, (r2_hidden(X1,k9_relat_1(esk6_0,k4_enumset1(X2,X3,X4,X5,X6,X7)))|~r2_hidden(k4_tarski(X2,X1),esk6_0)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.39/0.61  cnf(c_0_49, negated_conjecture, (r2_hidden(k4_tarski(esk4_0,esk5_0),esk6_0)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.39/0.61  cnf(c_0_50, negated_conjecture, (~r2_hidden(k4_tarski(esk4_0,esk5_0),esk6_0)|~r2_hidden(esk5_0,k11_relat_1(esk6_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.39/0.61  cnf(c_0_51, negated_conjecture, (r2_hidden(esk5_0,k9_relat_1(esk6_0,k4_enumset1(esk4_0,X1,X2,X3,X4,X5)))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.39/0.61  cnf(c_0_52, negated_conjecture, (~r2_hidden(esk5_0,k11_relat_1(esk6_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_49])])).
% 0.39/0.61  cnf(c_0_53, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_32]), c_0_52]), ['proof']).
% 0.39/0.61  # SZS output end CNFRefutation
% 0.39/0.61  # Proof object total steps             : 54
% 0.39/0.61  # Proof object clause steps            : 33
% 0.39/0.61  # Proof object formula steps           : 21
% 0.39/0.61  # Proof object conjectures             : 20
% 0.39/0.61  # Proof object clause conjectures      : 17
% 0.39/0.61  # Proof object formula conjectures     : 3
% 0.39/0.61  # Proof object initial clauses used    : 15
% 0.39/0.61  # Proof object initial formulas used   : 10
% 0.39/0.61  # Proof object generating inferences   : 13
% 0.39/0.61  # Proof object simplifying inferences  : 12
% 0.39/0.61  # Training examples: 0 positive, 0 negative
% 0.39/0.61  # Parsed axioms                        : 11
% 0.39/0.61  # Removed by relevancy pruning/SinE    : 0
% 0.39/0.61  # Initial clauses                      : 35
% 0.39/0.61  # Removed in clause preprocessing      : 5
% 0.39/0.61  # Initial clauses in saturation        : 30
% 0.39/0.61  # Processed clauses                    : 293
% 0.39/0.61  # ...of these trivial                  : 2
% 0.39/0.61  # ...subsumed                          : 74
% 0.39/0.61  # ...remaining for further processing  : 217
% 0.39/0.61  # Other redundant clauses eliminated   : 156
% 0.39/0.61  # Clauses deleted for lack of memory   : 0
% 0.39/0.61  # Backward-subsumed                    : 0
% 0.39/0.61  # Backward-rewritten                   : 96
% 0.39/0.61  # Generated clauses                    : 4189
% 0.39/0.61  # ...of the previous two non-trivial   : 3796
% 0.39/0.61  # Contextual simplify-reflections      : 2
% 0.39/0.61  # Paramodulations                      : 3935
% 0.39/0.61  # Factorizations                       : 106
% 0.39/0.61  # Equation resolutions                 : 156
% 0.39/0.61  # Propositional unsat checks           : 0
% 0.39/0.61  #    Propositional check models        : 0
% 0.39/0.61  #    Propositional check unsatisfiable : 0
% 0.39/0.61  #    Propositional clauses             : 0
% 0.39/0.61  #    Propositional clauses after purity: 0
% 0.39/0.61  #    Propositional unsat core size     : 0
% 0.39/0.61  #    Propositional preprocessing time  : 0.000
% 0.39/0.61  #    Propositional encoding time       : 0.000
% 0.39/0.61  #    Propositional solver time         : 0.000
% 0.39/0.61  #    Success case prop preproc time    : 0.000
% 0.39/0.61  #    Success case prop encoding time   : 0.000
% 0.39/0.61  #    Success case prop solver time     : 0.000
% 0.39/0.61  # Current number of processed clauses  : 83
% 0.39/0.61  #    Positive orientable unit clauses  : 15
% 0.39/0.61  #    Positive unorientable unit clauses: 0
% 0.39/0.61  #    Negative unit clauses             : 1
% 0.39/0.61  #    Non-unit-clauses                  : 67
% 0.39/0.61  # Current number of unprocessed clauses: 3533
% 0.39/0.61  # ...number of literals in the above   : 32238
% 0.39/0.61  # Current number of archived formulas  : 0
% 0.39/0.61  # Current number of archived clauses   : 129
% 0.39/0.61  # Clause-clause subsumption calls (NU) : 7574
% 0.39/0.61  # Rec. Clause-clause subsumption calls : 2698
% 0.39/0.61  # Non-unit clause-clause subsumptions  : 76
% 0.39/0.61  # Unit Clause-clause subsumption calls : 10
% 0.39/0.61  # Rewrite failures with RHS unbound    : 0
% 0.39/0.61  # BW rewrite match attempts            : 38
% 0.39/0.61  # BW rewrite match successes           : 1
% 0.39/0.61  # Condensation attempts                : 0
% 0.39/0.61  # Condensation successes               : 0
% 0.39/0.61  # Termbank termtop insertions          : 139858
% 0.39/0.61  
% 0.39/0.61  # -------------------------------------------------
% 0.39/0.61  # User time                : 0.240 s
% 0.39/0.61  # System time              : 0.015 s
% 0.39/0.61  # Total time               : 0.255 s
% 0.39/0.61  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
