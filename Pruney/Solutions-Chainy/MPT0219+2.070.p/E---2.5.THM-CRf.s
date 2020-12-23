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
% DateTime   : Thu Dec  3 10:37:27 EST 2020

% Result     : Theorem 3.53s
% Output     : CNFRefutation 3.53s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 198 expanded)
%              Number of clauses        :   37 (  84 expanded)
%              Number of leaves         :   11 (  56 expanded)
%              Depth                    :    9
%              Number of atoms          :  147 ( 416 expanded)
%              Number of equality atoms :   62 ( 235 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

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

fof(t13_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_zfmisc_1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t1_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k5_xboole_0(X2,X3))
    <=> ~ ( r2_hidden(X1,X2)
        <=> r2_hidden(X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(c_0_11,plain,(
    ! [X13,X14,X15,X16,X17,X18,X19,X20] :
      ( ( r2_hidden(X16,X13)
        | ~ r2_hidden(X16,X15)
        | X15 != k4_xboole_0(X13,X14) )
      & ( ~ r2_hidden(X16,X14)
        | ~ r2_hidden(X16,X15)
        | X15 != k4_xboole_0(X13,X14) )
      & ( ~ r2_hidden(X17,X13)
        | r2_hidden(X17,X14)
        | r2_hidden(X17,X15)
        | X15 != k4_xboole_0(X13,X14) )
      & ( ~ r2_hidden(esk2_3(X18,X19,X20),X20)
        | ~ r2_hidden(esk2_3(X18,X19,X20),X18)
        | r2_hidden(esk2_3(X18,X19,X20),X19)
        | X20 = k4_xboole_0(X18,X19) )
      & ( r2_hidden(esk2_3(X18,X19,X20),X18)
        | r2_hidden(esk2_3(X18,X19,X20),X20)
        | X20 = k4_xboole_0(X18,X19) )
      & ( ~ r2_hidden(esk2_3(X18,X19,X20),X19)
        | r2_hidden(esk2_3(X18,X19,X20),X20)
        | X20 = k4_xboole_0(X18,X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_12,plain,(
    ! [X27,X28] : k4_xboole_0(X27,X28) = k5_xboole_0(X27,k3_xboole_0(X27,X28)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_13,plain,(
    ! [X36,X37,X38,X39,X40,X41] :
      ( ( ~ r2_hidden(X38,X37)
        | X38 = X36
        | X37 != k1_tarski(X36) )
      & ( X39 != X36
        | r2_hidden(X39,X37)
        | X37 != k1_tarski(X36) )
      & ( ~ r2_hidden(esk3_2(X40,X41),X41)
        | esk3_2(X40,X41) != X40
        | X41 = k1_tarski(X40) )
      & ( r2_hidden(esk3_2(X40,X41),X41)
        | esk3_2(X40,X41) = X40
        | X41 = k1_tarski(X40) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_14,plain,(
    ! [X43] : k2_tarski(X43,X43) = k1_tarski(X43) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_15,plain,(
    ! [X44,X45] : k1_enumset1(X44,X44,X45) = k2_tarski(X44,X45) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_16,plain,(
    ! [X46,X47,X48] : k2_enumset1(X46,X46,X47,X48) = k1_enumset1(X46,X47,X48) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_17,plain,(
    ! [X49,X50,X51,X52] : k3_enumset1(X49,X49,X50,X51,X52) = k2_enumset1(X49,X50,X51,X52) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X4 != k4_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_25,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
       => X1 = X2 ) ),
    inference(assume_negation,[status(cth)],[t13_zfmisc_1])).

fof(c_0_26,plain,(
    ! [X34,X35] : k2_xboole_0(X34,X35) = k5_xboole_0(X34,k4_xboole_0(X35,X34)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

cnf(c_0_27,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,X4)
    | r2_hidden(X1,X3)
    | X4 != k5_xboole_0(X2,k3_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k3_enumset1(X2,X2,X2,X2,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_23]),c_0_24])).

fof(c_0_30,plain,(
    ! [X24,X25,X26] :
      ( ( ~ r2_hidden(X24,X25)
        | ~ r2_hidden(X24,X26)
        | ~ r2_hidden(X24,k5_xboole_0(X25,X26)) )
      & ( r2_hidden(X24,X25)
        | r2_hidden(X24,X26)
        | ~ r2_hidden(X24,k5_xboole_0(X25,X26)) )
      & ( ~ r2_hidden(X24,X25)
        | r2_hidden(X24,X26)
        | r2_hidden(X24,k5_xboole_0(X25,X26)) )
      & ( ~ r2_hidden(X24,X26)
        | r2_hidden(X24,X25)
        | r2_hidden(X24,k5_xboole_0(X25,X26)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).

fof(c_0_31,negated_conjecture,
    ( k2_xboole_0(k1_tarski(esk4_0),k1_tarski(esk5_0)) = k1_tarski(esk4_0)
    & esk4_0 != esk5_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).

cnf(c_0_32,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( X3 != k5_xboole_0(X4,k3_xboole_0(X4,X2))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_27,c_0_19])).

fof(c_0_34,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,k3_enumset1(X1,X1,X1,X1,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_29])])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,k5_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,negated_conjecture,
    ( k2_xboole_0(k1_tarski(esk4_0),k1_tarski(esk5_0)) = k1_tarski(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[c_0_32,c_0_19])).

cnf(c_0_40,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_33])).

cnf(c_0_41,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),X2)))
    | r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_44,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,k5_xboole_0(X3,X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_45,plain,
    ( r2_hidden(X1,k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),X2))
    | r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_37,c_0_36])).

cnf(c_0_46,negated_conjecture,
    ( k5_xboole_0(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k5_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)))) = k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_21]),c_0_21]),c_0_21]),c_0_22]),c_0_22]),c_0_22]),c_0_39]),c_0_23]),c_0_23]),c_0_23]),c_0_23]),c_0_23]),c_0_24]),c_0_24]),c_0_24]),c_0_24]),c_0_24])).

cnf(c_0_47,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X3,X2)))
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_48,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_49,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_36])])).

cnf(c_0_50,plain,
    ( r2_hidden(X1,k5_xboole_0(X2,k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),X3)))
    | r2_hidden(X1,X3)
    | r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_51,negated_conjecture,
    ( k5_xboole_0(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k5_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_xboole_0(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))) = k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_46,c_0_41])).

cnf(c_0_52,plain,
    ( r2_hidden(X1,k3_xboole_0(X2,k3_enumset1(X1,X1,X1,X1,X1)))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_47,c_0_45])).

cnf(c_0_53,plain,
    ( X1 = X3
    | X2 != k3_enumset1(X3,X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_21]),c_0_22]),c_0_23]),c_0_24])).

cnf(c_0_54,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,k3_enumset1(X1,X1,X1,X1,X1))) ),
    inference(spm,[status(thm)],[c_0_49,c_0_41])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(esk5_0,k3_xboole_0(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52])).

cnf(c_0_56,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k3_enumset1(X2,X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_53])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(esk5_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_58,negated_conjecture,
    ( esk4_0 != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_59,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:32:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 3.53/3.74  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 3.53/3.74  # and selection function SelectNegativeLiterals.
% 3.53/3.74  #
% 3.53/3.74  # Preprocessing time       : 0.050 s
% 3.53/3.74  # Presaturation interreduction done
% 3.53/3.74  
% 3.53/3.74  # Proof found!
% 3.53/3.74  # SZS status Theorem
% 3.53/3.74  # SZS output start CNFRefutation
% 3.53/3.74  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.53/3.74  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.53/3.74  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 3.53/3.74  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.53/3.74  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.53/3.74  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 3.53/3.74  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 3.53/3.74  fof(t13_zfmisc_1, conjecture, ![X1, X2]:(k2_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)=>X1=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 3.53/3.74  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.53/3.74  fof(t1_xboole_0, axiom, ![X1, X2, X3]:(r2_hidden(X1,k5_xboole_0(X2,X3))<=>~((r2_hidden(X1,X2)<=>r2_hidden(X1,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 3.53/3.74  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.53/3.74  fof(c_0_11, plain, ![X13, X14, X15, X16, X17, X18, X19, X20]:((((r2_hidden(X16,X13)|~r2_hidden(X16,X15)|X15!=k4_xboole_0(X13,X14))&(~r2_hidden(X16,X14)|~r2_hidden(X16,X15)|X15!=k4_xboole_0(X13,X14)))&(~r2_hidden(X17,X13)|r2_hidden(X17,X14)|r2_hidden(X17,X15)|X15!=k4_xboole_0(X13,X14)))&((~r2_hidden(esk2_3(X18,X19,X20),X20)|(~r2_hidden(esk2_3(X18,X19,X20),X18)|r2_hidden(esk2_3(X18,X19,X20),X19))|X20=k4_xboole_0(X18,X19))&((r2_hidden(esk2_3(X18,X19,X20),X18)|r2_hidden(esk2_3(X18,X19,X20),X20)|X20=k4_xboole_0(X18,X19))&(~r2_hidden(esk2_3(X18,X19,X20),X19)|r2_hidden(esk2_3(X18,X19,X20),X20)|X20=k4_xboole_0(X18,X19))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 3.53/3.74  fof(c_0_12, plain, ![X27, X28]:k4_xboole_0(X27,X28)=k5_xboole_0(X27,k3_xboole_0(X27,X28)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 3.53/3.74  fof(c_0_13, plain, ![X36, X37, X38, X39, X40, X41]:(((~r2_hidden(X38,X37)|X38=X36|X37!=k1_tarski(X36))&(X39!=X36|r2_hidden(X39,X37)|X37!=k1_tarski(X36)))&((~r2_hidden(esk3_2(X40,X41),X41)|esk3_2(X40,X41)!=X40|X41=k1_tarski(X40))&(r2_hidden(esk3_2(X40,X41),X41)|esk3_2(X40,X41)=X40|X41=k1_tarski(X40)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 3.53/3.74  fof(c_0_14, plain, ![X43]:k2_tarski(X43,X43)=k1_tarski(X43), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 3.53/3.74  fof(c_0_15, plain, ![X44, X45]:k1_enumset1(X44,X44,X45)=k2_tarski(X44,X45), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 3.53/3.74  fof(c_0_16, plain, ![X46, X47, X48]:k2_enumset1(X46,X46,X47,X48)=k1_enumset1(X46,X47,X48), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 3.53/3.74  fof(c_0_17, plain, ![X49, X50, X51, X52]:k3_enumset1(X49,X49,X50,X51,X52)=k2_enumset1(X49,X50,X51,X52), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 3.53/3.74  cnf(c_0_18, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X4!=k4_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 3.53/3.74  cnf(c_0_19, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 3.53/3.74  cnf(c_0_20, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 3.53/3.74  cnf(c_0_21, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 3.53/3.74  cnf(c_0_22, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 3.53/3.74  cnf(c_0_23, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 3.53/3.74  cnf(c_0_24, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 3.53/3.74  fof(c_0_25, negated_conjecture, ~(![X1, X2]:(k2_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)=>X1=X2)), inference(assume_negation,[status(cth)],[t13_zfmisc_1])).
% 3.53/3.74  fof(c_0_26, plain, ![X34, X35]:k2_xboole_0(X34,X35)=k5_xboole_0(X34,k4_xboole_0(X35,X34)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 3.53/3.74  cnf(c_0_27, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 3.53/3.74  cnf(c_0_28, plain, (r2_hidden(X1,X4)|r2_hidden(X1,X3)|X4!=k5_xboole_0(X2,k3_xboole_0(X2,X3))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_18, c_0_19])).
% 3.53/3.74  cnf(c_0_29, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k3_enumset1(X2,X2,X2,X2,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_21]), c_0_22]), c_0_23]), c_0_24])).
% 3.53/3.74  fof(c_0_30, plain, ![X24, X25, X26]:(((~r2_hidden(X24,X25)|~r2_hidden(X24,X26)|~r2_hidden(X24,k5_xboole_0(X25,X26)))&(r2_hidden(X24,X25)|r2_hidden(X24,X26)|~r2_hidden(X24,k5_xboole_0(X25,X26))))&((~r2_hidden(X24,X25)|r2_hidden(X24,X26)|r2_hidden(X24,k5_xboole_0(X25,X26)))&(~r2_hidden(X24,X26)|r2_hidden(X24,X25)|r2_hidden(X24,k5_xboole_0(X25,X26))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).
% 3.53/3.74  fof(c_0_31, negated_conjecture, (k2_xboole_0(k1_tarski(esk4_0),k1_tarski(esk5_0))=k1_tarski(esk4_0)&esk4_0!=esk5_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).
% 3.53/3.74  cnf(c_0_32, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 3.53/3.74  cnf(c_0_33, plain, (X3!=k5_xboole_0(X4,k3_xboole_0(X4,X2))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_27, c_0_19])).
% 3.53/3.74  fof(c_0_34, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 3.53/3.74  cnf(c_0_35, plain, (r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))|r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_28])).
% 3.53/3.74  cnf(c_0_36, plain, (r2_hidden(X1,k3_enumset1(X1,X1,X1,X1,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_29])])).
% 3.53/3.74  cnf(c_0_37, plain, (r2_hidden(X1,X3)|r2_hidden(X1,k5_xboole_0(X2,X3))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 3.53/3.74  cnf(c_0_38, negated_conjecture, (k2_xboole_0(k1_tarski(esk4_0),k1_tarski(esk5_0))=k1_tarski(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 3.53/3.74  cnf(c_0_39, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[c_0_32, c_0_19])).
% 3.53/3.74  cnf(c_0_40, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_33])).
% 3.53/3.74  cnf(c_0_41, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 3.53/3.74  cnf(c_0_42, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r2_hidden(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 3.53/3.74  cnf(c_0_43, plain, (r2_hidden(X1,k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),X2)))|r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 3.53/3.74  cnf(c_0_44, plain, (r2_hidden(X1,X3)|r2_hidden(X1,k5_xboole_0(X3,X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 3.53/3.74  cnf(c_0_45, plain, (r2_hidden(X1,k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),X2))|r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_37, c_0_36])).
% 3.53/3.74  cnf(c_0_46, negated_conjecture, (k5_xboole_0(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k5_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))))=k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_21]), c_0_21]), c_0_21]), c_0_22]), c_0_22]), c_0_22]), c_0_39]), c_0_23]), c_0_23]), c_0_23]), c_0_23]), c_0_23]), c_0_24]), c_0_24]), c_0_24]), c_0_24]), c_0_24])).
% 3.53/3.74  cnf(c_0_47, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X3,X2)))|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 3.53/3.74  cnf(c_0_48, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 3.53/3.74  cnf(c_0_49, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_36])])).
% 3.53/3.74  cnf(c_0_50, plain, (r2_hidden(X1,k5_xboole_0(X2,k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),X3)))|r2_hidden(X1,X3)|r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 3.53/3.74  cnf(c_0_51, negated_conjecture, (k5_xboole_0(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k5_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_xboole_0(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))))=k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)), inference(rw,[status(thm)],[c_0_46, c_0_41])).
% 3.53/3.74  cnf(c_0_52, plain, (r2_hidden(X1,k3_xboole_0(X2,k3_enumset1(X1,X1,X1,X1,X1)))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_47, c_0_45])).
% 3.53/3.74  cnf(c_0_53, plain, (X1=X3|X2!=k3_enumset1(X3,X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_21]), c_0_22]), c_0_23]), c_0_24])).
% 3.53/3.74  cnf(c_0_54, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X2,k3_enumset1(X1,X1,X1,X1,X1)))), inference(spm,[status(thm)],[c_0_49, c_0_41])).
% 3.53/3.74  cnf(c_0_55, negated_conjecture, (r2_hidden(esk5_0,k3_xboole_0(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52])).
% 3.53/3.74  cnf(c_0_56, plain, (X1=X2|~r2_hidden(X1,k3_enumset1(X2,X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_53])).
% 3.53/3.74  cnf(c_0_57, negated_conjecture, (r2_hidden(esk5_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 3.53/3.74  cnf(c_0_58, negated_conjecture, (esk4_0!=esk5_0), inference(split_conjunct,[status(thm)],[c_0_31])).
% 3.53/3.74  cnf(c_0_59, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_58]), ['proof']).
% 3.53/3.74  # SZS output end CNFRefutation
% 3.53/3.74  # Proof object total steps             : 60
% 3.53/3.74  # Proof object clause steps            : 37
% 3.53/3.74  # Proof object formula steps           : 23
% 3.53/3.74  # Proof object conjectures             : 10
% 3.53/3.74  # Proof object clause conjectures      : 7
% 3.53/3.74  # Proof object formula conjectures     : 3
% 3.53/3.74  # Proof object initial clauses used    : 16
% 3.53/3.74  # Proof object initial formulas used   : 11
% 3.53/3.74  # Proof object generating inferences   : 10
% 3.53/3.74  # Proof object simplifying inferences  : 38
% 3.53/3.74  # Training examples: 0 positive, 0 negative
% 3.53/3.74  # Parsed axioms                        : 17
% 3.53/3.74  # Removed by relevancy pruning/SinE    : 0
% 3.53/3.74  # Initial clauses                      : 31
% 3.53/3.74  # Removed in clause preprocessing      : 6
% 3.53/3.74  # Initial clauses in saturation        : 25
% 3.53/3.74  # Processed clauses                    : 6878
% 3.53/3.74  # ...of these trivial                  : 55
% 3.53/3.74  # ...subsumed                          : 5869
% 3.53/3.74  # ...remaining for further processing  : 954
% 3.53/3.74  # Other redundant clauses eliminated   : 207
% 3.53/3.74  # Clauses deleted for lack of memory   : 0
% 3.53/3.74  # Backward-subsumed                    : 74
% 3.53/3.74  # Backward-rewritten                   : 63
% 3.53/3.74  # Generated clauses                    : 342382
% 3.53/3.74  # ...of the previous two non-trivial   : 322082
% 3.53/3.74  # Contextual simplify-reflections      : 17
% 3.53/3.74  # Paramodulations                      : 342117
% 3.53/3.74  # Factorizations                       : 59
% 3.53/3.74  # Equation resolutions                 : 207
% 3.53/3.74  # Propositional unsat checks           : 0
% 3.53/3.74  #    Propositional check models        : 0
% 3.53/3.74  #    Propositional check unsatisfiable : 0
% 3.53/3.74  #    Propositional clauses             : 0
% 3.53/3.74  #    Propositional clauses after purity: 0
% 3.53/3.74  #    Propositional unsat core size     : 0
% 3.53/3.74  #    Propositional preprocessing time  : 0.000
% 3.53/3.74  #    Propositional encoding time       : 0.000
% 3.53/3.74  #    Propositional solver time         : 0.000
% 3.53/3.74  #    Success case prop preproc time    : 0.000
% 3.53/3.74  #    Success case prop encoding time   : 0.000
% 3.53/3.74  #    Success case prop solver time     : 0.000
% 3.53/3.74  # Current number of processed clauses  : 787
% 3.53/3.74  #    Positive orientable unit clauses  : 40
% 3.53/3.74  #    Positive unorientable unit clauses: 2
% 3.53/3.74  #    Negative unit clauses             : 6
% 3.53/3.74  #    Non-unit-clauses                  : 739
% 3.53/3.74  # Current number of unprocessed clauses: 313709
% 3.53/3.74  # ...number of literals in the above   : 1599572
% 3.53/3.74  # Current number of archived formulas  : 0
% 3.53/3.74  # Current number of archived clauses   : 168
% 3.53/3.74  # Clause-clause subsumption calls (NU) : 102408
% 3.53/3.74  # Rec. Clause-clause subsumption calls : 57279
% 3.53/3.74  # Non-unit clause-clause subsumptions  : 4353
% 3.53/3.74  # Unit Clause-clause subsumption calls : 1005
% 3.53/3.74  # Rewrite failures with RHS unbound    : 851
% 3.53/3.74  # BW rewrite match attempts            : 452
% 3.53/3.74  # BW rewrite match successes           : 62
% 3.53/3.74  # Condensation attempts                : 0
% 3.53/3.74  # Condensation successes               : 0
% 3.53/3.74  # Termbank termtop insertions          : 13337905
% 3.53/3.76  
% 3.53/3.76  # -------------------------------------------------
% 3.53/3.76  # User time                : 3.278 s
% 3.53/3.76  # System time              : 0.141 s
% 3.53/3.76  # Total time               : 3.419 s
% 3.53/3.76  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
