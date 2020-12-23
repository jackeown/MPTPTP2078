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
% DateTime   : Thu Dec  3 10:44:53 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 132 expanded)
%              Number of clauses        :   39 (  59 expanded)
%              Number of leaves         :   11 (  33 expanded)
%              Depth                    :   18
%              Number of atoms          :  145 ( 330 expanded)
%              Number of equality atoms :   33 (  48 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t149_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))
        & r2_hidden(X4,X3)
        & r1_xboole_0(X3,X2) )
     => r1_xboole_0(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t75_xboole_1,axiom,(
    ! [X1,X2] :
      ~ ( ~ r1_xboole_0(X1,X2)
        & r1_xboole_0(k3_xboole_0(X1,X2),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_xboole_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t70_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ~ ( ~ r1_xboole_0(X1,k2_xboole_0(X2,X3))
          & r1_xboole_0(X1,X2)
          & r1_xboole_0(X1,X3) )
      & ~ ( ~ ( r1_xboole_0(X1,X2)
              & r1_xboole_0(X1,X3) )
          & r1_xboole_0(X1,k2_xboole_0(X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))
          & r2_hidden(X4,X3)
          & r1_xboole_0(X3,X2) )
       => r1_xboole_0(k2_xboole_0(X1,X3),X2) ) ),
    inference(assume_negation,[status(cth)],[t149_zfmisc_1])).

fof(c_0_12,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk4_0,esk5_0),k1_tarski(esk7_0))
    & r2_hidden(esk7_0,esk6_0)
    & r1_xboole_0(esk6_0,esk5_0)
    & ~ r1_xboole_0(k2_xboole_0(esk4_0,esk6_0),esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

fof(c_0_13,plain,(
    ! [X33] : k2_tarski(X33,X33) = k1_tarski(X33) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_14,plain,(
    ! [X34,X35] : k1_enumset1(X34,X34,X35) = k2_tarski(X34,X35) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_15,plain,(
    ! [X36,X37,X38] : k2_enumset1(X36,X36,X37,X38) = k1_enumset1(X36,X37,X38) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_16,plain,(
    ! [X26,X27,X28,X29,X30,X31] :
      ( ( ~ r2_hidden(X28,X27)
        | X28 = X26
        | X27 != k1_tarski(X26) )
      & ( X29 != X26
        | r2_hidden(X29,X27)
        | X27 != k1_tarski(X26) )
      & ( ~ r2_hidden(esk3_2(X30,X31),X31)
        | esk3_2(X30,X31) != X30
        | X31 = k1_tarski(X30) )
      & ( r2_hidden(esk3_2(X30,X31),X31)
        | esk3_2(X30,X31) = X30
        | X31 = k1_tarski(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_17,plain,(
    ! [X7,X8,X9,X10,X11] :
      ( ( ~ r1_tarski(X7,X8)
        | ~ r2_hidden(X9,X7)
        | r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_2(X10,X11),X10)
        | r1_tarski(X10,X11) )
      & ( ~ r2_hidden(esk1_2(X10,X11),X11)
        | r1_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_18,plain,(
    ! [X15,X16,X18,X19,X20] :
      ( ( r2_hidden(esk2_2(X15,X16),X15)
        | r1_xboole_0(X15,X16) )
      & ( r2_hidden(esk2_2(X15,X16),X16)
        | r1_xboole_0(X15,X16) )
      & ( ~ r2_hidden(X20,X18)
        | ~ r2_hidden(X20,X19)
        | ~ r1_xboole_0(X18,X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_19,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk4_0,esk5_0),k1_tarski(esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_23,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_24,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk4_0,esk5_0),k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_22])).

cnf(c_0_28,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( X1 = X3
    | X2 != k2_enumset1(X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_20]),c_0_21]),c_0_22])).

cnf(c_0_30,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk2_2(X1,X2),X3)
    | ~ r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk5_0,esk4_0),k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0)) ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

fof(c_0_32,plain,(
    ! [X24,X25] :
      ( r1_xboole_0(X24,X25)
      | ~ r1_xboole_0(k3_xboole_0(X24,X25),X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t75_xboole_1])])])).

fof(c_0_33,plain,(
    ! [X13,X14] :
      ( ~ r1_xboole_0(X13,X14)
      | r1_xboole_0(X14,X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_34,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k2_enumset1(X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_35,negated_conjecture,
    ( r1_xboole_0(X1,k3_xboole_0(esk5_0,esk4_0))
    | r2_hidden(esk2_2(X1,k3_xboole_0(esk5_0,esk4_0)),k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_36,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(k3_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_37,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_38,negated_conjecture,
    ( esk2_2(X1,k3_xboole_0(esk5_0,esk4_0)) = esk7_0
    | r1_xboole_0(X1,k3_xboole_0(esk5_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

fof(c_0_39,plain,(
    ! [X21,X22,X23] :
      ( ( r1_xboole_0(X21,k2_xboole_0(X22,X23))
        | ~ r1_xboole_0(X21,X22)
        | ~ r1_xboole_0(X21,X23) )
      & ( r1_xboole_0(X21,X22)
        | ~ r1_xboole_0(X21,k2_xboole_0(X22,X23)) )
      & ( r1_xboole_0(X21,X23)
        | ~ r1_xboole_0(X21,k2_xboole_0(X22,X23)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).

cnf(c_0_40,negated_conjecture,
    ( r1_xboole_0(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_41,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(k3_xboole_0(X2,X1),X2) ),
    inference(spm,[status(thm)],[c_0_36,c_0_28])).

cnf(c_0_42,negated_conjecture,
    ( esk2_2(X1,k3_xboole_0(esk5_0,esk4_0)) = esk7_0
    | r1_xboole_0(k3_xboole_0(esk5_0,esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_43,plain,
    ( r1_xboole_0(X1,k2_xboole_0(X2,X3))
    | ~ r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( r1_xboole_0(esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_40])).

cnf(c_0_45,negated_conjecture,
    ( esk2_2(esk5_0,k3_xboole_0(esk5_0,esk4_0)) = esk7_0
    | r1_xboole_0(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_46,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_47,negated_conjecture,
    ( r1_xboole_0(esk5_0,k2_xboole_0(X1,esk6_0))
    | ~ r1_xboole_0(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_48,negated_conjecture,
    ( esk2_2(esk5_0,k3_xboole_0(esk5_0,esk4_0)) = esk7_0
    | r1_xboole_0(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_45])).

cnf(c_0_49,negated_conjecture,
    ( ~ r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_40])).

cnf(c_0_50,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_51,negated_conjecture,
    ( esk2_2(esk5_0,k3_xboole_0(esk5_0,esk4_0)) = esk7_0
    | r1_xboole_0(esk5_0,k2_xboole_0(esk4_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_52,negated_conjecture,
    ( ~ r1_xboole_0(k2_xboole_0(esk4_0,esk6_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_53,negated_conjecture,
    ( r1_xboole_0(esk5_0,X1)
    | ~ r2_hidden(esk2_2(esk5_0,X1),esk6_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_54,negated_conjecture,
    ( esk2_2(esk5_0,k3_xboole_0(esk5_0,esk4_0)) = esk7_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_51]),c_0_52])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(esk7_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_56,negated_conjecture,
    ( r1_xboole_0(esk5_0,k3_xboole_0(esk5_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55])])).

cnf(c_0_57,negated_conjecture,
    ( r1_xboole_0(k3_xboole_0(esk5_0,esk4_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_56])).

cnf(c_0_58,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_57])).

cnf(c_0_59,negated_conjecture,
    ( r1_xboole_0(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_58])).

cnf(c_0_60,negated_conjecture,
    ( r1_xboole_0(esk5_0,k2_xboole_0(esk4_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_59])).

cnf(c_0_61,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_60]),c_0_52]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:22:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.45  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S03EI
% 0.21/0.45  # and selection function SelectLComplex.
% 0.21/0.45  #
% 0.21/0.45  # Preprocessing time       : 0.028 s
% 0.21/0.45  # Presaturation interreduction done
% 0.21/0.45  
% 0.21/0.45  # Proof found!
% 0.21/0.45  # SZS status Theorem
% 0.21/0.45  # SZS output start CNFRefutation
% 0.21/0.45  fof(t149_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(((r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))&r2_hidden(X4,X3))&r1_xboole_0(X3,X2))=>r1_xboole_0(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 0.21/0.45  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.21/0.45  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.21/0.45  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.21/0.45  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 0.21/0.45  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.21/0.45  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.21/0.45  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.21/0.45  fof(t75_xboole_1, axiom, ![X1, X2]:~((~(r1_xboole_0(X1,X2))&r1_xboole_0(k3_xboole_0(X1,X2),X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_xboole_1)).
% 0.21/0.45  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.21/0.45  fof(t70_xboole_1, axiom, ![X1, X2, X3]:(~(((~(r1_xboole_0(X1,k2_xboole_0(X2,X3)))&r1_xboole_0(X1,X2))&r1_xboole_0(X1,X3)))&~((~((r1_xboole_0(X1,X2)&r1_xboole_0(X1,X3)))&r1_xboole_0(X1,k2_xboole_0(X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 0.21/0.45  fof(c_0_11, negated_conjecture, ~(![X1, X2, X3, X4]:(((r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))&r2_hidden(X4,X3))&r1_xboole_0(X3,X2))=>r1_xboole_0(k2_xboole_0(X1,X3),X2))), inference(assume_negation,[status(cth)],[t149_zfmisc_1])).
% 0.21/0.45  fof(c_0_12, negated_conjecture, (((r1_tarski(k3_xboole_0(esk4_0,esk5_0),k1_tarski(esk7_0))&r2_hidden(esk7_0,esk6_0))&r1_xboole_0(esk6_0,esk5_0))&~r1_xboole_0(k2_xboole_0(esk4_0,esk6_0),esk5_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 0.21/0.45  fof(c_0_13, plain, ![X33]:k2_tarski(X33,X33)=k1_tarski(X33), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.21/0.45  fof(c_0_14, plain, ![X34, X35]:k1_enumset1(X34,X34,X35)=k2_tarski(X34,X35), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.21/0.45  fof(c_0_15, plain, ![X36, X37, X38]:k2_enumset1(X36,X36,X37,X38)=k1_enumset1(X36,X37,X38), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.21/0.45  fof(c_0_16, plain, ![X26, X27, X28, X29, X30, X31]:(((~r2_hidden(X28,X27)|X28=X26|X27!=k1_tarski(X26))&(X29!=X26|r2_hidden(X29,X27)|X27!=k1_tarski(X26)))&((~r2_hidden(esk3_2(X30,X31),X31)|esk3_2(X30,X31)!=X30|X31=k1_tarski(X30))&(r2_hidden(esk3_2(X30,X31),X31)|esk3_2(X30,X31)=X30|X31=k1_tarski(X30)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.21/0.45  fof(c_0_17, plain, ![X7, X8, X9, X10, X11]:((~r1_tarski(X7,X8)|(~r2_hidden(X9,X7)|r2_hidden(X9,X8)))&((r2_hidden(esk1_2(X10,X11),X10)|r1_tarski(X10,X11))&(~r2_hidden(esk1_2(X10,X11),X11)|r1_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.21/0.45  fof(c_0_18, plain, ![X15, X16, X18, X19, X20]:(((r2_hidden(esk2_2(X15,X16),X15)|r1_xboole_0(X15,X16))&(r2_hidden(esk2_2(X15,X16),X16)|r1_xboole_0(X15,X16)))&(~r2_hidden(X20,X18)|~r2_hidden(X20,X19)|~r1_xboole_0(X18,X19))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.21/0.45  cnf(c_0_19, negated_conjecture, (r1_tarski(k3_xboole_0(esk4_0,esk5_0),k1_tarski(esk7_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.45  cnf(c_0_20, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.45  cnf(c_0_21, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.45  cnf(c_0_22, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.45  fof(c_0_23, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.21/0.45  cnf(c_0_24, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.45  cnf(c_0_25, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.45  cnf(c_0_26, plain, (r2_hidden(esk2_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.45  cnf(c_0_27, negated_conjecture, (r1_tarski(k3_xboole_0(esk4_0,esk5_0),k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_20]), c_0_21]), c_0_22])).
% 0.21/0.45  cnf(c_0_28, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.45  cnf(c_0_29, plain, (X1=X3|X2!=k2_enumset1(X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_20]), c_0_21]), c_0_22])).
% 0.21/0.45  cnf(c_0_30, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk2_2(X1,X2),X3)|~r1_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.21/0.45  cnf(c_0_31, negated_conjecture, (r1_tarski(k3_xboole_0(esk5_0,esk4_0),k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0))), inference(rw,[status(thm)],[c_0_27, c_0_28])).
% 0.21/0.45  fof(c_0_32, plain, ![X24, X25]:(r1_xboole_0(X24,X25)|~r1_xboole_0(k3_xboole_0(X24,X25),X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t75_xboole_1])])])).
% 0.21/0.45  fof(c_0_33, plain, ![X13, X14]:(~r1_xboole_0(X13,X14)|r1_xboole_0(X14,X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.21/0.45  cnf(c_0_34, plain, (X1=X2|~r2_hidden(X1,k2_enumset1(X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_29])).
% 0.21/0.45  cnf(c_0_35, negated_conjecture, (r1_xboole_0(X1,k3_xboole_0(esk5_0,esk4_0))|r2_hidden(esk2_2(X1,k3_xboole_0(esk5_0,esk4_0)),k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.21/0.45  cnf(c_0_36, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(k3_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.21/0.45  cnf(c_0_37, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.21/0.45  cnf(c_0_38, negated_conjecture, (esk2_2(X1,k3_xboole_0(esk5_0,esk4_0))=esk7_0|r1_xboole_0(X1,k3_xboole_0(esk5_0,esk4_0))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.21/0.45  fof(c_0_39, plain, ![X21, X22, X23]:((r1_xboole_0(X21,k2_xboole_0(X22,X23))|~r1_xboole_0(X21,X22)|~r1_xboole_0(X21,X23))&((r1_xboole_0(X21,X22)|~r1_xboole_0(X21,k2_xboole_0(X22,X23)))&(r1_xboole_0(X21,X23)|~r1_xboole_0(X21,k2_xboole_0(X22,X23))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).
% 0.21/0.45  cnf(c_0_40, negated_conjecture, (r1_xboole_0(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.45  cnf(c_0_41, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(k3_xboole_0(X2,X1),X2)), inference(spm,[status(thm)],[c_0_36, c_0_28])).
% 0.21/0.45  cnf(c_0_42, negated_conjecture, (esk2_2(X1,k3_xboole_0(esk5_0,esk4_0))=esk7_0|r1_xboole_0(k3_xboole_0(esk5_0,esk4_0),X1)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.21/0.45  cnf(c_0_43, plain, (r1_xboole_0(X1,k2_xboole_0(X2,X3))|~r1_xboole_0(X1,X2)|~r1_xboole_0(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.21/0.45  cnf(c_0_44, negated_conjecture, (r1_xboole_0(esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_37, c_0_40])).
% 0.21/0.45  cnf(c_0_45, negated_conjecture, (esk2_2(esk5_0,k3_xboole_0(esk5_0,esk4_0))=esk7_0|r1_xboole_0(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.21/0.45  cnf(c_0_46, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.45  cnf(c_0_47, negated_conjecture, (r1_xboole_0(esk5_0,k2_xboole_0(X1,esk6_0))|~r1_xboole_0(esk5_0,X1)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.21/0.45  cnf(c_0_48, negated_conjecture, (esk2_2(esk5_0,k3_xboole_0(esk5_0,esk4_0))=esk7_0|r1_xboole_0(esk5_0,esk4_0)), inference(spm,[status(thm)],[c_0_37, c_0_45])).
% 0.21/0.45  cnf(c_0_49, negated_conjecture, (~r2_hidden(X1,esk5_0)|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_46, c_0_40])).
% 0.21/0.45  cnf(c_0_50, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.45  cnf(c_0_51, negated_conjecture, (esk2_2(esk5_0,k3_xboole_0(esk5_0,esk4_0))=esk7_0|r1_xboole_0(esk5_0,k2_xboole_0(esk4_0,esk6_0))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.21/0.45  cnf(c_0_52, negated_conjecture, (~r1_xboole_0(k2_xboole_0(esk4_0,esk6_0),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.45  cnf(c_0_53, negated_conjecture, (r1_xboole_0(esk5_0,X1)|~r2_hidden(esk2_2(esk5_0,X1),esk6_0)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.21/0.45  cnf(c_0_54, negated_conjecture, (esk2_2(esk5_0,k3_xboole_0(esk5_0,esk4_0))=esk7_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_51]), c_0_52])).
% 0.21/0.45  cnf(c_0_55, negated_conjecture, (r2_hidden(esk7_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.45  cnf(c_0_56, negated_conjecture, (r1_xboole_0(esk5_0,k3_xboole_0(esk5_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55])])).
% 0.21/0.45  cnf(c_0_57, negated_conjecture, (r1_xboole_0(k3_xboole_0(esk5_0,esk4_0),esk5_0)), inference(spm,[status(thm)],[c_0_37, c_0_56])).
% 0.21/0.45  cnf(c_0_58, negated_conjecture, (r1_xboole_0(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_41, c_0_57])).
% 0.21/0.45  cnf(c_0_59, negated_conjecture, (r1_xboole_0(esk5_0,esk4_0)), inference(spm,[status(thm)],[c_0_37, c_0_58])).
% 0.21/0.45  cnf(c_0_60, negated_conjecture, (r1_xboole_0(esk5_0,k2_xboole_0(esk4_0,esk6_0))), inference(spm,[status(thm)],[c_0_47, c_0_59])).
% 0.21/0.45  cnf(c_0_61, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_60]), c_0_52]), ['proof']).
% 0.21/0.45  # SZS output end CNFRefutation
% 0.21/0.45  # Proof object total steps             : 62
% 0.21/0.45  # Proof object clause steps            : 39
% 0.21/0.45  # Proof object formula steps           : 23
% 0.21/0.45  # Proof object conjectures             : 26
% 0.21/0.45  # Proof object clause conjectures      : 23
% 0.21/0.45  # Proof object formula conjectures     : 3
% 0.21/0.45  # Proof object initial clauses used    : 16
% 0.21/0.45  # Proof object initial formulas used   : 11
% 0.21/0.45  # Proof object generating inferences   : 19
% 0.21/0.45  # Proof object simplifying inferences  : 12
% 0.21/0.45  # Training examples: 0 positive, 0 negative
% 0.21/0.45  # Parsed axioms                        : 11
% 0.21/0.45  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.45  # Initial clauses                      : 23
% 0.21/0.45  # Removed in clause preprocessing      : 3
% 0.21/0.45  # Initial clauses in saturation        : 20
% 0.21/0.45  # Processed clauses                    : 631
% 0.21/0.45  # ...of these trivial                  : 2
% 0.21/0.45  # ...subsumed                          : 103
% 0.21/0.45  # ...remaining for further processing  : 526
% 0.21/0.45  # Other redundant clauses eliminated   : 6
% 0.21/0.45  # Clauses deleted for lack of memory   : 0
% 0.21/0.45  # Backward-subsumed                    : 2
% 0.21/0.45  # Backward-rewritten                   : 9
% 0.21/0.45  # Generated clauses                    : 4059
% 0.21/0.45  # ...of the previous two non-trivial   : 3470
% 0.21/0.45  # Contextual simplify-reflections      : 4
% 0.21/0.45  # Paramodulations                      : 4050
% 0.21/0.45  # Factorizations                       : 4
% 0.21/0.45  # Equation resolutions                 : 6
% 0.21/0.45  # Propositional unsat checks           : 0
% 0.21/0.45  #    Propositional check models        : 0
% 0.21/0.45  #    Propositional check unsatisfiable : 0
% 0.21/0.45  #    Propositional clauses             : 0
% 0.21/0.45  #    Propositional clauses after purity: 0
% 0.21/0.45  #    Propositional unsat core size     : 0
% 0.21/0.45  #    Propositional preprocessing time  : 0.000
% 0.21/0.45  #    Propositional encoding time       : 0.000
% 0.21/0.45  #    Propositional solver time         : 0.000
% 0.21/0.45  #    Success case prop preproc time    : 0.000
% 0.21/0.45  #    Success case prop encoding time   : 0.000
% 0.21/0.45  #    Success case prop solver time     : 0.000
% 0.21/0.45  # Current number of processed clauses  : 493
% 0.21/0.45  #    Positive orientable unit clauses  : 250
% 0.21/0.45  #    Positive unorientable unit clauses: 1
% 0.21/0.45  #    Negative unit clauses             : 1
% 0.21/0.45  #    Non-unit-clauses                  : 241
% 0.21/0.45  # Current number of unprocessed clauses: 2769
% 0.21/0.45  # ...number of literals in the above   : 5174
% 0.21/0.45  # Current number of archived formulas  : 0
% 0.21/0.45  # Current number of archived clauses   : 34
% 0.21/0.45  # Clause-clause subsumption calls (NU) : 12082
% 0.21/0.45  # Rec. Clause-clause subsumption calls : 11992
% 0.21/0.45  # Non-unit clause-clause subsumptions  : 107
% 0.21/0.45  # Unit Clause-clause subsumption calls : 195
% 0.21/0.45  # Rewrite failures with RHS unbound    : 0
% 0.21/0.45  # BW rewrite match attempts            : 1721
% 0.21/0.45  # BW rewrite match successes           : 8
% 0.21/0.45  # Condensation attempts                : 0
% 0.21/0.45  # Condensation successes               : 0
% 0.21/0.45  # Termbank termtop insertions          : 73069
% 0.21/0.45  
% 0.21/0.45  # -------------------------------------------------
% 0.21/0.45  # User time                : 0.098 s
% 0.21/0.45  # System time              : 0.006 s
% 0.21/0.45  # Total time               : 0.104 s
% 0.21/0.45  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
