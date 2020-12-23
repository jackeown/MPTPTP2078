%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:59:01 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 127 expanded)
%              Number of clauses        :   30 (  52 expanded)
%              Number of leaves         :   12 (  36 expanded)
%              Depth                    :   10
%              Number of atoms          :  117 ( 214 expanded)
%              Number of equality atoms :   33 ( 102 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :    9 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_mcart_1,conjecture,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(k1_tarski(X2),X3))
     => ( k1_mcart_1(X1) = X2
        & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_mcart_1)).

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

fof(t10_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
     => ( r2_hidden(k1_mcart_1(X1),X2)
        & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t140_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X1)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_zfmisc_1)).

fof(t64_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))
    <=> ( r2_hidden(X1,X2)
        & X1 != X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t136_zfmisc_1,axiom,(
    ! [X1] :
    ? [X2] :
      ( r2_hidden(X1,X2)
      & ! [X3,X4] :
          ( ( r2_hidden(X3,X2)
            & r1_tarski(X4,X3) )
         => r2_hidden(X4,X2) )
      & ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(k1_zfmisc_1(X3),X2) )
      & ! [X3] :
          ~ ( r1_tarski(X3,X2)
            & ~ r2_tarski(X3,X2)
            & ~ r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t136_zfmisc_1)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r2_hidden(X1,k2_zfmisc_1(k1_tarski(X2),X3))
       => ( k1_mcart_1(X1) = X2
          & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    inference(assume_negation,[status(cth)],[t12_mcart_1])).

fof(c_0_13,negated_conjecture,
    ( r2_hidden(esk3_0,k2_zfmisc_1(k1_tarski(esk4_0),esk5_0))
    & ( k1_mcart_1(esk3_0) != esk4_0
      | ~ r2_hidden(k2_mcart_1(esk3_0),esk5_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

fof(c_0_14,plain,(
    ! [X15] : k2_tarski(X15,X15) = k1_tarski(X15) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_15,plain,(
    ! [X16,X17] : k1_enumset1(X16,X16,X17) = k2_tarski(X16,X17) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_16,plain,(
    ! [X18,X19,X20] : k2_enumset1(X18,X18,X19,X20) = k1_enumset1(X18,X19,X20) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_17,plain,(
    ! [X21,X22,X23,X24] : k3_enumset1(X21,X21,X22,X23,X24) = k2_enumset1(X21,X22,X23,X24) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_18,plain,(
    ! [X36,X37,X38] :
      ( ( r2_hidden(k1_mcart_1(X36),X37)
        | ~ r2_hidden(X36,k2_zfmisc_1(X37,X38)) )
      & ( r2_hidden(k2_mcart_1(X36),X38)
        | ~ r2_hidden(X36,k2_zfmisc_1(X37,X38)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(esk3_0,k2_zfmisc_1(k1_tarski(esk4_0),esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_24,plain,(
    ! [X7,X8,X9,X10,X11] :
      ( ( ~ r1_tarski(X7,X8)
        | ~ r2_hidden(X9,X7)
        | r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_2(X10,X11),X10)
        | r1_tarski(X10,X11) )
      & ( ~ r2_hidden(esk1_2(X10,X11),X11)
        | r1_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_25,plain,
    ( r2_hidden(k1_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk3_0,k2_zfmisc_1(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),esk5_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_22]),c_0_23])).

fof(c_0_27,plain,(
    ! [X31,X32] :
      ( ~ r2_hidden(X31,X32)
      | k2_xboole_0(k4_xboole_0(X32,k1_tarski(X31)),k1_tarski(X31)) = X32 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t140_zfmisc_1])])).

fof(c_0_28,plain,(
    ! [X33,X34,X35] :
      ( ( r2_hidden(X33,X34)
        | ~ r2_hidden(X33,k4_xboole_0(X34,k1_tarski(X35))) )
      & ( X33 != X35
        | ~ r2_hidden(X33,k4_xboole_0(X34,k1_tarski(X35))) )
      & ( ~ r2_hidden(X33,X34)
        | X33 = X35
        | r2_hidden(X33,k4_xboole_0(X34,k1_tarski(X35))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).

cnf(c_0_29,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk3_0),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

fof(c_0_31,plain,(
    ! [X13,X14] : r1_tarski(X13,k2_xboole_0(X13,X14)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_32,plain,
    ( k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X1)) = X2
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_33,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_34,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk3_0),X1)
    | ~ r1_tarski(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_37,plain,
    ( k2_xboole_0(k4_xboole_0(X2,k3_enumset1(X1,X1,X1,X1,X1)),k3_enumset1(X1,X1,X1,X1,X1)) = X2
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_20]),c_0_20]),c_0_21]),c_0_21]),c_0_22]),c_0_22]),c_0_23]),c_0_23])).

cnf(c_0_38,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_39,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k4_xboole_0(X3,k3_enumset1(X2,X2,X2,X2,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_20]),c_0_21]),c_0_22]),c_0_23])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk3_0),k2_xboole_0(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),X1)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_41,plain,
    ( k2_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k4_xboole_0(X2,k3_enumset1(X1,X1,X1,X1,X1))) = X2
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_42,plain,
    ( X1 = X3
    | r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_43,plain,(
    ! [X25,X27,X28,X29,X30] :
      ( r2_hidden(X25,esk2_1(X25))
      & ( ~ r2_hidden(X27,esk2_1(X25))
        | ~ r1_tarski(X28,X27)
        | r2_hidden(X28,esk2_1(X25)) )
      & ( ~ r2_hidden(X29,esk2_1(X25))
        | r2_hidden(k1_zfmisc_1(X29),esk2_1(X25)) )
      & ( ~ r1_tarski(X30,esk2_1(X25))
        | r2_tarski(X30,esk2_1(X25))
        | r2_hidden(X30,esk2_1(X25)) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t136_zfmisc_1])])])])])).

cnf(c_0_44,plain,
    ( r2_hidden(k2_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_45,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,k3_enumset1(X1,X1,X1,X1,X1))) ),
    inference(er,[status(thm)],[c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk3_0),X1)
    | ~ r2_hidden(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_47,plain,
    ( X1 = X3
    | r2_hidden(X1,k4_xboole_0(X2,k3_enumset1(X3,X3,X3,X3,X3)))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_20]),c_0_21]),c_0_22]),c_0_23])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,esk2_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_49,negated_conjecture,
    ( k1_mcart_1(esk3_0) != esk4_0
    | ~ r2_hidden(k2_mcart_1(esk3_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(k2_mcart_1(esk3_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_26])).

cnf(c_0_51,negated_conjecture,
    ( ~ r2_hidden(esk4_0,k4_xboole_0(X1,k3_enumset1(k1_mcart_1(esk3_0),k1_mcart_1(esk3_0),k1_mcart_1(esk3_0),k1_mcart_1(esk3_0),k1_mcart_1(esk3_0)))) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_52,plain,
    ( X1 = X2
    | r2_hidden(X1,k4_xboole_0(esk2_1(X1),k3_enumset1(X2,X2,X2,X2,X2))) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_53,negated_conjecture,
    ( k1_mcart_1(esk3_0) != esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_50])])).

cnf(c_0_54,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:33:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.12/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.12/0.38  #
% 0.12/0.38  # Preprocessing time       : 0.027 s
% 0.12/0.38  # Presaturation interreduction done
% 0.12/0.38  
% 0.12/0.38  # Proof found!
% 0.12/0.38  # SZS status Theorem
% 0.12/0.38  # SZS output start CNFRefutation
% 0.12/0.38  fof(t12_mcart_1, conjecture, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(k1_tarski(X2),X3))=>(k1_mcart_1(X1)=X2&r2_hidden(k2_mcart_1(X1),X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_mcart_1)).
% 0.12/0.38  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.12/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.12/0.38  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.12/0.38  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.12/0.38  fof(t10_mcart_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(X2,X3))=>(r2_hidden(k1_mcart_1(X1),X2)&r2_hidden(k2_mcart_1(X1),X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 0.12/0.38  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.12/0.38  fof(t140_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X1))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t140_zfmisc_1)).
% 0.12/0.38  fof(t64_zfmisc_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))<=>(r2_hidden(X1,X2)&X1!=X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 0.12/0.38  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.12/0.38  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.12/0.38  fof(t136_zfmisc_1, axiom, ![X1]:?[X2]:(((r2_hidden(X1,X2)&![X3, X4]:((r2_hidden(X3,X2)&r1_tarski(X4,X3))=>r2_hidden(X4,X2)))&![X3]:(r2_hidden(X3,X2)=>r2_hidden(k1_zfmisc_1(X3),X2)))&![X3]:~(((r1_tarski(X3,X2)&~(r2_tarski(X3,X2)))&~(r2_hidden(X3,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t136_zfmisc_1)).
% 0.12/0.38  fof(c_0_12, negated_conjecture, ~(![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(k1_tarski(X2),X3))=>(k1_mcart_1(X1)=X2&r2_hidden(k2_mcart_1(X1),X3)))), inference(assume_negation,[status(cth)],[t12_mcart_1])).
% 0.12/0.38  fof(c_0_13, negated_conjecture, (r2_hidden(esk3_0,k2_zfmisc_1(k1_tarski(esk4_0),esk5_0))&(k1_mcart_1(esk3_0)!=esk4_0|~r2_hidden(k2_mcart_1(esk3_0),esk5_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 0.12/0.38  fof(c_0_14, plain, ![X15]:k2_tarski(X15,X15)=k1_tarski(X15), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.12/0.38  fof(c_0_15, plain, ![X16, X17]:k1_enumset1(X16,X16,X17)=k2_tarski(X16,X17), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.12/0.38  fof(c_0_16, plain, ![X18, X19, X20]:k2_enumset1(X18,X18,X19,X20)=k1_enumset1(X18,X19,X20), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.12/0.38  fof(c_0_17, plain, ![X21, X22, X23, X24]:k3_enumset1(X21,X21,X22,X23,X24)=k2_enumset1(X21,X22,X23,X24), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.12/0.38  fof(c_0_18, plain, ![X36, X37, X38]:((r2_hidden(k1_mcart_1(X36),X37)|~r2_hidden(X36,k2_zfmisc_1(X37,X38)))&(r2_hidden(k2_mcart_1(X36),X38)|~r2_hidden(X36,k2_zfmisc_1(X37,X38)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).
% 0.12/0.38  cnf(c_0_19, negated_conjecture, (r2_hidden(esk3_0,k2_zfmisc_1(k1_tarski(esk4_0),esk5_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.38  cnf(c_0_20, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.38  cnf(c_0_21, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.38  cnf(c_0_22, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.38  cnf(c_0_23, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.38  fof(c_0_24, plain, ![X7, X8, X9, X10, X11]:((~r1_tarski(X7,X8)|(~r2_hidden(X9,X7)|r2_hidden(X9,X8)))&((r2_hidden(esk1_2(X10,X11),X10)|r1_tarski(X10,X11))&(~r2_hidden(esk1_2(X10,X11),X11)|r1_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.12/0.38  cnf(c_0_25, plain, (r2_hidden(k1_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.12/0.38  cnf(c_0_26, negated_conjecture, (r2_hidden(esk3_0,k2_zfmisc_1(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),esk5_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_20]), c_0_21]), c_0_22]), c_0_23])).
% 0.12/0.38  fof(c_0_27, plain, ![X31, X32]:(~r2_hidden(X31,X32)|k2_xboole_0(k4_xboole_0(X32,k1_tarski(X31)),k1_tarski(X31))=X32), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t140_zfmisc_1])])).
% 0.12/0.38  fof(c_0_28, plain, ![X33, X34, X35]:(((r2_hidden(X33,X34)|~r2_hidden(X33,k4_xboole_0(X34,k1_tarski(X35))))&(X33!=X35|~r2_hidden(X33,k4_xboole_0(X34,k1_tarski(X35)))))&(~r2_hidden(X33,X34)|X33=X35|r2_hidden(X33,k4_xboole_0(X34,k1_tarski(X35))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).
% 0.12/0.38  cnf(c_0_29, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.12/0.38  cnf(c_0_30, negated_conjecture, (r2_hidden(k1_mcart_1(esk3_0),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.12/0.38  fof(c_0_31, plain, ![X13, X14]:r1_tarski(X13,k2_xboole_0(X13,X14)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.12/0.38  cnf(c_0_32, plain, (k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X1))=X2|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.12/0.38  fof(c_0_33, plain, ![X5, X6]:k2_xboole_0(X5,X6)=k2_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.12/0.38  cnf(c_0_34, plain, (X1!=X2|~r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.12/0.38  cnf(c_0_35, negated_conjecture, (r2_hidden(k1_mcart_1(esk3_0),X1)|~r1_tarski(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),X1)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.12/0.38  cnf(c_0_36, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.12/0.38  cnf(c_0_37, plain, (k2_xboole_0(k4_xboole_0(X2,k3_enumset1(X1,X1,X1,X1,X1)),k3_enumset1(X1,X1,X1,X1,X1))=X2|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_20]), c_0_20]), c_0_21]), c_0_21]), c_0_22]), c_0_22]), c_0_23]), c_0_23])).
% 0.12/0.38  cnf(c_0_38, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.12/0.38  cnf(c_0_39, plain, (X1!=X2|~r2_hidden(X1,k4_xboole_0(X3,k3_enumset1(X2,X2,X2,X2,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_20]), c_0_21]), c_0_22]), c_0_23])).
% 0.12/0.38  cnf(c_0_40, negated_conjecture, (r2_hidden(k1_mcart_1(esk3_0),k2_xboole_0(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),X1))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.12/0.38  cnf(c_0_41, plain, (k2_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k4_xboole_0(X2,k3_enumset1(X1,X1,X1,X1,X1)))=X2|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_37, c_0_38])).
% 0.12/0.38  cnf(c_0_42, plain, (X1=X3|r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.12/0.38  fof(c_0_43, plain, ![X25, X27, X28, X29, X30]:(((r2_hidden(X25,esk2_1(X25))&(~r2_hidden(X27,esk2_1(X25))|~r1_tarski(X28,X27)|r2_hidden(X28,esk2_1(X25))))&(~r2_hidden(X29,esk2_1(X25))|r2_hidden(k1_zfmisc_1(X29),esk2_1(X25))))&(~r1_tarski(X30,esk2_1(X25))|r2_tarski(X30,esk2_1(X25))|r2_hidden(X30,esk2_1(X25)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t136_zfmisc_1])])])])])).
% 0.12/0.38  cnf(c_0_44, plain, (r2_hidden(k2_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.12/0.38  cnf(c_0_45, plain, (~r2_hidden(X1,k4_xboole_0(X2,k3_enumset1(X1,X1,X1,X1,X1)))), inference(er,[status(thm)],[c_0_39])).
% 0.12/0.38  cnf(c_0_46, negated_conjecture, (r2_hidden(k1_mcart_1(esk3_0),X1)|~r2_hidden(esk4_0,X1)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.12/0.38  cnf(c_0_47, plain, (X1=X3|r2_hidden(X1,k4_xboole_0(X2,k3_enumset1(X3,X3,X3,X3,X3)))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_20]), c_0_21]), c_0_22]), c_0_23])).
% 0.12/0.38  cnf(c_0_48, plain, (r2_hidden(X1,esk2_1(X1))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.12/0.38  cnf(c_0_49, negated_conjecture, (k1_mcart_1(esk3_0)!=esk4_0|~r2_hidden(k2_mcart_1(esk3_0),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.38  cnf(c_0_50, negated_conjecture, (r2_hidden(k2_mcart_1(esk3_0),esk5_0)), inference(spm,[status(thm)],[c_0_44, c_0_26])).
% 0.12/0.38  cnf(c_0_51, negated_conjecture, (~r2_hidden(esk4_0,k4_xboole_0(X1,k3_enumset1(k1_mcart_1(esk3_0),k1_mcart_1(esk3_0),k1_mcart_1(esk3_0),k1_mcart_1(esk3_0),k1_mcart_1(esk3_0))))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.12/0.38  cnf(c_0_52, plain, (X1=X2|r2_hidden(X1,k4_xboole_0(esk2_1(X1),k3_enumset1(X2,X2,X2,X2,X2)))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.12/0.38  cnf(c_0_53, negated_conjecture, (k1_mcart_1(esk3_0)!=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_50])])).
% 0.12/0.38  cnf(c_0_54, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53]), ['proof']).
% 0.12/0.38  # SZS output end CNFRefutation
% 0.12/0.38  # Proof object total steps             : 55
% 0.12/0.38  # Proof object clause steps            : 30
% 0.12/0.38  # Proof object formula steps           : 25
% 0.12/0.38  # Proof object conjectures             : 14
% 0.12/0.38  # Proof object clause conjectures      : 11
% 0.12/0.38  # Proof object formula conjectures     : 3
% 0.12/0.38  # Proof object initial clauses used    : 15
% 0.12/0.38  # Proof object initial formulas used   : 12
% 0.12/0.38  # Proof object generating inferences   : 8
% 0.12/0.38  # Proof object simplifying inferences  : 25
% 0.12/0.38  # Training examples: 0 positive, 0 negative
% 0.12/0.38  # Parsed axioms                        : 12
% 0.12/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.38  # Initial clauses                      : 21
% 0.12/0.38  # Removed in clause preprocessing      : 4
% 0.12/0.38  # Initial clauses in saturation        : 17
% 0.12/0.38  # Processed clauses                    : 226
% 0.12/0.38  # ...of these trivial                  : 21
% 0.12/0.38  # ...subsumed                          : 62
% 0.12/0.38  # ...remaining for further processing  : 143
% 0.12/0.38  # Other redundant clauses eliminated   : 1
% 0.12/0.38  # Clauses deleted for lack of memory   : 0
% 0.12/0.38  # Backward-subsumed                    : 0
% 0.12/0.38  # Backward-rewritten                   : 1
% 0.12/0.38  # Generated clauses                    : 448
% 0.12/0.38  # ...of the previous two non-trivial   : 400
% 0.12/0.38  # Contextual simplify-reflections      : 0
% 0.12/0.38  # Paramodulations                      : 447
% 0.12/0.38  # Factorizations                       : 0
% 0.12/0.38  # Equation resolutions                 : 1
% 0.12/0.38  # Propositional unsat checks           : 0
% 0.12/0.38  #    Propositional check models        : 0
% 0.12/0.38  #    Propositional check unsatisfiable : 0
% 0.12/0.38  #    Propositional clauses             : 0
% 0.12/0.38  #    Propositional clauses after purity: 0
% 0.12/0.38  #    Propositional unsat core size     : 0
% 0.12/0.38  #    Propositional preprocessing time  : 0.000
% 0.12/0.38  #    Propositional encoding time       : 0.000
% 0.12/0.38  #    Propositional solver time         : 0.000
% 0.12/0.38  #    Success case prop preproc time    : 0.000
% 0.12/0.38  #    Success case prop encoding time   : 0.000
% 0.12/0.38  #    Success case prop solver time     : 0.000
% 0.12/0.38  # Current number of processed clauses  : 124
% 0.12/0.38  #    Positive orientable unit clauses  : 32
% 0.12/0.38  #    Positive unorientable unit clauses: 1
% 0.12/0.38  #    Negative unit clauses             : 7
% 0.12/0.38  #    Non-unit-clauses                  : 84
% 0.12/0.38  # Current number of unprocessed clauses: 207
% 0.12/0.38  # ...number of literals in the above   : 436
% 0.12/0.38  # Current number of archived formulas  : 0
% 0.12/0.38  # Current number of archived clauses   : 22
% 0.12/0.38  # Clause-clause subsumption calls (NU) : 1332
% 0.12/0.38  # Rec. Clause-clause subsumption calls : 1093
% 0.12/0.38  # Non-unit clause-clause subsumptions  : 62
% 0.12/0.38  # Unit Clause-clause subsumption calls : 13
% 0.12/0.38  # Rewrite failures with RHS unbound    : 0
% 0.12/0.38  # BW rewrite match attempts            : 18
% 0.12/0.38  # BW rewrite match successes           : 3
% 0.12/0.38  # Condensation attempts                : 0
% 0.12/0.38  # Condensation successes               : 0
% 0.12/0.38  # Termbank termtop insertions          : 7184
% 0.12/0.38  
% 0.12/0.38  # -------------------------------------------------
% 0.12/0.38  # User time                : 0.040 s
% 0.12/0.38  # System time              : 0.004 s
% 0.12/0.38  # Total time               : 0.044 s
% 0.12/0.38  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
