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
% DateTime   : Thu Dec  3 10:47:14 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 115 expanded)
%              Number of clauses        :   25 (  52 expanded)
%              Number of leaves         :   12 (  35 expanded)
%              Depth                    :   10
%              Number of atoms          :   79 ( 172 expanded)
%              Number of equality atoms :   42 (  91 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t89_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_xboole_1)).

fof(t51_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k3_xboole_0(X1,k1_tarski(X2)) = k1_tarski(X2)
     => r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_zfmisc_1)).

fof(t10_setfam_1,axiom,(
    ! [X1,X2] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & k1_setfam_1(k2_xboole_0(X1,X2)) != k3_xboole_0(k1_setfam_1(X1),k1_setfam_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_setfam_1)).

fof(t4_boole,axiom,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(t12_setfam_1,conjecture,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t11_setfam_1,axiom,(
    ! [X1] : k1_setfam_1(k1_tarski(X1)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

fof(t41_enumset1,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(c_0_10,plain,(
    ! [X9,X10,X12,X13,X14] :
      ( ( r1_xboole_0(X9,X10)
        | r2_hidden(esk1_2(X9,X10),k3_xboole_0(X9,X10)) )
      & ( ~ r2_hidden(X14,k3_xboole_0(X12,X13))
        | ~ r1_xboole_0(X12,X13) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_11,plain,(
    ! [X18,X19] : k4_xboole_0(X18,k4_xboole_0(X18,X19)) = k3_xboole_0(X18,X19) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_12,plain,(
    ! [X7,X8] :
      ( ( ~ r1_xboole_0(X7,X8)
        | k3_xboole_0(X7,X8) = k1_xboole_0 )
      & ( k3_xboole_0(X7,X8) != k1_xboole_0
        | r1_xboole_0(X7,X8) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

fof(c_0_13,plain,(
    ! [X25,X26] : r1_xboole_0(k3_xboole_0(X25,X26),k4_xboole_0(X25,X26)) ),
    inference(variable_rename,[status(thm)],[t89_xboole_1])).

cnf(c_0_14,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_17,plain,
    ( ~ epred2_0
  <=> ! [X2,X3] : ~ r1_xboole_0(X2,X3) ),
    introduced(definition)).

cnf(c_0_18,plain,
    ( r1_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_19,plain,
    ( ~ epred1_0
  <=> ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    introduced(definition)).

cnf(c_0_20,plain,
    ( ~ r1_xboole_0(X2,X3)
    | ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_21,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_16,c_0_15])).

cnf(c_0_22,plain,
    ( epred2_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_equiv,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[c_0_18,c_0_15])).

fof(c_0_24,plain,(
    ! [X33,X34] :
      ( k3_xboole_0(X33,k1_tarski(X34)) != k1_tarski(X34)
      | r2_hidden(X34,X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t51_zfmisc_1])])).

cnf(c_0_25,plain,
    ( ~ epred2_0
    | ~ epred1_0 ),
    inference(apply_def,[status(thm)],[inference(apply_def,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_19]),c_0_17])).

cnf(c_0_26,plain,
    ( epred2_0 ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

fof(c_0_27,plain,(
    ! [X35,X36] :
      ( X35 = k1_xboole_0
      | X36 = k1_xboole_0
      | k1_setfam_1(k2_xboole_0(X35,X36)) = k3_xboole_0(k1_setfam_1(X35),k1_setfam_1(X36)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_setfam_1])])).

cnf(c_0_28,plain,
    ( r2_hidden(X2,X1)
    | k3_xboole_0(X1,k1_tarski(X2)) != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_29,plain,(
    ! [X20] : k4_xboole_0(k1_xboole_0,X20) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

cnf(c_0_30,plain,
    ( ~ epred1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_26])])).

fof(c_0_31,negated_conjecture,(
    ~ ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(assume_negation,[status(cth)],[t12_setfam_1])).

cnf(c_0_32,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | k1_setfam_1(k2_xboole_0(X1,X2)) = k3_xboole_0(k1_setfam_1(X1),k1_setfam_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_33,plain,(
    ! [X37] : k1_setfam_1(k1_tarski(X37)) = X37 ),
    inference(variable_rename,[status(thm)],[t11_setfam_1])).

cnf(c_0_34,plain,
    ( r2_hidden(X2,X1)
    | k4_xboole_0(X1,k4_xboole_0(X1,k1_tarski(X2))) != k1_tarski(X2) ),
    inference(rw,[status(thm)],[c_0_28,c_0_15])).

cnf(c_0_35,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(split_equiv,[status(thm)],[c_0_19]),c_0_30])).

fof(c_0_37,negated_conjecture,(
    k1_setfam_1(k2_tarski(esk2_0,esk3_0)) != k3_xboole_0(esk2_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_31])])])).

fof(c_0_38,plain,(
    ! [X27,X28] : k2_tarski(X27,X28) = k2_xboole_0(k1_tarski(X27),k1_tarski(X28)) ),
    inference(variable_rename,[status(thm)],[t41_enumset1])).

cnf(c_0_39,plain,
    ( X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k1_setfam_1(k2_xboole_0(X1,X2)) = k4_xboole_0(k1_setfam_1(X1),k4_xboole_0(k1_setfam_1(X1),k1_setfam_1(X2))) ),
    inference(rw,[status(thm)],[c_0_32,c_0_15])).

cnf(c_0_40,plain,
    ( k1_setfam_1(k1_tarski(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,plain,
    ( k1_tarski(X1) != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_35]),c_0_36])).

cnf(c_0_42,negated_conjecture,
    ( k1_setfam_1(k2_tarski(esk2_0,esk3_0)) != k3_xboole_0(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_43,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_44,plain,
    ( k4_xboole_0(k1_setfam_1(X1),k4_xboole_0(k1_setfam_1(X1),X2)) = k1_setfam_1(k2_xboole_0(X1,k1_tarski(X2)))
    | X1 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41])).

cnf(c_0_45,negated_conjecture,
    ( k1_setfam_1(k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0))) != k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_15]),c_0_43])).

cnf(c_0_46,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_setfam_1(k2_xboole_0(k1_tarski(X1),k1_tarski(X2))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_40]),c_0_41])).

cnf(c_0_47,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_46])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:48:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.21/0.46  # AutoSched0-Mode selected heuristic G_E___103_C18_F1_PI_AE_Q4_CS_SP_S0Y
% 0.21/0.46  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.21/0.46  #
% 0.21/0.46  # Preprocessing time       : 0.027 s
% 0.21/0.46  
% 0.21/0.46  # Proof found!
% 0.21/0.46  # SZS status Theorem
% 0.21/0.46  # SZS output start CNFRefutation
% 0.21/0.46  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.21/0.46  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.21/0.46  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.21/0.46  fof(t89_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t89_xboole_1)).
% 0.21/0.46  fof(t51_zfmisc_1, axiom, ![X1, X2]:(k3_xboole_0(X1,k1_tarski(X2))=k1_tarski(X2)=>r2_hidden(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_zfmisc_1)).
% 0.21/0.46  fof(t10_setfam_1, axiom, ![X1, X2]:~(((X1!=k1_xboole_0&X2!=k1_xboole_0)&k1_setfam_1(k2_xboole_0(X1,X2))!=k3_xboole_0(k1_setfam_1(X1),k1_setfam_1(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_setfam_1)).
% 0.21/0.46  fof(t4_boole, axiom, ![X1]:k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 0.21/0.46  fof(t12_setfam_1, conjecture, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.21/0.46  fof(t11_setfam_1, axiom, ![X1]:k1_setfam_1(k1_tarski(X1))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_setfam_1)).
% 0.21/0.46  fof(t41_enumset1, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 0.21/0.46  fof(c_0_10, plain, ![X9, X10, X12, X13, X14]:((r1_xboole_0(X9,X10)|r2_hidden(esk1_2(X9,X10),k3_xboole_0(X9,X10)))&(~r2_hidden(X14,k3_xboole_0(X12,X13))|~r1_xboole_0(X12,X13))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.21/0.46  fof(c_0_11, plain, ![X18, X19]:k4_xboole_0(X18,k4_xboole_0(X18,X19))=k3_xboole_0(X18,X19), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.21/0.46  fof(c_0_12, plain, ![X7, X8]:((~r1_xboole_0(X7,X8)|k3_xboole_0(X7,X8)=k1_xboole_0)&(k3_xboole_0(X7,X8)!=k1_xboole_0|r1_xboole_0(X7,X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.21/0.46  fof(c_0_13, plain, ![X25, X26]:r1_xboole_0(k3_xboole_0(X25,X26),k4_xboole_0(X25,X26)), inference(variable_rename,[status(thm)],[t89_xboole_1])).
% 0.21/0.46  cnf(c_0_14, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.46  cnf(c_0_15, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.46  cnf(c_0_16, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.46  fof(c_0_17, plain, (~epred2_0<=>![X2, X3]:~r1_xboole_0(X2,X3)), introduced(definition)).
% 0.21/0.46  cnf(c_0_18, plain, (r1_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.46  fof(c_0_19, plain, (~epred1_0<=>![X1]:~r2_hidden(X1,k1_xboole_0)), introduced(definition)).
% 0.21/0.46  cnf(c_0_20, plain, (~r1_xboole_0(X2,X3)|~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 0.21/0.46  cnf(c_0_21, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_16, c_0_15])).
% 0.21/0.46  cnf(c_0_22, plain, (epred2_0|~r1_xboole_0(X1,X2)), inference(split_equiv,[status(thm)],[c_0_17])).
% 0.21/0.46  cnf(c_0_23, plain, (r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2))), inference(rw,[status(thm)],[c_0_18, c_0_15])).
% 0.21/0.46  fof(c_0_24, plain, ![X33, X34]:(k3_xboole_0(X33,k1_tarski(X34))!=k1_tarski(X34)|r2_hidden(X34,X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t51_zfmisc_1])])).
% 0.21/0.46  cnf(c_0_25, plain, (~epred2_0|~epred1_0), inference(apply_def,[status(thm)],[inference(apply_def,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_19]), c_0_17])).
% 0.21/0.46  cnf(c_0_26, plain, (epred2_0), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.21/0.46  fof(c_0_27, plain, ![X35, X36]:(X35=k1_xboole_0|X36=k1_xboole_0|k1_setfam_1(k2_xboole_0(X35,X36))=k3_xboole_0(k1_setfam_1(X35),k1_setfam_1(X36))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_setfam_1])])).
% 0.21/0.46  cnf(c_0_28, plain, (r2_hidden(X2,X1)|k3_xboole_0(X1,k1_tarski(X2))!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.21/0.46  fof(c_0_29, plain, ![X20]:k4_xboole_0(k1_xboole_0,X20)=k1_xboole_0, inference(variable_rename,[status(thm)],[t4_boole])).
% 0.21/0.46  cnf(c_0_30, plain, (~epred1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_26])])).
% 0.21/0.46  fof(c_0_31, negated_conjecture, ~(![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(assume_negation,[status(cth)],[t12_setfam_1])).
% 0.21/0.46  cnf(c_0_32, plain, (X1=k1_xboole_0|X2=k1_xboole_0|k1_setfam_1(k2_xboole_0(X1,X2))=k3_xboole_0(k1_setfam_1(X1),k1_setfam_1(X2))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.21/0.46  fof(c_0_33, plain, ![X37]:k1_setfam_1(k1_tarski(X37))=X37, inference(variable_rename,[status(thm)],[t11_setfam_1])).
% 0.21/0.46  cnf(c_0_34, plain, (r2_hidden(X2,X1)|k4_xboole_0(X1,k4_xboole_0(X1,k1_tarski(X2)))!=k1_tarski(X2)), inference(rw,[status(thm)],[c_0_28, c_0_15])).
% 0.21/0.46  cnf(c_0_35, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.21/0.46  cnf(c_0_36, plain, (~r2_hidden(X1,k1_xboole_0)), inference(sr,[status(thm)],[inference(split_equiv,[status(thm)],[c_0_19]), c_0_30])).
% 0.21/0.46  fof(c_0_37, negated_conjecture, k1_setfam_1(k2_tarski(esk2_0,esk3_0))!=k3_xboole_0(esk2_0,esk3_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_31])])])).
% 0.21/0.46  fof(c_0_38, plain, ![X27, X28]:k2_tarski(X27,X28)=k2_xboole_0(k1_tarski(X27),k1_tarski(X28)), inference(variable_rename,[status(thm)],[t41_enumset1])).
% 0.21/0.46  cnf(c_0_39, plain, (X2=k1_xboole_0|X1=k1_xboole_0|k1_setfam_1(k2_xboole_0(X1,X2))=k4_xboole_0(k1_setfam_1(X1),k4_xboole_0(k1_setfam_1(X1),k1_setfam_1(X2)))), inference(rw,[status(thm)],[c_0_32, c_0_15])).
% 0.21/0.46  cnf(c_0_40, plain, (k1_setfam_1(k1_tarski(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.21/0.46  cnf(c_0_41, plain, (k1_tarski(X1)!=k1_xboole_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_35]), c_0_36])).
% 0.21/0.46  cnf(c_0_42, negated_conjecture, (k1_setfam_1(k2_tarski(esk2_0,esk3_0))!=k3_xboole_0(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.21/0.46  cnf(c_0_43, plain, (k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.21/0.46  cnf(c_0_44, plain, (k4_xboole_0(k1_setfam_1(X1),k4_xboole_0(k1_setfam_1(X1),X2))=k1_setfam_1(k2_xboole_0(X1,k1_tarski(X2)))|X1=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41])).
% 0.21/0.46  cnf(c_0_45, negated_conjecture, (k1_setfam_1(k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0)))!=k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_15]), c_0_43])).
% 0.21/0.46  cnf(c_0_46, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_setfam_1(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_40]), c_0_41])).
% 0.21/0.46  cnf(c_0_47, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_46])]), ['proof']).
% 0.21/0.46  # SZS output end CNFRefutation
% 0.21/0.46  # Proof object total steps             : 48
% 0.21/0.46  # Proof object clause steps            : 25
% 0.21/0.46  # Proof object formula steps           : 23
% 0.21/0.46  # Proof object conjectures             : 6
% 0.21/0.46  # Proof object clause conjectures      : 3
% 0.21/0.47  # Proof object formula conjectures     : 3
% 0.21/0.47  # Proof object initial clauses used    : 11
% 0.21/0.47  # Proof object initial formulas used   : 10
% 0.21/0.47  # Proof object generating inferences   : 5
% 0.21/0.47  # Proof object simplifying inferences  : 18
% 0.21/0.47  # Training examples: 0 positive, 0 negative
% 0.21/0.47  # Parsed axioms                        : 16
% 0.21/0.47  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.47  # Initial clauses                      : 19
% 0.21/0.47  # Removed in clause preprocessing      : 2
% 0.21/0.47  # Initial clauses in saturation        : 17
% 0.21/0.47  # Processed clauses                    : 1455
% 0.21/0.47  # ...of these trivial                  : 39
% 0.21/0.47  # ...subsumed                          : 1143
% 0.21/0.47  # ...remaining for further processing  : 273
% 0.21/0.47  # Other redundant clauses eliminated   : 55
% 0.21/0.47  # Clauses deleted for lack of memory   : 0
% 0.21/0.47  # Backward-subsumed                    : 12
% 0.21/0.47  # Backward-rewritten                   : 16
% 0.21/0.47  # Generated clauses                    : 8391
% 0.21/0.47  # ...of the previous two non-trivial   : 6143
% 0.21/0.47  # Contextual simplify-reflections      : 9
% 0.21/0.47  # Paramodulations                      : 8324
% 0.21/0.47  # Factorizations                       : 4
% 0.21/0.47  # Equation resolutions                 : 60
% 0.21/0.47  # Propositional unsat checks           : 0
% 0.21/0.47  #    Propositional check models        : 0
% 0.21/0.47  #    Propositional check unsatisfiable : 0
% 0.21/0.47  #    Propositional clauses             : 0
% 0.21/0.47  #    Propositional clauses after purity: 0
% 0.21/0.47  #    Propositional unsat core size     : 0
% 0.21/0.47  #    Propositional preprocessing time  : 0.000
% 0.21/0.47  #    Propositional encoding time       : 0.000
% 0.21/0.47  #    Propositional solver time         : 0.000
% 0.21/0.47  #    Success case prop preproc time    : 0.000
% 0.21/0.47  #    Success case prop encoding time   : 0.000
% 0.21/0.47  #    Success case prop solver time     : 0.000
% 0.21/0.47  # Current number of processed clauses  : 243
% 0.21/0.47  #    Positive orientable unit clauses  : 22
% 0.21/0.47  #    Positive unorientable unit clauses: 2
% 0.21/0.47  #    Negative unit clauses             : 7
% 0.21/0.47  #    Non-unit-clauses                  : 212
% 0.21/0.47  # Current number of unprocessed clauses: 4333
% 0.21/0.47  # ...number of literals in the above   : 15636
% 0.21/0.47  # Current number of archived formulas  : 0
% 0.21/0.47  # Current number of archived clauses   : 30
% 0.21/0.47  # Clause-clause subsumption calls (NU) : 7285
% 0.21/0.47  # Rec. Clause-clause subsumption calls : 6174
% 0.21/0.47  # Non-unit clause-clause subsumptions  : 680
% 0.21/0.47  # Unit Clause-clause subsumption calls : 42
% 0.21/0.47  # Rewrite failures with RHS unbound    : 0
% 0.21/0.47  # BW rewrite match attempts            : 90
% 0.21/0.47  # BW rewrite match successes           : 30
% 0.21/0.47  # Condensation attempts                : 0
% 0.21/0.47  # Condensation successes               : 0
% 0.21/0.47  # Termbank termtop insertions          : 108374
% 0.21/0.47  
% 0.21/0.47  # -------------------------------------------------
% 0.21/0.47  # User time                : 0.119 s
% 0.21/0.47  # System time              : 0.006 s
% 0.21/0.47  # Total time               : 0.126 s
% 0.21/0.47  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
