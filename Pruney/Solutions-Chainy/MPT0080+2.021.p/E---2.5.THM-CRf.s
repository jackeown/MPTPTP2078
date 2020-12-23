%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:33:10 EST 2020

% Result     : Theorem 0.60s
% Output     : CNFRefutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 151 expanded)
%              Number of clauses        :   34 (  68 expanded)
%              Number of leaves         :   10 (  40 expanded)
%              Depth                    :   13
%              Number of atoms          :   87 ( 235 expanded)
%              Number of equality atoms :   35 ( 122 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t73_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,k2_xboole_0(X2,X3))
        & r1_xboole_0(X1,X3) )
     => r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t63_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X2,X3) )
     => r1_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( r1_tarski(X1,k2_xboole_0(X2,X3))
          & r1_xboole_0(X1,X3) )
       => r1_tarski(X1,X2) ) ),
    inference(assume_negation,[status(cth)],[t73_xboole_1])).

fof(c_0_11,negated_conjecture,
    ( r1_tarski(esk3_0,k2_xboole_0(esk4_0,esk5_0))
    & r1_xboole_0(esk3_0,esk5_0)
    & ~ r1_tarski(esk3_0,esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

fof(c_0_12,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_13,plain,(
    ! [X28] : k2_xboole_0(X28,k1_xboole_0) = X28 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_14,plain,(
    ! [X26,X27] :
      ( ~ r1_tarski(X26,X27)
      | k2_xboole_0(X26,X27) = X27 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_15,negated_conjecture,
    ( r1_tarski(esk3_0,k2_xboole_0(esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_17,plain,(
    ! [X39,X40] : r1_tarski(X39,k2_xboole_0(X39,X40)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_18,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_19,plain,(
    ! [X24,X25] :
      ( ( k4_xboole_0(X24,X25) != k1_xboole_0
        | r1_tarski(X24,X25) )
      & ( ~ r1_tarski(X24,X25)
        | k4_xboole_0(X24,X25) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_20,plain,(
    ! [X33,X34,X35] : k4_xboole_0(k4_xboole_0(X33,X34),X35) = k4_xboole_0(X33,k2_xboole_0(X34,X35)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_21,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,negated_conjecture,
    ( r1_tarski(esk3_0,k2_xboole_0(esk5_0,esk4_0)) ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_23,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_18,c_0_16])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( k2_xboole_0(esk3_0,k2_xboole_0(esk5_0,esk4_0)) = k2_xboole_0(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_28,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_16])).

cnf(c_0_30,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | k4_xboole_0(k4_xboole_0(X1,X2),X3) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,esk3_0),esk5_0),esk4_0) = k4_xboole_0(k4_xboole_0(X1,esk5_0),esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_26]),c_0_26])).

cnf(c_0_33,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_26])).

cnf(c_0_34,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_28,c_0_30])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4))
    | k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X3),X4) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_31,c_0_26])).

cnf(c_0_36,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(esk3_0,X1),esk5_0),esk4_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_34])).

fof(c_0_37,plain,(
    ! [X36,X37,X38] :
      ( ~ r1_tarski(X36,X37)
      | ~ r1_xboole_0(X37,X38)
      | r1_xboole_0(X36,X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).

cnf(c_0_38,negated_conjecture,
    ( r1_tarski(esk3_0,k2_xboole_0(esk4_0,k2_xboole_0(X1,esk5_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_16])).

cnf(c_0_39,plain,
    ( r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_40,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_41,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(esk3_0,esk4_0),X1),esk5_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_38]),c_0_26]),c_0_26])).

fof(c_0_42,plain,(
    ! [X22,X23] :
      ( ( ~ r1_xboole_0(X22,X23)
        | k3_xboole_0(X22,X23) = k1_xboole_0 )
      & ( k3_xboole_0(X22,X23) != k1_xboole_0
        | r1_xboole_0(X22,X23) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_43,negated_conjecture,
    ( r1_xboole_0(X1,esk5_0)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_44,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_33])).

fof(c_0_45,plain,(
    ! [X29,X30] :
      ( ~ r1_tarski(X29,X30)
      | k3_xboole_0(X29,X30) = X29 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk3_0,esk4_0),k2_xboole_0(X1,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_41])).

cnf(c_0_47,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_48,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(esk3_0,X1),esk5_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_49,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk3_0,esk4_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_24])).

cnf(c_0_51,negated_conjecture,
    ( k3_xboole_0(k4_xboole_0(esk3_0,X1),esk5_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_52,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk4_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51])).

cnf(c_0_53,negated_conjecture,
    ( ~ r1_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_54,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_52]),c_0_53]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:34:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.60/0.79  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.60/0.79  # and selection function SelectNegativeLiterals.
% 0.60/0.79  #
% 0.60/0.79  # Preprocessing time       : 0.027 s
% 0.60/0.79  # Presaturation interreduction done
% 0.60/0.79  
% 0.60/0.79  # Proof found!
% 0.60/0.79  # SZS status Theorem
% 0.60/0.79  # SZS output start CNFRefutation
% 0.60/0.79  fof(t73_xboole_1, conjecture, ![X1, X2, X3]:((r1_tarski(X1,k2_xboole_0(X2,X3))&r1_xboole_0(X1,X3))=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_xboole_1)).
% 0.60/0.79  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.60/0.79  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 0.60/0.79  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.60/0.79  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.60/0.79  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.60/0.79  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 0.60/0.79  fof(t63_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X2,X3))=>r1_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 0.60/0.79  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.60/0.79  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.60/0.79  fof(c_0_10, negated_conjecture, ~(![X1, X2, X3]:((r1_tarski(X1,k2_xboole_0(X2,X3))&r1_xboole_0(X1,X3))=>r1_tarski(X1,X2))), inference(assume_negation,[status(cth)],[t73_xboole_1])).
% 0.60/0.79  fof(c_0_11, negated_conjecture, ((r1_tarski(esk3_0,k2_xboole_0(esk4_0,esk5_0))&r1_xboole_0(esk3_0,esk5_0))&~r1_tarski(esk3_0,esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).
% 0.60/0.79  fof(c_0_12, plain, ![X5, X6]:k2_xboole_0(X5,X6)=k2_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.60/0.79  fof(c_0_13, plain, ![X28]:k2_xboole_0(X28,k1_xboole_0)=X28, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.60/0.79  fof(c_0_14, plain, ![X26, X27]:(~r1_tarski(X26,X27)|k2_xboole_0(X26,X27)=X27), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.60/0.79  cnf(c_0_15, negated_conjecture, (r1_tarski(esk3_0,k2_xboole_0(esk4_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.60/0.79  cnf(c_0_16, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.60/0.79  fof(c_0_17, plain, ![X39, X40]:r1_tarski(X39,k2_xboole_0(X39,X40)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.60/0.79  cnf(c_0_18, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.60/0.79  fof(c_0_19, plain, ![X24, X25]:((k4_xboole_0(X24,X25)!=k1_xboole_0|r1_tarski(X24,X25))&(~r1_tarski(X24,X25)|k4_xboole_0(X24,X25)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.60/0.79  fof(c_0_20, plain, ![X33, X34, X35]:k4_xboole_0(k4_xboole_0(X33,X34),X35)=k4_xboole_0(X33,k2_xboole_0(X34,X35)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 0.60/0.79  cnf(c_0_21, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.60/0.79  cnf(c_0_22, negated_conjecture, (r1_tarski(esk3_0,k2_xboole_0(esk5_0,esk4_0))), inference(rw,[status(thm)],[c_0_15, c_0_16])).
% 0.60/0.79  cnf(c_0_23, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.60/0.79  cnf(c_0_24, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_18, c_0_16])).
% 0.60/0.79  cnf(c_0_25, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.60/0.79  cnf(c_0_26, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.60/0.79  cnf(c_0_27, negated_conjecture, (k2_xboole_0(esk3_0,k2_xboole_0(esk5_0,esk4_0))=k2_xboole_0(esk5_0,esk4_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.60/0.79  cnf(c_0_28, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.60/0.79  cnf(c_0_29, plain, (r1_tarski(X1,k2_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_23, c_0_16])).
% 0.60/0.79  cnf(c_0_30, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.60/0.79  cnf(c_0_31, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|k4_xboole_0(k4_xboole_0(X1,X2),X3)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.60/0.79  cnf(c_0_32, negated_conjecture, (k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,esk3_0),esk5_0),esk4_0)=k4_xboole_0(k4_xboole_0(X1,esk5_0),esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_26]), c_0_26])).
% 0.60/0.79  cnf(c_0_33, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_26])).
% 0.60/0.79  cnf(c_0_34, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_28, c_0_30])).
% 0.60/0.79  cnf(c_0_35, plain, (r1_tarski(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4))|k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X3),X4)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_31, c_0_26])).
% 0.60/0.79  cnf(c_0_36, negated_conjecture, (k4_xboole_0(k4_xboole_0(k4_xboole_0(esk3_0,X1),esk5_0),esk4_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34]), c_0_34])).
% 0.60/0.79  fof(c_0_37, plain, ![X36, X37, X38]:(~r1_tarski(X36,X37)|~r1_xboole_0(X37,X38)|r1_xboole_0(X36,X38)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).
% 0.60/0.79  cnf(c_0_38, negated_conjecture, (r1_tarski(esk3_0,k2_xboole_0(esk4_0,k2_xboole_0(X1,esk5_0)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_16])).
% 0.60/0.79  cnf(c_0_39, plain, (r1_xboole_0(X1,X3)|~r1_tarski(X1,X2)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.60/0.79  cnf(c_0_40, negated_conjecture, (r1_xboole_0(esk3_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.60/0.79  cnf(c_0_41, negated_conjecture, (k4_xboole_0(k4_xboole_0(k4_xboole_0(esk3_0,esk4_0),X1),esk5_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_38]), c_0_26]), c_0_26])).
% 0.60/0.79  fof(c_0_42, plain, ![X22, X23]:((~r1_xboole_0(X22,X23)|k3_xboole_0(X22,X23)=k1_xboole_0)&(k3_xboole_0(X22,X23)!=k1_xboole_0|r1_xboole_0(X22,X23))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.60/0.79  cnf(c_0_43, negated_conjecture, (r1_xboole_0(X1,esk5_0)|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.60/0.79  cnf(c_0_44, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_25, c_0_33])).
% 0.60/0.79  fof(c_0_45, plain, ![X29, X30]:(~r1_tarski(X29,X30)|k3_xboole_0(X29,X30)=X29), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.60/0.79  cnf(c_0_46, negated_conjecture, (r1_tarski(k4_xboole_0(esk3_0,esk4_0),k2_xboole_0(X1,esk5_0))), inference(spm,[status(thm)],[c_0_31, c_0_41])).
% 0.60/0.79  cnf(c_0_47, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.60/0.79  cnf(c_0_48, negated_conjecture, (r1_xboole_0(k4_xboole_0(esk3_0,X1),esk5_0)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.60/0.79  cnf(c_0_49, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.60/0.79  cnf(c_0_50, negated_conjecture, (r1_tarski(k4_xboole_0(esk3_0,esk4_0),esk5_0)), inference(spm,[status(thm)],[c_0_46, c_0_24])).
% 0.60/0.79  cnf(c_0_51, negated_conjecture, (k3_xboole_0(k4_xboole_0(esk3_0,X1),esk5_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.60/0.79  cnf(c_0_52, negated_conjecture, (k4_xboole_0(esk3_0,esk4_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51])).
% 0.60/0.79  cnf(c_0_53, negated_conjecture, (~r1_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.60/0.79  cnf(c_0_54, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_52]), c_0_53]), ['proof']).
% 0.60/0.79  # SZS output end CNFRefutation
% 0.60/0.79  # Proof object total steps             : 55
% 0.60/0.79  # Proof object clause steps            : 34
% 0.60/0.79  # Proof object formula steps           : 21
% 0.60/0.79  # Proof object conjectures             : 19
% 0.60/0.79  # Proof object clause conjectures      : 16
% 0.60/0.79  # Proof object formula conjectures     : 3
% 0.60/0.79  # Proof object initial clauses used    : 13
% 0.60/0.79  # Proof object initial formulas used   : 10
% 0.60/0.79  # Proof object generating inferences   : 20
% 0.60/0.79  # Proof object simplifying inferences  : 11
% 0.60/0.79  # Training examples: 0 positive, 0 negative
% 0.60/0.79  # Parsed axioms                        : 13
% 0.60/0.79  # Removed by relevancy pruning/SinE    : 0
% 0.60/0.79  # Initial clauses                      : 24
% 0.60/0.79  # Removed in clause preprocessing      : 0
% 0.60/0.79  # Initial clauses in saturation        : 24
% 0.60/0.79  # Processed clauses                    : 1930
% 0.60/0.79  # ...of these trivial                  : 307
% 0.60/0.79  # ...subsumed                          : 1053
% 0.60/0.79  # ...remaining for further processing  : 570
% 0.60/0.79  # Other redundant clauses eliminated   : 293
% 0.60/0.79  # Clauses deleted for lack of memory   : 0
% 0.60/0.79  # Backward-subsumed                    : 8
% 0.60/0.79  # Backward-rewritten                   : 79
% 0.60/0.79  # Generated clauses                    : 42077
% 0.60/0.79  # ...of the previous two non-trivial   : 32080
% 0.60/0.79  # Contextual simplify-reflections      : 3
% 0.60/0.79  # Paramodulations                      : 41762
% 0.60/0.79  # Factorizations                       : 22
% 0.60/0.79  # Equation resolutions                 : 293
% 0.60/0.79  # Propositional unsat checks           : 0
% 0.60/0.79  #    Propositional check models        : 0
% 0.60/0.79  #    Propositional check unsatisfiable : 0
% 0.60/0.79  #    Propositional clauses             : 0
% 0.60/0.79  #    Propositional clauses after purity: 0
% 0.60/0.79  #    Propositional unsat core size     : 0
% 0.60/0.79  #    Propositional preprocessing time  : 0.000
% 0.60/0.79  #    Propositional encoding time       : 0.000
% 0.60/0.79  #    Propositional solver time         : 0.000
% 0.60/0.79  #    Success case prop preproc time    : 0.000
% 0.60/0.79  #    Success case prop encoding time   : 0.000
% 0.60/0.79  #    Success case prop solver time     : 0.000
% 0.60/0.79  # Current number of processed clauses  : 456
% 0.60/0.79  #    Positive orientable unit clauses  : 205
% 0.60/0.79  #    Positive unorientable unit clauses: 2
% 0.60/0.79  #    Negative unit clauses             : 12
% 0.60/0.79  #    Non-unit-clauses                  : 237
% 0.60/0.79  # Current number of unprocessed clauses: 30038
% 0.60/0.79  # ...number of literals in the above   : 108425
% 0.60/0.79  # Current number of archived formulas  : 0
% 0.60/0.79  # Current number of archived clauses   : 111
% 0.60/0.79  # Clause-clause subsumption calls (NU) : 6641
% 0.60/0.79  # Rec. Clause-clause subsumption calls : 5063
% 0.60/0.79  # Non-unit clause-clause subsumptions  : 399
% 0.60/0.79  # Unit Clause-clause subsumption calls : 1008
% 0.60/0.79  # Rewrite failures with RHS unbound    : 0
% 0.60/0.79  # BW rewrite match attempts            : 408
% 0.60/0.79  # BW rewrite match successes           : 91
% 0.60/0.79  # Condensation attempts                : 0
% 0.60/0.79  # Condensation successes               : 0
% 0.60/0.79  # Termbank termtop insertions          : 655730
% 0.60/0.79  
% 0.60/0.79  # -------------------------------------------------
% 0.60/0.79  # User time                : 0.418 s
% 0.60/0.79  # System time              : 0.032 s
% 0.60/0.79  # Total time               : 0.450 s
% 0.60/0.79  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
