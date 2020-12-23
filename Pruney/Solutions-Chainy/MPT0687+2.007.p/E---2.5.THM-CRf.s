%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:54:35 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   35 (  62 expanded)
%              Number of clauses        :   24 (  28 expanded)
%              Number of leaves         :    5 (  15 expanded)
%              Depth                    :    8
%              Number of atoms          :  102 ( 195 expanded)
%              Number of equality atoms :   38 (  72 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(t142_funct_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X1,k2_relat_1(X2))
      <=> k10_relat_1(X2,k1_tarski(X1)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_1)).

fof(t173_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( k10_relat_1(X2,X1) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

fof(c_0_5,plain,(
    ! [X10,X11,X12,X13,X14,X15] :
      ( ( ~ r2_hidden(X12,X11)
        | X12 = X10
        | X11 != k1_tarski(X10) )
      & ( X13 != X10
        | r2_hidden(X13,X11)
        | X11 != k1_tarski(X10) )
      & ( ~ r2_hidden(esk2_2(X14,X15),X15)
        | esk2_2(X14,X15) != X14
        | X15 = k1_tarski(X14) )
      & ( r2_hidden(esk2_2(X14,X15),X15)
        | esk2_2(X14,X15) = X14
        | X15 = k1_tarski(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_6,plain,(
    ! [X17] : k2_tarski(X17,X17) = k1_tarski(X17) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_7,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,plain,
    ( X1 = X3
    | X2 != k2_tarski(X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_7,c_0_8])).

fof(c_0_11,plain,(
    ! [X4,X5,X7,X8,X9] :
      ( ( r2_hidden(esk1_2(X4,X5),X4)
        | r1_xboole_0(X4,X5) )
      & ( r2_hidden(esk1_2(X4,X5),X5)
        | r1_xboole_0(X4,X5) )
      & ( ~ r2_hidden(X9,X7)
        | ~ r2_hidden(X9,X8)
        | ~ r1_xboole_0(X7,X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_12,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X2) ),
    inference(rw,[status(thm)],[c_0_9,c_0_8])).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( r2_hidden(X1,k2_relat_1(X2))
        <=> k10_relat_1(X2,k1_tarski(X1)) != k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t142_funct_1])).

cnf(c_0_14,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k2_tarski(X2,X2)) ),
    inference(er,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,k2_tarski(X1,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_12])])).

fof(c_0_18,plain,(
    ! [X20,X21] :
      ( ( k10_relat_1(X21,X20) != k1_xboole_0
        | r1_xboole_0(k2_relat_1(X21),X20)
        | ~ v1_relat_1(X21) )
      & ( ~ r1_xboole_0(k2_relat_1(X21),X20)
        | k10_relat_1(X21,X20) = k1_xboole_0
        | ~ v1_relat_1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t173_relat_1])])])).

fof(c_0_19,negated_conjecture,
    ( v1_relat_1(esk4_0)
    & ( ~ r2_hidden(esk3_0,k2_relat_1(esk4_0))
      | k10_relat_1(esk4_0,k1_tarski(esk3_0)) = k1_xboole_0 )
    & ( r2_hidden(esk3_0,k2_relat_1(esk4_0))
      | k10_relat_1(esk4_0,k1_tarski(esk3_0)) != k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

cnf(c_0_20,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_21,plain,
    ( esk1_2(X1,k2_tarski(X2,X2)) = X2
    | r1_xboole_0(X1,k2_tarski(X2,X2)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_22,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_xboole_0(X2,k2_tarski(X1,X1)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_23,plain,
    ( r1_xboole_0(k2_relat_1(X1),X2)
    | k10_relat_1(X1,X2) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( k10_relat_1(esk4_0,k1_tarski(esk3_0)) = k1_xboole_0
    | ~ r2_hidden(esk3_0,k2_relat_1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk3_0,k2_relat_1(esk4_0))
    | k10_relat_1(esk4_0,k1_tarski(esk3_0)) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( k10_relat_1(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(k2_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(X2,k2_tarski(X1,X1)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_28,plain,
    ( k10_relat_1(X1,k2_tarski(X2,X2)) != k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( k10_relat_1(esk4_0,k2_tarski(esk3_0,esk3_0)) = k1_xboole_0
    | ~ r2_hidden(esk3_0,k2_relat_1(esk4_0)) ),
    inference(rw,[status(thm)],[c_0_24,c_0_8])).

cnf(c_0_30,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk3_0,k2_relat_1(esk4_0))
    | k10_relat_1(esk4_0,k2_tarski(esk3_0,esk3_0)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_25,c_0_8])).

cnf(c_0_32,plain,
    ( k10_relat_1(X1,k2_tarski(X2,X2)) = k1_xboole_0
    | r2_hidden(X2,k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( ~ r2_hidden(esk3_0,k2_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])])).

cnf(c_0_34,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_30])]),c_0_33]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:04:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.19/0.39  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.19/0.39  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.39  #
% 0.19/0.39  # Preprocessing time       : 0.036 s
% 0.19/0.39  
% 0.19/0.39  # Proof found!
% 0.19/0.39  # SZS status Theorem
% 0.19/0.39  # SZS output start CNFRefutation
% 0.19/0.39  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 0.19/0.39  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.39  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.19/0.39  fof(t142_funct_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(r2_hidden(X1,k2_relat_1(X2))<=>k10_relat_1(X2,k1_tarski(X1))!=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_funct_1)).
% 0.19/0.39  fof(t173_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(k10_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k2_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 0.19/0.39  fof(c_0_5, plain, ![X10, X11, X12, X13, X14, X15]:(((~r2_hidden(X12,X11)|X12=X10|X11!=k1_tarski(X10))&(X13!=X10|r2_hidden(X13,X11)|X11!=k1_tarski(X10)))&((~r2_hidden(esk2_2(X14,X15),X15)|esk2_2(X14,X15)!=X14|X15=k1_tarski(X14))&(r2_hidden(esk2_2(X14,X15),X15)|esk2_2(X14,X15)=X14|X15=k1_tarski(X14)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.19/0.39  fof(c_0_6, plain, ![X17]:k2_tarski(X17,X17)=k1_tarski(X17), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.39  cnf(c_0_7, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.39  cnf(c_0_8, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.39  cnf(c_0_9, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.39  cnf(c_0_10, plain, (X1=X3|X2!=k2_tarski(X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_7, c_0_8])).
% 0.19/0.39  fof(c_0_11, plain, ![X4, X5, X7, X8, X9]:(((r2_hidden(esk1_2(X4,X5),X4)|r1_xboole_0(X4,X5))&(r2_hidden(esk1_2(X4,X5),X5)|r1_xboole_0(X4,X5)))&(~r2_hidden(X9,X7)|~r2_hidden(X9,X8)|~r1_xboole_0(X7,X8))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.19/0.39  cnf(c_0_12, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X2,X2)), inference(rw,[status(thm)],[c_0_9, c_0_8])).
% 0.19/0.39  fof(c_0_13, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(r2_hidden(X1,k2_relat_1(X2))<=>k10_relat_1(X2,k1_tarski(X1))!=k1_xboole_0))), inference(assume_negation,[status(cth)],[t142_funct_1])).
% 0.19/0.39  cnf(c_0_14, plain, (X1=X2|~r2_hidden(X1,k2_tarski(X2,X2))), inference(er,[status(thm)],[c_0_10])).
% 0.19/0.39  cnf(c_0_15, plain, (r2_hidden(esk1_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.39  cnf(c_0_16, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.39  cnf(c_0_17, plain, (r2_hidden(X1,k2_tarski(X1,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_12])])).
% 0.19/0.39  fof(c_0_18, plain, ![X20, X21]:((k10_relat_1(X21,X20)!=k1_xboole_0|r1_xboole_0(k2_relat_1(X21),X20)|~v1_relat_1(X21))&(~r1_xboole_0(k2_relat_1(X21),X20)|k10_relat_1(X21,X20)=k1_xboole_0|~v1_relat_1(X21))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t173_relat_1])])])).
% 0.19/0.39  fof(c_0_19, negated_conjecture, (v1_relat_1(esk4_0)&((~r2_hidden(esk3_0,k2_relat_1(esk4_0))|k10_relat_1(esk4_0,k1_tarski(esk3_0))=k1_xboole_0)&(r2_hidden(esk3_0,k2_relat_1(esk4_0))|k10_relat_1(esk4_0,k1_tarski(esk3_0))!=k1_xboole_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 0.19/0.39  cnf(c_0_20, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.39  cnf(c_0_21, plain, (esk1_2(X1,k2_tarski(X2,X2))=X2|r1_xboole_0(X1,k2_tarski(X2,X2))), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.19/0.39  cnf(c_0_22, plain, (~r2_hidden(X1,X2)|~r1_xboole_0(X2,k2_tarski(X1,X1))), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.19/0.39  cnf(c_0_23, plain, (r1_xboole_0(k2_relat_1(X1),X2)|k10_relat_1(X1,X2)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.39  cnf(c_0_24, negated_conjecture, (k10_relat_1(esk4_0,k1_tarski(esk3_0))=k1_xboole_0|~r2_hidden(esk3_0,k2_relat_1(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.39  cnf(c_0_25, negated_conjecture, (r2_hidden(esk3_0,k2_relat_1(esk4_0))|k10_relat_1(esk4_0,k1_tarski(esk3_0))!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.39  cnf(c_0_26, plain, (k10_relat_1(X1,X2)=k1_xboole_0|~r1_xboole_0(k2_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.39  cnf(c_0_27, plain, (r2_hidden(X1,X2)|r1_xboole_0(X2,k2_tarski(X1,X1))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.19/0.39  cnf(c_0_28, plain, (k10_relat_1(X1,k2_tarski(X2,X2))!=k1_xboole_0|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.19/0.39  cnf(c_0_29, negated_conjecture, (k10_relat_1(esk4_0,k2_tarski(esk3_0,esk3_0))=k1_xboole_0|~r2_hidden(esk3_0,k2_relat_1(esk4_0))), inference(rw,[status(thm)],[c_0_24, c_0_8])).
% 0.19/0.39  cnf(c_0_30, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.39  cnf(c_0_31, negated_conjecture, (r2_hidden(esk3_0,k2_relat_1(esk4_0))|k10_relat_1(esk4_0,k2_tarski(esk3_0,esk3_0))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_25, c_0_8])).
% 0.19/0.39  cnf(c_0_32, plain, (k10_relat_1(X1,k2_tarski(X2,X2))=k1_xboole_0|r2_hidden(X2,k2_relat_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.19/0.39  cnf(c_0_33, negated_conjecture, (~r2_hidden(esk3_0,k2_relat_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30])])).
% 0.19/0.39  cnf(c_0_34, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_30])]), c_0_33]), ['proof']).
% 0.19/0.39  # SZS output end CNFRefutation
% 0.19/0.39  # Proof object total steps             : 35
% 0.19/0.39  # Proof object clause steps            : 24
% 0.19/0.39  # Proof object formula steps           : 11
% 0.19/0.39  # Proof object conjectures             : 10
% 0.19/0.39  # Proof object clause conjectures      : 7
% 0.19/0.39  # Proof object formula conjectures     : 3
% 0.19/0.39  # Proof object initial clauses used    : 11
% 0.19/0.39  # Proof object initial formulas used   : 5
% 0.19/0.39  # Proof object generating inferences   : 7
% 0.19/0.39  # Proof object simplifying inferences  : 12
% 0.19/0.39  # Training examples: 0 positive, 0 negative
% 0.19/0.39  # Parsed axioms                        : 6
% 0.19/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.39  # Initial clauses                      : 14
% 0.19/0.39  # Removed in clause preprocessing      : 1
% 0.19/0.39  # Initial clauses in saturation        : 13
% 0.19/0.39  # Processed clauses                    : 33
% 0.19/0.39  # ...of these trivial                  : 0
% 0.19/0.39  # ...subsumed                          : 3
% 0.19/0.39  # ...remaining for further processing  : 30
% 0.19/0.39  # Other redundant clauses eliminated   : 4
% 0.19/0.39  # Clauses deleted for lack of memory   : 0
% 0.19/0.39  # Backward-subsumed                    : 0
% 0.19/0.39  # Backward-rewritten                   : 0
% 0.19/0.39  # Generated clauses                    : 92
% 0.19/0.39  # ...of the previous two non-trivial   : 73
% 0.19/0.39  # Contextual simplify-reflections      : 0
% 0.19/0.39  # Paramodulations                      : 89
% 0.19/0.39  # Factorizations                       : 0
% 0.19/0.39  # Equation resolutions                 : 4
% 0.19/0.39  # Propositional unsat checks           : 0
% 0.19/0.39  #    Propositional check models        : 0
% 0.19/0.39  #    Propositional check unsatisfiable : 0
% 0.19/0.39  #    Propositional clauses             : 0
% 0.19/0.39  #    Propositional clauses after purity: 0
% 0.19/0.39  #    Propositional unsat core size     : 0
% 0.19/0.39  #    Propositional preprocessing time  : 0.000
% 0.19/0.39  #    Propositional encoding time       : 0.000
% 0.19/0.39  #    Propositional solver time         : 0.000
% 0.19/0.39  #    Success case prop preproc time    : 0.000
% 0.19/0.39  #    Success case prop encoding time   : 0.000
% 0.19/0.39  #    Success case prop solver time     : 0.000
% 0.19/0.39  # Current number of processed clauses  : 28
% 0.19/0.39  #    Positive orientable unit clauses  : 2
% 0.19/0.39  #    Positive unorientable unit clauses: 0
% 0.19/0.39  #    Negative unit clauses             : 1
% 0.19/0.39  #    Non-unit-clauses                  : 25
% 0.19/0.39  # Current number of unprocessed clauses: 53
% 0.19/0.39  # ...number of literals in the above   : 213
% 0.19/0.39  # Current number of archived formulas  : 0
% 0.19/0.39  # Current number of archived clauses   : 1
% 0.19/0.39  # Clause-clause subsumption calls (NU) : 31
% 0.19/0.39  # Rec. Clause-clause subsumption calls : 26
% 0.19/0.39  # Non-unit clause-clause subsumptions  : 3
% 0.19/0.39  # Unit Clause-clause subsumption calls : 2
% 0.19/0.39  # Rewrite failures with RHS unbound    : 0
% 0.19/0.39  # BW rewrite match attempts            : 0
% 0.19/0.39  # BW rewrite match successes           : 0
% 0.19/0.39  # Condensation attempts                : 0
% 0.19/0.39  # Condensation successes               : 0
% 0.19/0.39  # Termbank termtop insertions          : 2011
% 0.19/0.39  
% 0.19/0.39  # -------------------------------------------------
% 0.19/0.39  # User time                : 0.035 s
% 0.19/0.39  # System time              : 0.009 s
% 0.19/0.39  # Total time               : 0.044 s
% 0.19/0.39  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
