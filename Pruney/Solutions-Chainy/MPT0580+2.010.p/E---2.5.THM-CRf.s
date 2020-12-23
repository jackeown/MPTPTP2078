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
% DateTime   : Thu Dec  3 10:51:56 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   36 ( 118 expanded)
%              Number of clauses        :   25 (  53 expanded)
%              Number of leaves         :    5 (  28 expanded)
%              Depth                    :   10
%              Number of atoms          :  117 ( 468 expanded)
%              Number of equality atoms :   35 ( 135 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t184_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v3_relat_1(X1)
      <=> ! [X2] :
            ( r2_hidden(X2,k2_relat_1(X1))
           => X2 = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t184_relat_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(d15_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v3_relat_1(X1)
      <=> r1_tarski(k2_relat_1(X1),k1_tarski(k1_xboole_0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d15_relat_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ( v3_relat_1(X1)
        <=> ! [X2] :
              ( r2_hidden(X2,k2_relat_1(X1))
             => X2 = k1_xboole_0 ) ) ) ),
    inference(assume_negation,[status(cth)],[t184_relat_1])).

fof(c_0_6,negated_conjecture,(
    ! [X24] :
      ( v1_relat_1(esk3_0)
      & ( r2_hidden(esk4_0,k2_relat_1(esk3_0))
        | ~ v3_relat_1(esk3_0) )
      & ( esk4_0 != k1_xboole_0
        | ~ v3_relat_1(esk3_0) )
      & ( v3_relat_1(esk3_0)
        | ~ r2_hidden(X24,k2_relat_1(esk3_0))
        | X24 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])])])).

fof(c_0_7,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_8,plain,(
    ! [X21] :
      ( ( ~ v3_relat_1(X21)
        | r1_tarski(k2_relat_1(X21),k1_tarski(k1_xboole_0))
        | ~ v1_relat_1(X21) )
      & ( ~ r1_tarski(k2_relat_1(X21),k1_tarski(k1_xboole_0))
        | v3_relat_1(X21)
        | ~ v1_relat_1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d15_relat_1])])])).

fof(c_0_9,plain,(
    ! [X20] : k2_tarski(X20,X20) = k1_tarski(X20) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_10,negated_conjecture,
    ( v3_relat_1(esk3_0)
    | X1 = k1_xboole_0
    | ~ r2_hidden(X1,k2_relat_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( v3_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),k1_tarski(k1_xboole_0))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_15,negated_conjecture,
    ( esk1_2(k2_relat_1(esk3_0),X1) = k1_xboole_0
    | v3_relat_1(esk3_0)
    | r1_tarski(k2_relat_1(esk3_0),X1) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

fof(c_0_16,plain,(
    ! [X11,X12,X13,X14,X15,X16,X17,X18] :
      ( ( ~ r2_hidden(X14,X13)
        | X14 = X11
        | X14 = X12
        | X13 != k2_tarski(X11,X12) )
      & ( X15 != X11
        | r2_hidden(X15,X13)
        | X13 != k2_tarski(X11,X12) )
      & ( X15 != X12
        | r2_hidden(X15,X13)
        | X13 != k2_tarski(X11,X12) )
      & ( esk2_3(X16,X17,X18) != X16
        | ~ r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k2_tarski(X16,X17) )
      & ( esk2_3(X16,X17,X18) != X17
        | ~ r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k2_tarski(X16,X17) )
      & ( r2_hidden(esk2_3(X16,X17,X18),X18)
        | esk2_3(X16,X17,X18) = X16
        | esk2_3(X16,X17,X18) = X17
        | X18 = k2_tarski(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

cnf(c_0_17,plain,
    ( v3_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),k2_tarski(k1_xboole_0,k1_xboole_0)) ),
    inference(rw,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( v3_relat_1(esk3_0)
    | r1_tarski(k2_relat_1(esk3_0),X1)
    | ~ r2_hidden(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( r1_tarski(k2_relat_1(X1),k1_tarski(k1_xboole_0))
    | ~ v3_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_22,negated_conjecture,
    ( v3_relat_1(esk3_0)
    | ~ r2_hidden(k1_xboole_0,k2_tarski(k1_xboole_0,k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,k2_tarski(X2,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_20])])).

cnf(c_0_24,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_25,plain,
    ( r1_tarski(k2_relat_1(X1),k2_tarski(k1_xboole_0,k1_xboole_0))
    | ~ v1_relat_1(X1)
    | ~ v3_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_21,c_0_13])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk4_0,k2_relat_1(esk3_0))
    | ~ v3_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_27,negated_conjecture,
    ( v3_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_23])])).

cnf(c_0_28,plain,
    ( X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,k2_tarski(k1_xboole_0,k1_xboole_0))
    | ~ v3_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k2_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk4_0,k2_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_27])])).

cnf(c_0_31,negated_conjecture,
    ( esk4_0 != k1_xboole_0
    | ~ v3_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_32,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r2_hidden(X1,k2_tarski(X3,X2)) ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk4_0,k2_tarski(k1_xboole_0,k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_27]),c_0_19])])).

cnf(c_0_34,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_27])])).

cnf(c_0_35,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:03:45 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.39  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.20/0.39  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.39  #
% 0.20/0.39  # Preprocessing time       : 0.050 s
% 0.20/0.39  
% 0.20/0.39  # Proof found!
% 0.20/0.39  # SZS status Theorem
% 0.20/0.39  # SZS output start CNFRefutation
% 0.20/0.39  fof(t184_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>(v3_relat_1(X1)<=>![X2]:(r2_hidden(X2,k2_relat_1(X1))=>X2=k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t184_relat_1)).
% 0.20/0.39  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.39  fof(d15_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>(v3_relat_1(X1)<=>r1_tarski(k2_relat_1(X1),k1_tarski(k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d15_relat_1)).
% 0.20/0.39  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.20/0.39  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 0.20/0.39  fof(c_0_5, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>(v3_relat_1(X1)<=>![X2]:(r2_hidden(X2,k2_relat_1(X1))=>X2=k1_xboole_0)))), inference(assume_negation,[status(cth)],[t184_relat_1])).
% 0.20/0.39  fof(c_0_6, negated_conjecture, ![X24]:(v1_relat_1(esk3_0)&(((r2_hidden(esk4_0,k2_relat_1(esk3_0))|~v3_relat_1(esk3_0))&(esk4_0!=k1_xboole_0|~v3_relat_1(esk3_0)))&(v3_relat_1(esk3_0)|(~r2_hidden(X24,k2_relat_1(esk3_0))|X24=k1_xboole_0)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])])])).
% 0.20/0.39  fof(c_0_7, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.39  fof(c_0_8, plain, ![X21]:((~v3_relat_1(X21)|r1_tarski(k2_relat_1(X21),k1_tarski(k1_xboole_0))|~v1_relat_1(X21))&(~r1_tarski(k2_relat_1(X21),k1_tarski(k1_xboole_0))|v3_relat_1(X21)|~v1_relat_1(X21))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d15_relat_1])])])).
% 0.20/0.39  fof(c_0_9, plain, ![X20]:k2_tarski(X20,X20)=k1_tarski(X20), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.20/0.39  cnf(c_0_10, negated_conjecture, (v3_relat_1(esk3_0)|X1=k1_xboole_0|~r2_hidden(X1,k2_relat_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.39  cnf(c_0_11, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.39  cnf(c_0_12, plain, (v3_relat_1(X1)|~r1_tarski(k2_relat_1(X1),k1_tarski(k1_xboole_0))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.39  cnf(c_0_13, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.39  cnf(c_0_14, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.39  cnf(c_0_15, negated_conjecture, (esk1_2(k2_relat_1(esk3_0),X1)=k1_xboole_0|v3_relat_1(esk3_0)|r1_tarski(k2_relat_1(esk3_0),X1)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.20/0.39  fof(c_0_16, plain, ![X11, X12, X13, X14, X15, X16, X17, X18]:(((~r2_hidden(X14,X13)|(X14=X11|X14=X12)|X13!=k2_tarski(X11,X12))&((X15!=X11|r2_hidden(X15,X13)|X13!=k2_tarski(X11,X12))&(X15!=X12|r2_hidden(X15,X13)|X13!=k2_tarski(X11,X12))))&(((esk2_3(X16,X17,X18)!=X16|~r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k2_tarski(X16,X17))&(esk2_3(X16,X17,X18)!=X17|~r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k2_tarski(X16,X17)))&(r2_hidden(esk2_3(X16,X17,X18),X18)|(esk2_3(X16,X17,X18)=X16|esk2_3(X16,X17,X18)=X17)|X18=k2_tarski(X16,X17)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.20/0.39  cnf(c_0_17, plain, (v3_relat_1(X1)|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),k2_tarski(k1_xboole_0,k1_xboole_0))), inference(rw,[status(thm)],[c_0_12, c_0_13])).
% 0.20/0.39  cnf(c_0_18, negated_conjecture, (v3_relat_1(esk3_0)|r1_tarski(k2_relat_1(esk3_0),X1)|~r2_hidden(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.20/0.39  cnf(c_0_19, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.39  cnf(c_0_20, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.39  cnf(c_0_21, plain, (r1_tarski(k2_relat_1(X1),k1_tarski(k1_xboole_0))|~v3_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.39  cnf(c_0_22, negated_conjecture, (v3_relat_1(esk3_0)|~r2_hidden(k1_xboole_0,k2_tarski(k1_xboole_0,k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19])])).
% 0.20/0.39  cnf(c_0_23, plain, (r2_hidden(X1,k2_tarski(X2,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_20])])).
% 0.20/0.39  cnf(c_0_24, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.39  cnf(c_0_25, plain, (r1_tarski(k2_relat_1(X1),k2_tarski(k1_xboole_0,k1_xboole_0))|~v1_relat_1(X1)|~v3_relat_1(X1)), inference(rw,[status(thm)],[c_0_21, c_0_13])).
% 0.20/0.39  cnf(c_0_26, negated_conjecture, (r2_hidden(esk4_0,k2_relat_1(esk3_0))|~v3_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.39  cnf(c_0_27, negated_conjecture, (v3_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_23])])).
% 0.20/0.39  cnf(c_0_28, plain, (X1=X3|X1=X4|~r2_hidden(X1,X2)|X2!=k2_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.39  cnf(c_0_29, plain, (r2_hidden(X1,k2_tarski(k1_xboole_0,k1_xboole_0))|~v3_relat_1(X2)|~v1_relat_1(X2)|~r2_hidden(X1,k2_relat_1(X2))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.20/0.39  cnf(c_0_30, negated_conjecture, (r2_hidden(esk4_0,k2_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_27])])).
% 0.20/0.39  cnf(c_0_31, negated_conjecture, (esk4_0!=k1_xboole_0|~v3_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.39  cnf(c_0_32, plain, (X1=X2|X1=X3|~r2_hidden(X1,k2_tarski(X3,X2))), inference(er,[status(thm)],[c_0_28])).
% 0.20/0.39  cnf(c_0_33, negated_conjecture, (r2_hidden(esk4_0,k2_tarski(k1_xboole_0,k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_27]), c_0_19])])).
% 0.20/0.39  cnf(c_0_34, negated_conjecture, (esk4_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_27])])).
% 0.20/0.39  cnf(c_0_35, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34]), ['proof']).
% 0.20/0.39  # SZS output end CNFRefutation
% 0.20/0.39  # Proof object total steps             : 36
% 0.20/0.39  # Proof object clause steps            : 25
% 0.20/0.39  # Proof object formula steps           : 11
% 0.20/0.39  # Proof object conjectures             : 15
% 0.20/0.39  # Proof object clause conjectures      : 12
% 0.20/0.39  # Proof object formula conjectures     : 3
% 0.20/0.39  # Proof object initial clauses used    : 12
% 0.20/0.39  # Proof object initial formulas used   : 5
% 0.20/0.39  # Proof object generating inferences   : 6
% 0.20/0.39  # Proof object simplifying inferences  : 17
% 0.20/0.39  # Training examples: 0 positive, 0 negative
% 0.20/0.39  # Parsed axioms                        : 5
% 0.20/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.39  # Initial clauses                      : 16
% 0.20/0.39  # Removed in clause preprocessing      : 1
% 0.20/0.39  # Initial clauses in saturation        : 15
% 0.20/0.39  # Processed clauses                    : 28
% 0.20/0.39  # ...of these trivial                  : 0
% 0.20/0.39  # ...subsumed                          : 0
% 0.20/0.39  # ...remaining for further processing  : 28
% 0.20/0.39  # Other redundant clauses eliminated   : 5
% 0.20/0.39  # Clauses deleted for lack of memory   : 0
% 0.20/0.39  # Backward-subsumed                    : 1
% 0.20/0.39  # Backward-rewritten                   : 7
% 0.20/0.39  # Generated clauses                    : 17
% 0.20/0.39  # ...of the previous two non-trivial   : 15
% 0.20/0.39  # Contextual simplify-reflections      : 0
% 0.20/0.39  # Paramodulations                      : 14
% 0.20/0.39  # Factorizations                       : 0
% 0.20/0.39  # Equation resolutions                 : 5
% 0.20/0.39  # Propositional unsat checks           : 0
% 0.20/0.39  #    Propositional check models        : 0
% 0.20/0.39  #    Propositional check unsatisfiable : 0
% 0.20/0.39  #    Propositional clauses             : 0
% 0.20/0.39  #    Propositional clauses after purity: 0
% 0.20/0.39  #    Propositional unsat core size     : 0
% 0.20/0.39  #    Propositional preprocessing time  : 0.000
% 0.20/0.39  #    Propositional encoding time       : 0.000
% 0.20/0.39  #    Propositional solver time         : 0.000
% 0.20/0.39  #    Success case prop preproc time    : 0.000
% 0.20/0.39  #    Success case prop encoding time   : 0.000
% 0.20/0.39  #    Success case prop solver time     : 0.000
% 0.20/0.39  # Current number of processed clauses  : 17
% 0.20/0.39  #    Positive orientable unit clauses  : 7
% 0.20/0.39  #    Positive unorientable unit clauses: 0
% 0.20/0.39  #    Negative unit clauses             : 1
% 0.20/0.39  #    Non-unit-clauses                  : 9
% 0.20/0.39  # Current number of unprocessed clauses: 2
% 0.20/0.39  # ...number of literals in the above   : 8
% 0.20/0.39  # Current number of archived formulas  : 0
% 0.20/0.39  # Current number of archived clauses   : 9
% 0.20/0.39  # Clause-clause subsumption calls (NU) : 17
% 0.20/0.39  # Rec. Clause-clause subsumption calls : 14
% 0.20/0.39  # Non-unit clause-clause subsumptions  : 1
% 0.20/0.39  # Unit Clause-clause subsumption calls : 6
% 0.20/0.39  # Rewrite failures with RHS unbound    : 0
% 0.20/0.39  # BW rewrite match attempts            : 5
% 0.20/0.39  # BW rewrite match successes           : 2
% 0.20/0.39  # Condensation attempts                : 0
% 0.20/0.39  # Condensation successes               : 0
% 0.20/0.39  # Termbank termtop insertions          : 1198
% 0.20/0.39  
% 0.20/0.39  # -------------------------------------------------
% 0.20/0.39  # User time                : 0.054 s
% 0.20/0.39  # System time              : 0.003 s
% 0.20/0.39  # Total time               : 0.057 s
% 0.20/0.39  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
