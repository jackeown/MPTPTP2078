%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:26 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   37 ( 202 expanded)
%              Number of clauses        :   20 (  74 expanded)
%              Number of leaves         :    8 (  51 expanded)
%              Depth                    :    9
%              Number of atoms          :  116 ( 729 expanded)
%              Number of equality atoms :    8 (  16 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t34_ordinal1,conjecture,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r2_hidden(X1,k1_ordinal1(X2))
          <=> r1_ordinal1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).

fof(t13_ordinal1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,k1_ordinal1(X2))
    <=> ( r2_hidden(X1,X2)
        | X1 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).

fof(redefinition_r1_ordinal1,axiom,(
    ! [X1,X2] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X2) )
     => ( r1_ordinal1(X1,X2)
      <=> r1_tarski(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(t26_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r1_ordinal1(X1,X2)
            | r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).

fof(t33_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r2_hidden(X1,X2)
          <=> r1_ordinal1(k1_ordinal1(X1),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_ordinal1)).

fof(fc2_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ( ~ v1_xboole_0(k1_ordinal1(X1))
        & v3_ordinal1(k1_ordinal1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_ordinal1)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(antisymmetry_r2_hidden,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
        ( v3_ordinal1(X1)
       => ! [X2] :
            ( v3_ordinal1(X2)
           => ( r2_hidden(X1,k1_ordinal1(X2))
            <=> r1_ordinal1(X1,X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t34_ordinal1])).

fof(c_0_9,plain,(
    ! [X9,X10] :
      ( ( ~ r2_hidden(X9,k1_ordinal1(X10))
        | r2_hidden(X9,X10)
        | X9 = X10 )
      & ( ~ r2_hidden(X9,X10)
        | r2_hidden(X9,k1_ordinal1(X10)) )
      & ( X9 != X10
        | r2_hidden(X9,k1_ordinal1(X10)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_ordinal1])])])).

fof(c_0_10,negated_conjecture,
    ( v3_ordinal1(esk1_0)
    & v3_ordinal1(esk2_0)
    & ( ~ r2_hidden(esk1_0,k1_ordinal1(esk2_0))
      | ~ r1_ordinal1(esk1_0,esk2_0) )
    & ( r2_hidden(esk1_0,k1_ordinal1(esk2_0))
      | r1_ordinal1(esk1_0,esk2_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

fof(c_0_11,plain,(
    ! [X6,X7] :
      ( ( ~ r1_ordinal1(X6,X7)
        | r1_tarski(X6,X7)
        | ~ v3_ordinal1(X6)
        | ~ v3_ordinal1(X7) )
      & ( ~ r1_tarski(X6,X7)
        | r1_ordinal1(X6,X7)
        | ~ v3_ordinal1(X6)
        | ~ v3_ordinal1(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).

cnf(c_0_12,plain,
    ( r2_hidden(X1,X2)
    | X1 = X2
    | ~ r2_hidden(X1,k1_ordinal1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( r2_hidden(esk1_0,k1_ordinal1(esk2_0))
    | r1_ordinal1(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_14,plain,(
    ! [X11,X12] :
      ( ~ v3_ordinal1(X11)
      | ~ v3_ordinal1(X12)
      | r1_ordinal1(X11,X12)
      | r2_hidden(X12,X11) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_ordinal1])])])).

fof(c_0_15,plain,(
    ! [X13,X14] :
      ( ( ~ r2_hidden(X13,X14)
        | r1_ordinal1(k1_ordinal1(X13),X14)
        | ~ v3_ordinal1(X14)
        | ~ v3_ordinal1(X13) )
      & ( ~ r1_ordinal1(k1_ordinal1(X13),X14)
        | r2_hidden(X13,X14)
        | ~ v3_ordinal1(X14)
        | ~ v3_ordinal1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t33_ordinal1])])])])).

fof(c_0_16,plain,(
    ! [X5] :
      ( ( ~ v1_xboole_0(k1_ordinal1(X5))
        | ~ v3_ordinal1(X5) )
      & ( v3_ordinal1(k1_ordinal1(X5))
        | ~ v3_ordinal1(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_ordinal1])])])])).

fof(c_0_17,plain,(
    ! [X15,X16] :
      ( ~ r2_hidden(X15,X16)
      | ~ r1_tarski(X16,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_18,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,negated_conjecture,
    ( esk1_0 = esk2_0
    | r1_ordinal1(esk1_0,esk2_0)
    | r2_hidden(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( v3_ordinal1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_21,negated_conjecture,
    ( v3_ordinal1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_22,plain,(
    ! [X3,X4] :
      ( ~ r2_hidden(X3,X4)
      | ~ r2_hidden(X4,X3) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[antisymmetry_r2_hidden])])])).

cnf(c_0_23,negated_conjecture,
    ( ~ r2_hidden(esk1_0,k1_ordinal1(esk2_0))
    | ~ r1_ordinal1(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_24,plain,
    ( r1_ordinal1(X1,X2)
    | r2_hidden(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_ordinal1(k1_ordinal1(X1),X2)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,plain,
    ( v3_ordinal1(k1_ordinal1(X1))
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_27,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,negated_conjecture,
    ( esk1_0 = esk2_0
    | r1_tarski(esk1_0,esk2_0)
    | r2_hidden(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20]),c_0_21])])).

cnf(c_0_29,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk2_0,esk1_0)
    | ~ r2_hidden(esk1_0,k1_ordinal1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_20]),c_0_21])])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,k1_ordinal1(X2))
    | r2_hidden(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_24]),c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( esk1_0 = esk2_0
    | ~ r2_hidden(esk2_0,esk1_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_21]),c_0_20])])).

cnf(c_0_34,negated_conjecture,
    ( esk1_0 = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_33])])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk2_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_36,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_35]),c_0_35])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:44:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic G_____0026_C18_F1_SE_CS_SP_S4S
% 0.14/0.38  # and selection function SelectNewComplexAHPNS.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.027 s
% 0.14/0.38  
% 0.14/0.38  # Proof found!
% 0.14/0.38  # SZS status Theorem
% 0.14/0.38  # SZS output start CNFRefutation
% 0.14/0.38  fof(t34_ordinal1, conjecture, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,k1_ordinal1(X2))<=>r1_ordinal1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_ordinal1)).
% 0.14/0.38  fof(t13_ordinal1, axiom, ![X1, X2]:(r2_hidden(X1,k1_ordinal1(X2))<=>(r2_hidden(X1,X2)|X1=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_ordinal1)).
% 0.14/0.38  fof(redefinition_r1_ordinal1, axiom, ![X1, X2]:((v3_ordinal1(X1)&v3_ordinal1(X2))=>(r1_ordinal1(X1,X2)<=>r1_tarski(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 0.14/0.38  fof(t26_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r1_ordinal1(X1,X2)|r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_ordinal1)).
% 0.14/0.38  fof(t33_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,X2)<=>r1_ordinal1(k1_ordinal1(X1),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_ordinal1)).
% 0.14/0.38  fof(fc2_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>(~(v1_xboole_0(k1_ordinal1(X1)))&v3_ordinal1(k1_ordinal1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_ordinal1)).
% 0.14/0.38  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.14/0.38  fof(antisymmetry_r2_hidden, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 0.14/0.38  fof(c_0_8, negated_conjecture, ~(![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,k1_ordinal1(X2))<=>r1_ordinal1(X1,X2))))), inference(assume_negation,[status(cth)],[t34_ordinal1])).
% 0.14/0.38  fof(c_0_9, plain, ![X9, X10]:((~r2_hidden(X9,k1_ordinal1(X10))|(r2_hidden(X9,X10)|X9=X10))&((~r2_hidden(X9,X10)|r2_hidden(X9,k1_ordinal1(X10)))&(X9!=X10|r2_hidden(X9,k1_ordinal1(X10))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_ordinal1])])])).
% 0.14/0.38  fof(c_0_10, negated_conjecture, (v3_ordinal1(esk1_0)&(v3_ordinal1(esk2_0)&((~r2_hidden(esk1_0,k1_ordinal1(esk2_0))|~r1_ordinal1(esk1_0,esk2_0))&(r2_hidden(esk1_0,k1_ordinal1(esk2_0))|r1_ordinal1(esk1_0,esk2_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.14/0.38  fof(c_0_11, plain, ![X6, X7]:((~r1_ordinal1(X6,X7)|r1_tarski(X6,X7)|(~v3_ordinal1(X6)|~v3_ordinal1(X7)))&(~r1_tarski(X6,X7)|r1_ordinal1(X6,X7)|(~v3_ordinal1(X6)|~v3_ordinal1(X7)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).
% 0.14/0.38  cnf(c_0_12, plain, (r2_hidden(X1,X2)|X1=X2|~r2_hidden(X1,k1_ordinal1(X2))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.38  cnf(c_0_13, negated_conjecture, (r2_hidden(esk1_0,k1_ordinal1(esk2_0))|r1_ordinal1(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.38  fof(c_0_14, plain, ![X11, X12]:(~v3_ordinal1(X11)|(~v3_ordinal1(X12)|(r1_ordinal1(X11,X12)|r2_hidden(X12,X11)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_ordinal1])])])).
% 0.14/0.38  fof(c_0_15, plain, ![X13, X14]:((~r2_hidden(X13,X14)|r1_ordinal1(k1_ordinal1(X13),X14)|~v3_ordinal1(X14)|~v3_ordinal1(X13))&(~r1_ordinal1(k1_ordinal1(X13),X14)|r2_hidden(X13,X14)|~v3_ordinal1(X14)|~v3_ordinal1(X13))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t33_ordinal1])])])])).
% 0.14/0.38  fof(c_0_16, plain, ![X5]:((~v1_xboole_0(k1_ordinal1(X5))|~v3_ordinal1(X5))&(v3_ordinal1(k1_ordinal1(X5))|~v3_ordinal1(X5))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_ordinal1])])])])).
% 0.14/0.38  fof(c_0_17, plain, ![X15, X16]:(~r2_hidden(X15,X16)|~r1_tarski(X16,X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.14/0.38  cnf(c_0_18, plain, (r1_tarski(X1,X2)|~r1_ordinal1(X1,X2)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.38  cnf(c_0_19, negated_conjecture, (esk1_0=esk2_0|r1_ordinal1(esk1_0,esk2_0)|r2_hidden(esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.14/0.38  cnf(c_0_20, negated_conjecture, (v3_ordinal1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.38  cnf(c_0_21, negated_conjecture, (v3_ordinal1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.38  fof(c_0_22, plain, ![X3, X4]:(~r2_hidden(X3,X4)|~r2_hidden(X4,X3)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[antisymmetry_r2_hidden])])])).
% 0.14/0.38  cnf(c_0_23, negated_conjecture, (~r2_hidden(esk1_0,k1_ordinal1(esk2_0))|~r1_ordinal1(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.38  cnf(c_0_24, plain, (r1_ordinal1(X1,X2)|r2_hidden(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.38  cnf(c_0_25, plain, (r2_hidden(X1,X2)|~r1_ordinal1(k1_ordinal1(X1),X2)|~v3_ordinal1(X2)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.38  cnf(c_0_26, plain, (v3_ordinal1(k1_ordinal1(X1))|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.38  cnf(c_0_27, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.38  cnf(c_0_28, negated_conjecture, (esk1_0=esk2_0|r1_tarski(esk1_0,esk2_0)|r2_hidden(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20]), c_0_21])])).
% 0.14/0.38  cnf(c_0_29, plain, (~r2_hidden(X1,X2)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.38  cnf(c_0_30, negated_conjecture, (r2_hidden(esk2_0,esk1_0)|~r2_hidden(esk1_0,k1_ordinal1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_20]), c_0_21])])).
% 0.14/0.38  cnf(c_0_31, plain, (r2_hidden(X1,k1_ordinal1(X2))|r2_hidden(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_24]), c_0_26])).
% 0.14/0.38  cnf(c_0_32, negated_conjecture, (esk1_0=esk2_0|~r2_hidden(esk2_0,esk1_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29])).
% 0.14/0.38  cnf(c_0_33, negated_conjecture, (r2_hidden(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_21]), c_0_20])])).
% 0.14/0.38  cnf(c_0_34, negated_conjecture, (esk1_0=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_33])])).
% 0.14/0.38  cnf(c_0_35, negated_conjecture, (r2_hidden(esk2_0,esk2_0)), inference(rw,[status(thm)],[c_0_33, c_0_34])).
% 0.14/0.38  cnf(c_0_36, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_35]), c_0_35])]), ['proof']).
% 0.14/0.38  # SZS output end CNFRefutation
% 0.14/0.38  # Proof object total steps             : 37
% 0.14/0.38  # Proof object clause steps            : 20
% 0.14/0.38  # Proof object formula steps           : 17
% 0.14/0.38  # Proof object conjectures             : 15
% 0.14/0.38  # Proof object clause conjectures      : 12
% 0.14/0.38  # Proof object formula conjectures     : 3
% 0.14/0.38  # Proof object initial clauses used    : 11
% 0.14/0.38  # Proof object initial formulas used   : 8
% 0.14/0.38  # Proof object generating inferences   : 7
% 0.14/0.38  # Proof object simplifying inferences  : 16
% 0.14/0.38  # Training examples: 0 positive, 0 negative
% 0.14/0.38  # Parsed axioms                        : 9
% 0.14/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.38  # Initial clauses                      : 17
% 0.14/0.38  # Removed in clause preprocessing      : 0
% 0.14/0.38  # Initial clauses in saturation        : 17
% 0.14/0.38  # Processed clauses                    : 84
% 0.14/0.38  # ...of these trivial                  : 0
% 0.14/0.38  # ...subsumed                          : 11
% 0.14/0.38  # ...remaining for further processing  : 73
% 0.14/0.38  # Other redundant clauses eliminated   : 1
% 0.14/0.38  # Clauses deleted for lack of memory   : 0
% 0.14/0.38  # Backward-subsumed                    : 6
% 0.14/0.38  # Backward-rewritten                   : 25
% 0.14/0.38  # Generated clauses                    : 122
% 0.14/0.38  # ...of the previous two non-trivial   : 106
% 0.14/0.38  # Contextual simplify-reflections      : 6
% 0.14/0.38  # Paramodulations                      : 121
% 0.14/0.38  # Factorizations                       : 0
% 0.14/0.38  # Equation resolutions                 : 1
% 0.14/0.38  # Propositional unsat checks           : 0
% 0.14/0.38  #    Propositional check models        : 0
% 0.14/0.38  #    Propositional check unsatisfiable : 0
% 0.14/0.38  #    Propositional clauses             : 0
% 0.14/0.38  #    Propositional clauses after purity: 0
% 0.14/0.38  #    Propositional unsat core size     : 0
% 0.14/0.38  #    Propositional preprocessing time  : 0.000
% 0.14/0.38  #    Propositional encoding time       : 0.000
% 0.14/0.38  #    Propositional solver time         : 0.000
% 0.14/0.38  #    Success case prop preproc time    : 0.000
% 0.14/0.38  #    Success case prop encoding time   : 0.000
% 0.14/0.38  #    Success case prop solver time     : 0.000
% 0.14/0.38  # Current number of processed clauses  : 41
% 0.14/0.38  #    Positive orientable unit clauses  : 13
% 0.14/0.38  #    Positive unorientable unit clauses: 0
% 0.14/0.38  #    Negative unit clauses             : 10
% 0.14/0.38  #    Non-unit-clauses                  : 18
% 0.14/0.38  # Current number of unprocessed clauses: 38
% 0.14/0.38  # ...number of literals in the above   : 106
% 0.14/0.38  # Current number of archived formulas  : 0
% 0.14/0.38  # Current number of archived clauses   : 31
% 0.14/0.38  # Clause-clause subsumption calls (NU) : 231
% 0.14/0.38  # Rec. Clause-clause subsumption calls : 214
% 0.14/0.38  # Non-unit clause-clause subsumptions  : 23
% 0.14/0.38  # Unit Clause-clause subsumption calls : 9
% 0.14/0.38  # Rewrite failures with RHS unbound    : 0
% 0.14/0.38  # BW rewrite match attempts            : 59
% 0.14/0.38  # BW rewrite match successes           : 2
% 0.14/0.38  # Condensation attempts                : 0
% 0.14/0.38  # Condensation successes               : 0
% 0.14/0.38  # Termbank termtop insertions          : 3118
% 0.14/0.38  
% 0.14/0.38  # -------------------------------------------------
% 0.14/0.38  # User time                : 0.032 s
% 0.14/0.38  # System time              : 0.003 s
% 0.14/0.38  # Total time               : 0.035 s
% 0.14/0.38  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
