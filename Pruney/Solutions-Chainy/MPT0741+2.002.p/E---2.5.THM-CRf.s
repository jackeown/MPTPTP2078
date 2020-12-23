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
% DateTime   : Thu Dec  3 10:56:13 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 144 expanded)
%              Number of clauses        :   29 (  58 expanded)
%              Number of leaves         :    9 (  37 expanded)
%              Depth                    :   10
%              Number of atoms          :  165 ( 560 expanded)
%              Number of equality atoms :   13 (  25 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t31_ordinal1,conjecture,(
    ! [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
         => ( v3_ordinal1(X2)
            & r1_tarski(X2,X1) ) )
     => v3_ordinal1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_ordinal1)).

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

fof(d2_ordinal1,axiom,(
    ! [X1] :
      ( v1_ordinal1(X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
         => r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_ordinal1)).

fof(d8_xboole_0,axiom,(
    ! [X1,X2] :
      ( r2_xboole_0(X1,X2)
    <=> ( r1_tarski(X1,X2)
        & X1 != X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(d3_ordinal1,axiom,(
    ! [X1] :
      ( v2_ordinal1(X1)
    <=> ! [X2,X3] :
          ~ ( r2_hidden(X2,X1)
            & r2_hidden(X3,X1)
            & ~ r2_hidden(X2,X3)
            & X2 != X3
            & ~ r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_ordinal1)).

fof(cc2_ordinal1,axiom,(
    ! [X1] :
      ( ( v1_ordinal1(X1)
        & v2_ordinal1(X1) )
     => v3_ordinal1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_ordinal1)).

fof(t21_ordinal1,axiom,(
    ! [X1] :
      ( v1_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r2_xboole_0(X1,X2)
           => r2_hidden(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_ordinal1)).

fof(cc1_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ( v1_ordinal1(X1)
        & v2_ordinal1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( ! [X2] :
            ( r2_hidden(X2,X1)
           => ( v3_ordinal1(X2)
              & r1_tarski(X2,X1) ) )
       => v3_ordinal1(X1) ) ),
    inference(assume_negation,[status(cth)],[t31_ordinal1])).

fof(c_0_10,plain,(
    ! [X18,X19] :
      ( ( ~ r1_ordinal1(X18,X19)
        | r1_tarski(X18,X19)
        | ~ v3_ordinal1(X18)
        | ~ v3_ordinal1(X19) )
      & ( ~ r1_tarski(X18,X19)
        | r1_ordinal1(X18,X19)
        | ~ v3_ordinal1(X18)
        | ~ v3_ordinal1(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).

fof(c_0_11,plain,(
    ! [X22,X23] :
      ( ~ v3_ordinal1(X22)
      | ~ v3_ordinal1(X23)
      | r1_ordinal1(X22,X23)
      | r2_hidden(X23,X22) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_ordinal1])])])).

fof(c_0_12,negated_conjecture,(
    ! [X25] :
      ( ( v3_ordinal1(X25)
        | ~ r2_hidden(X25,esk4_0) )
      & ( r1_tarski(X25,esk4_0)
        | ~ r2_hidden(X25,esk4_0) )
      & ~ v3_ordinal1(esk4_0) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])])])).

fof(c_0_13,plain,(
    ! [X8,X9,X10] :
      ( ( ~ v1_ordinal1(X8)
        | ~ r2_hidden(X9,X8)
        | r1_tarski(X9,X8) )
      & ( r2_hidden(esk1_1(X10),X10)
        | v1_ordinal1(X10) )
      & ( ~ r1_tarski(esk1_1(X10),X10)
        | v1_ordinal1(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_ordinal1])])])])])])).

fof(c_0_14,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | ~ r2_xboole_0(X4,X5) )
      & ( X4 != X5
        | ~ r2_xboole_0(X4,X5) )
      & ( ~ r1_tarski(X4,X5)
        | X4 = X5
        | r2_xboole_0(X4,X5) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).

cnf(c_0_15,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( r1_ordinal1(X1,X2)
    | r2_hidden(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_17,plain,(
    ! [X12,X13,X14,X15] :
      ( ( ~ v2_ordinal1(X12)
        | ~ r2_hidden(X13,X12)
        | ~ r2_hidden(X14,X12)
        | r2_hidden(X13,X14)
        | X13 = X14
        | r2_hidden(X14,X13) )
      & ( r2_hidden(esk2_1(X15),X15)
        | v2_ordinal1(X15) )
      & ( r2_hidden(esk3_1(X15),X15)
        | v2_ordinal1(X15) )
      & ( ~ r2_hidden(esk2_1(X15),esk3_1(X15))
        | v2_ordinal1(X15) )
      & ( esk2_1(X15) != esk3_1(X15)
        | v2_ordinal1(X15) )
      & ( ~ r2_hidden(esk3_1(X15),esk2_1(X15))
        | v2_ordinal1(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d3_ordinal1])])])])])])])).

fof(c_0_18,plain,(
    ! [X7] :
      ( ~ v1_ordinal1(X7)
      | ~ v2_ordinal1(X7)
      | v3_ordinal1(X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_ordinal1])])).

cnf(c_0_19,negated_conjecture,
    ( r1_tarski(X1,esk4_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( v1_ordinal1(X1)
    | ~ r1_tarski(esk1_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_22,plain,(
    ! [X20,X21] :
      ( ~ v1_ordinal1(X20)
      | ~ v3_ordinal1(X21)
      | ~ r2_xboole_0(X20,X21)
      | r2_hidden(X20,X21) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_ordinal1])])])).

cnf(c_0_23,plain,
    ( X1 = X2
    | r2_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,X2)
    | r1_tarski(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

fof(c_0_25,plain,(
    ! [X6] :
      ( ( v1_ordinal1(X6)
        | ~ v3_ordinal1(X6) )
      & ( v2_ordinal1(X6)
        | ~ v3_ordinal1(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_ordinal1])])])).

cnf(c_0_26,negated_conjecture,
    ( v3_ordinal1(X1)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_27,plain,
    ( r2_hidden(esk3_1(X1),X1)
    | v2_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,plain,
    ( v3_ordinal1(X1)
    | ~ v1_ordinal1(X1)
    | ~ v2_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,negated_conjecture,
    ( v1_ordinal1(esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])).

cnf(c_0_30,negated_conjecture,
    ( ~ v3_ordinal1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,X2)
    | ~ v1_ordinal1(X1)
    | ~ v3_ordinal1(X2)
    | ~ r2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( X1 = X2
    | r2_hidden(X2,X1)
    | r2_xboole_0(X1,X2)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_33,plain,
    ( v1_ordinal1(X1)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,negated_conjecture,
    ( v2_ordinal1(esk4_0)
    | v3_ordinal1(esk3_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_35,negated_conjecture,
    ( ~ v2_ordinal1(esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])).

cnf(c_0_36,plain,
    ( r2_hidden(esk2_1(X1),X1)
    | v2_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_37,plain,
    ( X1 = X2
    | r2_hidden(X2,X1)
    | r2_hidden(X1,X2)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])).

cnf(c_0_38,negated_conjecture,
    ( v3_ordinal1(esk3_1(esk4_0)) ),
    inference(sr,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_39,negated_conjecture,
    ( v2_ordinal1(esk4_0)
    | v3_ordinal1(esk2_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_36])).

cnf(c_0_40,plain,
    ( v2_ordinal1(X1)
    | ~ r2_hidden(esk3_1(X1),esk2_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_41,negated_conjecture,
    ( esk3_1(esk4_0) = X1
    | r2_hidden(esk3_1(esk4_0),X1)
    | r2_hidden(X1,esk3_1(esk4_0))
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_42,negated_conjecture,
    ( v3_ordinal1(esk2_1(esk4_0)) ),
    inference(sr,[status(thm)],[c_0_39,c_0_35])).

cnf(c_0_43,plain,
    ( v2_ordinal1(X1)
    | ~ r2_hidden(esk2_1(X1),esk3_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_44,negated_conjecture,
    ( esk3_1(esk4_0) = esk2_1(esk4_0)
    | r2_hidden(esk2_1(esk4_0),esk3_1(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])]),c_0_35])).

cnf(c_0_45,plain,
    ( v2_ordinal1(X1)
    | esk2_1(X1) != esk3_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_46,negated_conjecture,
    ( esk3_1(esk4_0) = esk2_1(esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_35])).

cnf(c_0_47,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_35]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:01:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_____0026_C18_F1_SE_CS_SP_S4S
% 0.13/0.38  # and selection function SelectNewComplexAHPNS.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.027 s
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t31_ordinal1, conjecture, ![X1]:(![X2]:(r2_hidden(X2,X1)=>(v3_ordinal1(X2)&r1_tarski(X2,X1)))=>v3_ordinal1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_ordinal1)).
% 0.13/0.38  fof(redefinition_r1_ordinal1, axiom, ![X1, X2]:((v3_ordinal1(X1)&v3_ordinal1(X2))=>(r1_ordinal1(X1,X2)<=>r1_tarski(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 0.13/0.38  fof(t26_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r1_ordinal1(X1,X2)|r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_ordinal1)).
% 0.13/0.38  fof(d2_ordinal1, axiom, ![X1]:(v1_ordinal1(X1)<=>![X2]:(r2_hidden(X2,X1)=>r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_ordinal1)).
% 0.13/0.38  fof(d8_xboole_0, axiom, ![X1, X2]:(r2_xboole_0(X1,X2)<=>(r1_tarski(X1,X2)&X1!=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 0.13/0.38  fof(d3_ordinal1, axiom, ![X1]:(v2_ordinal1(X1)<=>![X2, X3]:~(((((r2_hidden(X2,X1)&r2_hidden(X3,X1))&~(r2_hidden(X2,X3)))&X2!=X3)&~(r2_hidden(X3,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_ordinal1)).
% 0.13/0.38  fof(cc2_ordinal1, axiom, ![X1]:((v1_ordinal1(X1)&v2_ordinal1(X1))=>v3_ordinal1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_ordinal1)).
% 0.13/0.38  fof(t21_ordinal1, axiom, ![X1]:(v1_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_xboole_0(X1,X2)=>r2_hidden(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_ordinal1)).
% 0.13/0.38  fof(cc1_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>(v1_ordinal1(X1)&v2_ordinal1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_ordinal1)).
% 0.13/0.38  fof(c_0_9, negated_conjecture, ~(![X1]:(![X2]:(r2_hidden(X2,X1)=>(v3_ordinal1(X2)&r1_tarski(X2,X1)))=>v3_ordinal1(X1))), inference(assume_negation,[status(cth)],[t31_ordinal1])).
% 0.13/0.38  fof(c_0_10, plain, ![X18, X19]:((~r1_ordinal1(X18,X19)|r1_tarski(X18,X19)|(~v3_ordinal1(X18)|~v3_ordinal1(X19)))&(~r1_tarski(X18,X19)|r1_ordinal1(X18,X19)|(~v3_ordinal1(X18)|~v3_ordinal1(X19)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).
% 0.13/0.38  fof(c_0_11, plain, ![X22, X23]:(~v3_ordinal1(X22)|(~v3_ordinal1(X23)|(r1_ordinal1(X22,X23)|r2_hidden(X23,X22)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_ordinal1])])])).
% 0.13/0.38  fof(c_0_12, negated_conjecture, ![X25]:(((v3_ordinal1(X25)|~r2_hidden(X25,esk4_0))&(r1_tarski(X25,esk4_0)|~r2_hidden(X25,esk4_0)))&~v3_ordinal1(esk4_0)), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])])])).
% 0.13/0.38  fof(c_0_13, plain, ![X8, X9, X10]:((~v1_ordinal1(X8)|(~r2_hidden(X9,X8)|r1_tarski(X9,X8)))&((r2_hidden(esk1_1(X10),X10)|v1_ordinal1(X10))&(~r1_tarski(esk1_1(X10),X10)|v1_ordinal1(X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_ordinal1])])])])])])).
% 0.13/0.38  fof(c_0_14, plain, ![X4, X5]:(((r1_tarski(X4,X5)|~r2_xboole_0(X4,X5))&(X4!=X5|~r2_xboole_0(X4,X5)))&(~r1_tarski(X4,X5)|X4=X5|r2_xboole_0(X4,X5))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).
% 0.13/0.38  cnf(c_0_15, plain, (r1_tarski(X1,X2)|~r1_ordinal1(X1,X2)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.38  cnf(c_0_16, plain, (r1_ordinal1(X1,X2)|r2_hidden(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  fof(c_0_17, plain, ![X12, X13, X14, X15]:((~v2_ordinal1(X12)|(~r2_hidden(X13,X12)|~r2_hidden(X14,X12)|r2_hidden(X13,X14)|X13=X14|r2_hidden(X14,X13)))&(((((r2_hidden(esk2_1(X15),X15)|v2_ordinal1(X15))&(r2_hidden(esk3_1(X15),X15)|v2_ordinal1(X15)))&(~r2_hidden(esk2_1(X15),esk3_1(X15))|v2_ordinal1(X15)))&(esk2_1(X15)!=esk3_1(X15)|v2_ordinal1(X15)))&(~r2_hidden(esk3_1(X15),esk2_1(X15))|v2_ordinal1(X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d3_ordinal1])])])])])])])).
% 0.13/0.38  fof(c_0_18, plain, ![X7]:(~v1_ordinal1(X7)|~v2_ordinal1(X7)|v3_ordinal1(X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_ordinal1])])).
% 0.13/0.38  cnf(c_0_19, negated_conjecture, (r1_tarski(X1,esk4_0)|~r2_hidden(X1,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_20, plain, (r2_hidden(esk1_1(X1),X1)|v1_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_21, plain, (v1_ordinal1(X1)|~r1_tarski(esk1_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  fof(c_0_22, plain, ![X20, X21]:(~v1_ordinal1(X20)|(~v3_ordinal1(X21)|(~r2_xboole_0(X20,X21)|r2_hidden(X20,X21)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_ordinal1])])])).
% 0.13/0.38  cnf(c_0_23, plain, (X1=X2|r2_xboole_0(X1,X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.38  cnf(c_0_24, plain, (r2_hidden(X1,X2)|r1_tarski(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.13/0.38  fof(c_0_25, plain, ![X6]:((v1_ordinal1(X6)|~v3_ordinal1(X6))&(v2_ordinal1(X6)|~v3_ordinal1(X6))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_ordinal1])])])).
% 0.13/0.38  cnf(c_0_26, negated_conjecture, (v3_ordinal1(X1)|~r2_hidden(X1,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_27, plain, (r2_hidden(esk3_1(X1),X1)|v2_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.38  cnf(c_0_28, plain, (v3_ordinal1(X1)|~v1_ordinal1(X1)|~v2_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.38  cnf(c_0_29, negated_conjecture, (v1_ordinal1(esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21])).
% 0.13/0.38  cnf(c_0_30, negated_conjecture, (~v3_ordinal1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_31, plain, (r2_hidden(X1,X2)|~v1_ordinal1(X1)|~v3_ordinal1(X2)|~r2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.38  cnf(c_0_32, plain, (X1=X2|r2_hidden(X2,X1)|r2_xboole_0(X1,X2)|~v3_ordinal1(X2)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.13/0.38  cnf(c_0_33, plain, (v1_ordinal1(X1)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.38  cnf(c_0_34, negated_conjecture, (v2_ordinal1(esk4_0)|v3_ordinal1(esk3_1(esk4_0))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.13/0.38  cnf(c_0_35, negated_conjecture, (~v2_ordinal1(esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30])).
% 0.13/0.38  cnf(c_0_36, plain, (r2_hidden(esk2_1(X1),X1)|v2_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.38  cnf(c_0_37, plain, (X1=X2|r2_hidden(X2,X1)|r2_hidden(X1,X2)|~v3_ordinal1(X2)|~v3_ordinal1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33])).
% 0.13/0.38  cnf(c_0_38, negated_conjecture, (v3_ordinal1(esk3_1(esk4_0))), inference(sr,[status(thm)],[c_0_34, c_0_35])).
% 0.13/0.38  cnf(c_0_39, negated_conjecture, (v2_ordinal1(esk4_0)|v3_ordinal1(esk2_1(esk4_0))), inference(spm,[status(thm)],[c_0_26, c_0_36])).
% 0.13/0.38  cnf(c_0_40, plain, (v2_ordinal1(X1)|~r2_hidden(esk3_1(X1),esk2_1(X1))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.38  cnf(c_0_41, negated_conjecture, (esk3_1(esk4_0)=X1|r2_hidden(esk3_1(esk4_0),X1)|r2_hidden(X1,esk3_1(esk4_0))|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.13/0.38  cnf(c_0_42, negated_conjecture, (v3_ordinal1(esk2_1(esk4_0))), inference(sr,[status(thm)],[c_0_39, c_0_35])).
% 0.13/0.38  cnf(c_0_43, plain, (v2_ordinal1(X1)|~r2_hidden(esk2_1(X1),esk3_1(X1))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.38  cnf(c_0_44, negated_conjecture, (esk3_1(esk4_0)=esk2_1(esk4_0)|r2_hidden(esk2_1(esk4_0),esk3_1(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42])]), c_0_35])).
% 0.13/0.38  cnf(c_0_45, plain, (v2_ordinal1(X1)|esk2_1(X1)!=esk3_1(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.38  cnf(c_0_46, negated_conjecture, (esk3_1(esk4_0)=esk2_1(esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_35])).
% 0.13/0.38  cnf(c_0_47, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_35]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 48
% 0.13/0.38  # Proof object clause steps            : 29
% 0.13/0.38  # Proof object formula steps           : 19
% 0.13/0.38  # Proof object conjectures             : 16
% 0.13/0.38  # Proof object clause conjectures      : 13
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 16
% 0.13/0.38  # Proof object initial formulas used   : 9
% 0.13/0.38  # Proof object generating inferences   : 11
% 0.13/0.38  # Proof object simplifying inferences  : 10
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 9
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 22
% 0.13/0.38  # Removed in clause preprocessing      : 0
% 0.13/0.38  # Initial clauses in saturation        : 22
% 0.13/0.38  # Processed clauses                    : 58
% 0.13/0.38  # ...of these trivial                  : 0
% 0.13/0.38  # ...subsumed                          : 12
% 0.13/0.38  # ...remaining for further processing  : 46
% 0.13/0.38  # Other redundant clauses eliminated   : 1
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 0
% 0.13/0.38  # Backward-rewritten                   : 6
% 0.13/0.38  # Generated clauses                    : 72
% 0.13/0.38  # ...of the previous two non-trivial   : 56
% 0.13/0.38  # Contextual simplify-reflections      : 2
% 0.13/0.38  # Paramodulations                      : 63
% 0.13/0.38  # Factorizations                       : 4
% 0.13/0.38  # Equation resolutions                 : 1
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 35
% 0.13/0.38  #    Positive orientable unit clauses  : 4
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 3
% 0.13/0.38  #    Non-unit-clauses                  : 28
% 0.13/0.38  # Current number of unprocessed clauses: 18
% 0.13/0.38  # ...number of literals in the above   : 105
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 10
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 232
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 107
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 9
% 0.13/0.38  # Unit Clause-clause subsumption calls : 45
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 2
% 0.13/0.38  # BW rewrite match successes           : 2
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 2188
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.029 s
% 0.13/0.38  # System time              : 0.004 s
% 0.13/0.38  # Total time               : 0.033 s
% 0.13/0.38  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
