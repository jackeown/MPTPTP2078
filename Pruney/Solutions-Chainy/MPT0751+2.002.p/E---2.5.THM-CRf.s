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
% DateTime   : Thu Dec  3 10:56:34 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 307 expanded)
%              Number of clauses        :   31 ( 125 expanded)
%              Number of leaves         :    9 (  77 expanded)
%              Depth                    :   13
%              Number of atoms          :  170 (1694 expanded)
%              Number of equality atoms :   24 ( 308 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t42_ordinal1,conjecture,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ( ~ ( ~ v4_ordinal1(X1)
            & ! [X2] :
                ( v3_ordinal1(X2)
               => X1 != k1_ordinal1(X2) ) )
        & ~ ( ? [X2] :
                ( v3_ordinal1(X2)
                & X1 = k1_ordinal1(X2) )
            & v4_ordinal1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_ordinal1)).

fof(t24_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ~ ( ~ r2_hidden(X1,X2)
              & X1 != X2
              & ~ r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).

fof(fc2_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ( ~ v1_xboole_0(k1_ordinal1(X1))
        & v3_ordinal1(k1_ordinal1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_ordinal1)).

fof(t41_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ( v4_ordinal1(X1)
      <=> ! [X2] :
            ( v3_ordinal1(X2)
           => ( r2_hidden(X2,X1)
             => r2_hidden(k1_ordinal1(X2),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_ordinal1)).

fof(t13_ordinal1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,k1_ordinal1(X2))
    <=> ( r2_hidden(X1,X2)
        | X1 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).

fof(antisymmetry_r2_hidden,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t10_ordinal1,axiom,(
    ! [X1] : r2_hidden(X1,k1_ordinal1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( v3_ordinal1(X1)
       => ( ~ ( ~ v4_ordinal1(X1)
              & ! [X2] :
                  ( v3_ordinal1(X2)
                 => X1 != k1_ordinal1(X2) ) )
          & ~ ( ? [X2] :
                  ( v3_ordinal1(X2)
                  & X1 = k1_ordinal1(X2) )
              & v4_ordinal1(X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t42_ordinal1])).

fof(c_0_10,plain,(
    ! [X16,X17] :
      ( ~ v3_ordinal1(X16)
      | ~ v3_ordinal1(X17)
      | r2_hidden(X16,X17)
      | X16 = X17
      | r2_hidden(X17,X16) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_ordinal1])])])])).

fof(c_0_11,negated_conjecture,(
    ! [X24] :
      ( v3_ordinal1(esk3_0)
      & ( v3_ordinal1(esk4_0)
        | ~ v4_ordinal1(esk3_0) )
      & ( esk3_0 = k1_ordinal1(esk4_0)
        | ~ v4_ordinal1(esk3_0) )
      & ( v4_ordinal1(esk3_0)
        | ~ v4_ordinal1(esk3_0) )
      & ( v3_ordinal1(esk4_0)
        | ~ v3_ordinal1(X24)
        | esk3_0 != k1_ordinal1(X24) )
      & ( esk3_0 = k1_ordinal1(esk4_0)
        | ~ v3_ordinal1(X24)
        | esk3_0 != k1_ordinal1(X24) )
      & ( v4_ordinal1(esk3_0)
        | ~ v3_ordinal1(X24)
        | esk3_0 != k1_ordinal1(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])])])).

cnf(c_0_12,plain,
    ( r2_hidden(X1,X2)
    | X1 = X2
    | r2_hidden(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( v3_ordinal1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_14,plain,(
    ! [X12] :
      ( ( ~ v1_xboole_0(k1_ordinal1(X12))
        | ~ v3_ordinal1(X12) )
      & ( v3_ordinal1(k1_ordinal1(X12))
        | ~ v3_ordinal1(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_ordinal1])])])])).

fof(c_0_15,plain,(
    ! [X18,X19] :
      ( ( ~ v4_ordinal1(X18)
        | ~ v3_ordinal1(X19)
        | ~ r2_hidden(X19,X18)
        | r2_hidden(k1_ordinal1(X19),X18)
        | ~ v3_ordinal1(X18) )
      & ( v3_ordinal1(esk2_1(X18))
        | v4_ordinal1(X18)
        | ~ v3_ordinal1(X18) )
      & ( r2_hidden(esk2_1(X18),X18)
        | v4_ordinal1(X18)
        | ~ v3_ordinal1(X18) )
      & ( ~ r2_hidden(k1_ordinal1(esk2_1(X18)),X18)
        | v4_ordinal1(X18)
        | ~ v3_ordinal1(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t41_ordinal1])])])])])).

cnf(c_0_16,negated_conjecture,
    ( X1 = esk3_0
    | r2_hidden(esk3_0,X1)
    | r2_hidden(X1,esk3_0)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_17,plain,
    ( v3_ordinal1(k1_ordinal1(X1))
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_18,plain,(
    ! [X14,X15] :
      ( ( ~ r2_hidden(X14,k1_ordinal1(X15))
        | r2_hidden(X14,X15)
        | X14 = X15 )
      & ( ~ r2_hidden(X14,X15)
        | r2_hidden(X14,k1_ordinal1(X15)) )
      & ( X14 != X15
        | r2_hidden(X14,k1_ordinal1(X15)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_ordinal1])])])).

cnf(c_0_19,plain,
    ( v4_ordinal1(X1)
    | ~ r2_hidden(k1_ordinal1(esk2_1(X1)),X1)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( k1_ordinal1(X1) = esk3_0
    | r2_hidden(k1_ordinal1(X1),esk3_0)
    | r2_hidden(esk3_0,k1_ordinal1(X1))
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( v4_ordinal1(esk3_0)
    | ~ v3_ordinal1(X1)
    | esk3_0 != k1_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_22,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,X5)
      | ~ r2_hidden(X5,X4) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[antisymmetry_r2_hidden])])])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,X2)
    | X1 = X2
    | ~ r2_hidden(X1,k1_ordinal1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( v4_ordinal1(esk3_0)
    | r2_hidden(esk3_0,k1_ordinal1(esk2_1(esk3_0)))
    | ~ v3_ordinal1(esk2_1(esk3_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_13])]),c_0_21])).

fof(c_0_25,plain,(
    ! [X6,X7,X8,X9,X10] :
      ( ( ~ r1_tarski(X6,X7)
        | ~ r2_hidden(X8,X6)
        | r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_2(X9,X10),X9)
        | r1_tarski(X9,X10) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | r1_tarski(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_26,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,plain,
    ( r2_hidden(esk2_1(X1),X1)
    | v4_ordinal1(X1)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_28,negated_conjecture,
    ( esk2_1(esk3_0) = esk3_0
    | v4_ordinal1(esk3_0)
    | r2_hidden(esk3_0,esk2_1(esk3_0))
    | ~ v3_ordinal1(esk2_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_29,plain,
    ( v3_ordinal1(esk2_1(X1))
    | v4_ordinal1(X1)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_30,plain,(
    ! [X21,X22] :
      ( ~ r2_hidden(X21,X22)
      | ~ r1_tarski(X22,X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,plain,
    ( v4_ordinal1(X1)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X1,esk2_1(X1)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( esk2_1(esk3_0) = esk3_0
    | v4_ordinal1(esk3_0)
    | r2_hidden(esk3_0,esk2_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_13])])).

cnf(c_0_35,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_37,negated_conjecture,
    ( esk2_1(esk3_0) = esk3_0
    | v4_ordinal1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_13])])).

cnf(c_0_38,plain,
    ( ~ r2_hidden(X1,X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

fof(c_0_39,plain,(
    ! [X13] : r2_hidden(X13,k1_ordinal1(X13)) ),
    inference(variable_rename,[status(thm)],[t10_ordinal1])).

cnf(c_0_40,negated_conjecture,
    ( esk3_0 = k1_ordinal1(esk4_0)
    | ~ v4_ordinal1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_41,negated_conjecture,
    ( v4_ordinal1(esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_37]),c_0_13])]),c_0_38])).

cnf(c_0_42,plain,
    ( r2_hidden(k1_ordinal1(X2),X1)
    | ~ v4_ordinal1(X1)
    | ~ v3_ordinal1(X2)
    | ~ r2_hidden(X2,X1)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_43,negated_conjecture,
    ( v3_ordinal1(esk4_0)
    | ~ v4_ordinal1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_44,plain,
    ( r2_hidden(X1,k1_ordinal1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_45,negated_conjecture,
    ( k1_ordinal1(esk4_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_41])])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(k1_ordinal1(X1),esk3_0)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_41]),c_0_13])])).

cnf(c_0_47,negated_conjecture,
    ( v3_ordinal1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_41])])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_49,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_45]),c_0_47]),c_0_48])]),c_0_38]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:05:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.20/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.027 s
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(t42_ordinal1, conjecture, ![X1]:(v3_ordinal1(X1)=>(~((~(v4_ordinal1(X1))&![X2]:(v3_ordinal1(X2)=>X1!=k1_ordinal1(X2))))&~((?[X2]:(v3_ordinal1(X2)&X1=k1_ordinal1(X2))&v4_ordinal1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_ordinal1)).
% 0.20/0.38  fof(t24_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>~(((~(r2_hidden(X1,X2))&X1!=X2)&~(r2_hidden(X2,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_ordinal1)).
% 0.20/0.38  fof(fc2_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>(~(v1_xboole_0(k1_ordinal1(X1)))&v3_ordinal1(k1_ordinal1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_ordinal1)).
% 0.20/0.38  fof(t41_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>(v4_ordinal1(X1)<=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X2,X1)=>r2_hidden(k1_ordinal1(X2),X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_ordinal1)).
% 0.20/0.38  fof(t13_ordinal1, axiom, ![X1, X2]:(r2_hidden(X1,k1_ordinal1(X2))<=>(r2_hidden(X1,X2)|X1=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_ordinal1)).
% 0.20/0.38  fof(antisymmetry_r2_hidden, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 0.20/0.38  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.38  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.20/0.38  fof(t10_ordinal1, axiom, ![X1]:r2_hidden(X1,k1_ordinal1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_ordinal1)).
% 0.20/0.38  fof(c_0_9, negated_conjecture, ~(![X1]:(v3_ordinal1(X1)=>(~((~(v4_ordinal1(X1))&![X2]:(v3_ordinal1(X2)=>X1!=k1_ordinal1(X2))))&~((?[X2]:(v3_ordinal1(X2)&X1=k1_ordinal1(X2))&v4_ordinal1(X1)))))), inference(assume_negation,[status(cth)],[t42_ordinal1])).
% 0.20/0.38  fof(c_0_10, plain, ![X16, X17]:(~v3_ordinal1(X16)|(~v3_ordinal1(X17)|(r2_hidden(X16,X17)|X16=X17|r2_hidden(X17,X16)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_ordinal1])])])])).
% 0.20/0.38  fof(c_0_11, negated_conjecture, ![X24]:(v3_ordinal1(esk3_0)&((((v3_ordinal1(esk4_0)|~v4_ordinal1(esk3_0))&(esk3_0=k1_ordinal1(esk4_0)|~v4_ordinal1(esk3_0)))&(v4_ordinal1(esk3_0)|~v4_ordinal1(esk3_0)))&(((v3_ordinal1(esk4_0)|(~v3_ordinal1(X24)|esk3_0!=k1_ordinal1(X24)))&(esk3_0=k1_ordinal1(esk4_0)|(~v3_ordinal1(X24)|esk3_0!=k1_ordinal1(X24))))&(v4_ordinal1(esk3_0)|(~v3_ordinal1(X24)|esk3_0!=k1_ordinal1(X24)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])])])).
% 0.20/0.38  cnf(c_0_12, plain, (r2_hidden(X1,X2)|X1=X2|r2_hidden(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.38  cnf(c_0_13, negated_conjecture, (v3_ordinal1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.38  fof(c_0_14, plain, ![X12]:((~v1_xboole_0(k1_ordinal1(X12))|~v3_ordinal1(X12))&(v3_ordinal1(k1_ordinal1(X12))|~v3_ordinal1(X12))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_ordinal1])])])])).
% 0.20/0.38  fof(c_0_15, plain, ![X18, X19]:((~v4_ordinal1(X18)|(~v3_ordinal1(X19)|(~r2_hidden(X19,X18)|r2_hidden(k1_ordinal1(X19),X18)))|~v3_ordinal1(X18))&((v3_ordinal1(esk2_1(X18))|v4_ordinal1(X18)|~v3_ordinal1(X18))&((r2_hidden(esk2_1(X18),X18)|v4_ordinal1(X18)|~v3_ordinal1(X18))&(~r2_hidden(k1_ordinal1(esk2_1(X18)),X18)|v4_ordinal1(X18)|~v3_ordinal1(X18))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t41_ordinal1])])])])])).
% 0.20/0.38  cnf(c_0_16, negated_conjecture, (X1=esk3_0|r2_hidden(esk3_0,X1)|r2_hidden(X1,esk3_0)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.20/0.38  cnf(c_0_17, plain, (v3_ordinal1(k1_ordinal1(X1))|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.38  fof(c_0_18, plain, ![X14, X15]:((~r2_hidden(X14,k1_ordinal1(X15))|(r2_hidden(X14,X15)|X14=X15))&((~r2_hidden(X14,X15)|r2_hidden(X14,k1_ordinal1(X15)))&(X14!=X15|r2_hidden(X14,k1_ordinal1(X15))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_ordinal1])])])).
% 0.20/0.38  cnf(c_0_19, plain, (v4_ordinal1(X1)|~r2_hidden(k1_ordinal1(esk2_1(X1)),X1)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.38  cnf(c_0_20, negated_conjecture, (k1_ordinal1(X1)=esk3_0|r2_hidden(k1_ordinal1(X1),esk3_0)|r2_hidden(esk3_0,k1_ordinal1(X1))|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.20/0.38  cnf(c_0_21, negated_conjecture, (v4_ordinal1(esk3_0)|~v3_ordinal1(X1)|esk3_0!=k1_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.38  fof(c_0_22, plain, ![X4, X5]:(~r2_hidden(X4,X5)|~r2_hidden(X5,X4)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[antisymmetry_r2_hidden])])])).
% 0.20/0.38  cnf(c_0_23, plain, (r2_hidden(X1,X2)|X1=X2|~r2_hidden(X1,k1_ordinal1(X2))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.38  cnf(c_0_24, negated_conjecture, (v4_ordinal1(esk3_0)|r2_hidden(esk3_0,k1_ordinal1(esk2_1(esk3_0)))|~v3_ordinal1(esk2_1(esk3_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_13])]), c_0_21])).
% 0.20/0.38  fof(c_0_25, plain, ![X6, X7, X8, X9, X10]:((~r1_tarski(X6,X7)|(~r2_hidden(X8,X6)|r2_hidden(X8,X7)))&((r2_hidden(esk1_2(X9,X10),X9)|r1_tarski(X9,X10))&(~r2_hidden(esk1_2(X9,X10),X10)|r1_tarski(X9,X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.38  cnf(c_0_26, plain, (~r2_hidden(X1,X2)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.38  cnf(c_0_27, plain, (r2_hidden(esk2_1(X1),X1)|v4_ordinal1(X1)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.38  cnf(c_0_28, negated_conjecture, (esk2_1(esk3_0)=esk3_0|v4_ordinal1(esk3_0)|r2_hidden(esk3_0,esk2_1(esk3_0))|~v3_ordinal1(esk2_1(esk3_0))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.20/0.38  cnf(c_0_29, plain, (v3_ordinal1(esk2_1(X1))|v4_ordinal1(X1)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.38  fof(c_0_30, plain, ![X21, X22]:(~r2_hidden(X21,X22)|~r1_tarski(X22,X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.20/0.38  cnf(c_0_31, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.38  cnf(c_0_32, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.38  cnf(c_0_33, plain, (v4_ordinal1(X1)|~v3_ordinal1(X1)|~r2_hidden(X1,esk2_1(X1))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.20/0.38  cnf(c_0_34, negated_conjecture, (esk2_1(esk3_0)=esk3_0|v4_ordinal1(esk3_0)|r2_hidden(esk3_0,esk2_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_13])])).
% 0.20/0.38  cnf(c_0_35, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.38  cnf(c_0_36, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.20/0.38  cnf(c_0_37, negated_conjecture, (esk2_1(esk3_0)=esk3_0|v4_ordinal1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_13])])).
% 0.20/0.38  cnf(c_0_38, plain, (~r2_hidden(X1,X1)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.20/0.38  fof(c_0_39, plain, ![X13]:r2_hidden(X13,k1_ordinal1(X13)), inference(variable_rename,[status(thm)],[t10_ordinal1])).
% 0.20/0.38  cnf(c_0_40, negated_conjecture, (esk3_0=k1_ordinal1(esk4_0)|~v4_ordinal1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.38  cnf(c_0_41, negated_conjecture, (v4_ordinal1(esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_37]), c_0_13])]), c_0_38])).
% 0.20/0.38  cnf(c_0_42, plain, (r2_hidden(k1_ordinal1(X2),X1)|~v4_ordinal1(X1)|~v3_ordinal1(X2)|~r2_hidden(X2,X1)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.38  cnf(c_0_43, negated_conjecture, (v3_ordinal1(esk4_0)|~v4_ordinal1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.38  cnf(c_0_44, plain, (r2_hidden(X1,k1_ordinal1(X1))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.38  cnf(c_0_45, negated_conjecture, (k1_ordinal1(esk4_0)=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_41])])).
% 0.20/0.38  cnf(c_0_46, negated_conjecture, (r2_hidden(k1_ordinal1(X1),esk3_0)|~v3_ordinal1(X1)|~r2_hidden(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_41]), c_0_13])])).
% 0.20/0.38  cnf(c_0_47, negated_conjecture, (v3_ordinal1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_41])])).
% 0.20/0.38  cnf(c_0_48, negated_conjecture, (r2_hidden(esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.20/0.38  cnf(c_0_49, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_45]), c_0_47]), c_0_48])]), c_0_38]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 50
% 0.20/0.38  # Proof object clause steps            : 31
% 0.20/0.38  # Proof object formula steps           : 19
% 0.20/0.38  # Proof object conjectures             : 19
% 0.20/0.38  # Proof object clause conjectures      : 16
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 16
% 0.20/0.38  # Proof object initial formulas used   : 9
% 0.20/0.38  # Proof object generating inferences   : 13
% 0.20/0.38  # Proof object simplifying inferences  : 20
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 9
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 23
% 0.20/0.38  # Removed in clause preprocessing      : 1
% 0.20/0.38  # Initial clauses in saturation        : 22
% 0.20/0.38  # Processed clauses                    : 138
% 0.20/0.38  # ...of these trivial                  : 1
% 0.20/0.38  # ...subsumed                          : 47
% 0.20/0.38  # ...remaining for further processing  : 90
% 0.20/0.38  # Other redundant clauses eliminated   : 1
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 3
% 0.20/0.38  # Backward-rewritten                   : 7
% 0.20/0.38  # Generated clauses                    : 275
% 0.20/0.38  # ...of the previous two non-trivial   : 249
% 0.20/0.38  # Contextual simplify-reflections      : 1
% 0.20/0.38  # Paramodulations                      : 274
% 0.20/0.38  # Factorizations                       : 0
% 0.20/0.38  # Equation resolutions                 : 1
% 0.20/0.38  # Propositional unsat checks           : 0
% 0.20/0.38  #    Propositional check models        : 0
% 0.20/0.38  #    Propositional check unsatisfiable : 0
% 0.20/0.38  #    Propositional clauses             : 0
% 0.20/0.38  #    Propositional clauses after purity: 0
% 0.20/0.38  #    Propositional unsat core size     : 0
% 0.20/0.38  #    Propositional preprocessing time  : 0.000
% 0.20/0.38  #    Propositional encoding time       : 0.000
% 0.20/0.38  #    Propositional solver time         : 0.000
% 0.20/0.38  #    Success case prop preproc time    : 0.000
% 0.20/0.38  #    Success case prop encoding time   : 0.000
% 0.20/0.38  #    Success case prop solver time     : 0.000
% 0.20/0.38  # Current number of processed clauses  : 79
% 0.20/0.38  #    Positive orientable unit clauses  : 10
% 0.20/0.38  #    Positive unorientable unit clauses: 0
% 0.20/0.38  #    Negative unit clauses             : 16
% 0.20/0.38  #    Non-unit-clauses                  : 53
% 0.20/0.38  # Current number of unprocessed clauses: 105
% 0.20/0.38  # ...number of literals in the above   : 373
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 10
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 306
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 208
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 13
% 0.20/0.38  # Unit Clause-clause subsumption calls : 21
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 5
% 0.20/0.38  # BW rewrite match successes           : 3
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 4787
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.034 s
% 0.20/0.38  # System time              : 0.004 s
% 0.20/0.38  # Total time               : 0.038 s
% 0.20/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
