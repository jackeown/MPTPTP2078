%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:59:10 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 109 expanded)
%              Number of clauses        :   30 (  50 expanded)
%              Number of leaves         :    7 (  26 expanded)
%              Depth                    :   11
%              Number of atoms          :  148 ( 370 expanded)
%              Number of equality atoms :   65 ( 189 expanded)
%              Maximal formula depth    :   27 (   4 average)
%              Maximal clause size      :   36 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t16_mcart_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(X1,k2_zfmisc_1(X2,k2_tarski(X3,X4)))
     => ( r2_hidden(k1_mcart_1(X1),X2)
        & ( k2_mcart_1(X1) = X3
          | k2_mcart_1(X1) = X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_mcart_1)).

fof(t38_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_tarski(X1,X2),X3)
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t10_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
     => ( r2_hidden(k1_mcart_1(X1),X2)
        & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(d2_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] :
      ( X5 = k2_enumset1(X1,X2,X3,X4)
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ~ ( X6 != X1
              & X6 != X2
              & X6 != X3
              & X6 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_enumset1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( r2_hidden(X1,k2_zfmisc_1(X2,k2_tarski(X3,X4)))
       => ( r2_hidden(k1_mcart_1(X1),X2)
          & ( k2_mcart_1(X1) = X3
            | k2_mcart_1(X1) = X4 ) ) ) ),
    inference(assume_negation,[status(cth)],[t16_mcart_1])).

fof(c_0_8,plain,(
    ! [X19,X20,X21] :
      ( ( r2_hidden(X19,X21)
        | ~ r1_tarski(k2_tarski(X19,X20),X21) )
      & ( r2_hidden(X20,X21)
        | ~ r1_tarski(k2_tarski(X19,X20),X21) )
      & ( ~ r2_hidden(X19,X21)
        | ~ r2_hidden(X20,X21)
        | r1_tarski(k2_tarski(X19,X20),X21) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).

fof(c_0_9,plain,(
    ! [X14,X15] : k1_enumset1(X14,X14,X15) = k2_tarski(X14,X15) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_10,plain,(
    ! [X16,X17,X18] : k2_enumset1(X16,X16,X17,X18) = k1_enumset1(X16,X17,X18) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_11,negated_conjecture,
    ( r2_hidden(esk3_0,k2_zfmisc_1(esk4_0,k2_tarski(esk5_0,esk6_0)))
    & ( k2_mcart_1(esk3_0) != esk5_0
      | ~ r2_hidden(k1_mcart_1(esk3_0),esk4_0) )
    & ( k2_mcart_1(esk3_0) != esk6_0
      | ~ r2_hidden(k1_mcart_1(esk3_0),esk4_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])])).

fof(c_0_12,plain,(
    ! [X7,X8,X9,X10,X11] :
      ( ( ~ r1_tarski(X7,X8)
        | ~ r2_hidden(X9,X7)
        | r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_2(X10,X11),X10)
        | r1_tarski(X10,X11) )
      & ( ~ r2_hidden(esk1_2(X10,X11),X11)
        | r1_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_13,plain,
    ( r1_tarski(k2_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_16,plain,(
    ! [X38,X39,X40] :
      ( ( r2_hidden(k1_mcart_1(X38),X39)
        | ~ r2_hidden(X38,k2_zfmisc_1(X39,X40)) )
      & ( r2_hidden(k2_mcart_1(X38),X40)
        | ~ r2_hidden(X38,k2_zfmisc_1(X39,X40)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).

cnf(c_0_17,negated_conjecture,
    ( r2_hidden(esk3_0,k2_zfmisc_1(esk4_0,k2_tarski(esk5_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_18,plain,(
    ! [X25,X26,X27,X28,X29,X30,X31,X32,X33,X34,X35,X36] :
      ( ( ~ r2_hidden(X30,X29)
        | X30 = X25
        | X30 = X26
        | X30 = X27
        | X30 = X28
        | X29 != k2_enumset1(X25,X26,X27,X28) )
      & ( X31 != X25
        | r2_hidden(X31,X29)
        | X29 != k2_enumset1(X25,X26,X27,X28) )
      & ( X31 != X26
        | r2_hidden(X31,X29)
        | X29 != k2_enumset1(X25,X26,X27,X28) )
      & ( X31 != X27
        | r2_hidden(X31,X29)
        | X29 != k2_enumset1(X25,X26,X27,X28) )
      & ( X31 != X28
        | r2_hidden(X31,X29)
        | X29 != k2_enumset1(X25,X26,X27,X28) )
      & ( esk2_5(X32,X33,X34,X35,X36) != X32
        | ~ r2_hidden(esk2_5(X32,X33,X34,X35,X36),X36)
        | X36 = k2_enumset1(X32,X33,X34,X35) )
      & ( esk2_5(X32,X33,X34,X35,X36) != X33
        | ~ r2_hidden(esk2_5(X32,X33,X34,X35,X36),X36)
        | X36 = k2_enumset1(X32,X33,X34,X35) )
      & ( esk2_5(X32,X33,X34,X35,X36) != X34
        | ~ r2_hidden(esk2_5(X32,X33,X34,X35,X36),X36)
        | X36 = k2_enumset1(X32,X33,X34,X35) )
      & ( esk2_5(X32,X33,X34,X35,X36) != X35
        | ~ r2_hidden(esk2_5(X32,X33,X34,X35,X36),X36)
        | X36 = k2_enumset1(X32,X33,X34,X35) )
      & ( r2_hidden(esk2_5(X32,X33,X34,X35,X36),X36)
        | esk2_5(X32,X33,X34,X35,X36) = X32
        | esk2_5(X32,X33,X34,X35,X36) = X33
        | esk2_5(X32,X33,X34,X35,X36) = X34
        | esk2_5(X32,X33,X34,X35,X36) = X35
        | X36 = k2_enumset1(X32,X33,X34,X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_enumset1])])])])])])).

cnf(c_0_19,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( r1_tarski(k2_enumset1(X1,X1,X1,X3),X2)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13,c_0_14]),c_0_15])).

cnf(c_0_21,plain,
    ( r2_hidden(k2_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk3_0,k2_zfmisc_1(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk6_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_14]),c_0_15])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X4,X5,X6,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k2_enumset1(X3,X3,X3,X4))
    | ~ r2_hidden(X4,X2)
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(k2_mcart_1(esk3_0),k2_enumset1(esk5_0,esk5_0,esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,X2)
    | X2 != k2_enumset1(X3,X4,X5,X1) ),
    inference(er,[status(thm)],[c_0_23])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X2,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(k2_mcart_1(esk3_0),X1)
    | ~ r2_hidden(esk6_0,X1)
    | ~ r2_hidden(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,k2_enumset1(X2,X3,X4,X1)) ),
    inference(er,[status(thm)],[c_0_26])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X2)
    | X2 != k2_enumset1(X1,X3,X4,X5) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_31,plain,
    ( r2_hidden(k1_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_32,plain,
    ( X1 = X3
    | X1 = X4
    | X1 = X5
    | X1 = X6
    | ~ r2_hidden(X1,X2)
    | X2 != k2_enumset1(X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(k2_mcart_1(esk3_0),k2_enumset1(X1,X2,X3,esk6_0))
    | ~ r2_hidden(esk5_0,k2_enumset1(X1,X2,X3,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,k2_enumset1(X1,X2,X3,X4)) ),
    inference(er,[status(thm)],[c_0_30])).

cnf(c_0_35,negated_conjecture,
    ( k2_mcart_1(esk3_0) != esk5_0
    | ~ r2_hidden(k1_mcart_1(esk3_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk3_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_22])).

cnf(c_0_37,negated_conjecture,
    ( k2_mcart_1(esk3_0) != esk6_0
    | ~ r2_hidden(k1_mcart_1(esk3_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_38,plain,
    ( X1 = X2
    | X1 = X3
    | X1 = X4
    | X1 = X5
    | ~ r2_hidden(X1,k2_enumset1(X2,X3,X4,X5)) ),
    inference(er,[status(thm)],[c_0_32])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(k2_mcart_1(esk3_0),k2_enumset1(esk5_0,X1,X2,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( esk5_0 != k2_mcart_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_36])])).

cnf(c_0_41,negated_conjecture,
    ( esk6_0 != k2_mcart_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_36])])).

cnf(c_0_42,negated_conjecture,
    ( k2_mcart_1(esk3_0) = X1
    | k2_mcart_1(esk3_0) = X2 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40]),c_0_41])).

cnf(c_0_43,negated_conjecture,
    ( k2_mcart_1(esk3_0) = X1 ),
    inference(ef,[status(thm)],[c_0_42])).

cnf(c_0_44,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_43])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:29:29 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic G_E___208_B02_F1_AE_CS_SP_PS_S0Y
% 0.14/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.027 s
% 0.14/0.38  # Presaturation interreduction done
% 0.14/0.38  
% 0.14/0.38  # Proof found!
% 0.14/0.38  # SZS status Theorem
% 0.14/0.38  # SZS output start CNFRefutation
% 0.14/0.38  fof(t16_mcart_1, conjecture, ![X1, X2, X3, X4]:(r2_hidden(X1,k2_zfmisc_1(X2,k2_tarski(X3,X4)))=>(r2_hidden(k1_mcart_1(X1),X2)&(k2_mcart_1(X1)=X3|k2_mcart_1(X1)=X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_mcart_1)).
% 0.14/0.38  fof(t38_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_tarski(X1,X2),X3)<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 0.14/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.14/0.38  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.14/0.38  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.14/0.38  fof(t10_mcart_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(X2,X3))=>(r2_hidden(k1_mcart_1(X1),X2)&r2_hidden(k2_mcart_1(X1),X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 0.14/0.38  fof(d2_enumset1, axiom, ![X1, X2, X3, X4, X5]:(X5=k2_enumset1(X1,X2,X3,X4)<=>![X6]:(r2_hidden(X6,X5)<=>~((((X6!=X1&X6!=X2)&X6!=X3)&X6!=X4)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_enumset1)).
% 0.14/0.38  fof(c_0_7, negated_conjecture, ~(![X1, X2, X3, X4]:(r2_hidden(X1,k2_zfmisc_1(X2,k2_tarski(X3,X4)))=>(r2_hidden(k1_mcart_1(X1),X2)&(k2_mcart_1(X1)=X3|k2_mcart_1(X1)=X4)))), inference(assume_negation,[status(cth)],[t16_mcart_1])).
% 0.14/0.38  fof(c_0_8, plain, ![X19, X20, X21]:(((r2_hidden(X19,X21)|~r1_tarski(k2_tarski(X19,X20),X21))&(r2_hidden(X20,X21)|~r1_tarski(k2_tarski(X19,X20),X21)))&(~r2_hidden(X19,X21)|~r2_hidden(X20,X21)|r1_tarski(k2_tarski(X19,X20),X21))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).
% 0.14/0.38  fof(c_0_9, plain, ![X14, X15]:k1_enumset1(X14,X14,X15)=k2_tarski(X14,X15), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.14/0.38  fof(c_0_10, plain, ![X16, X17, X18]:k2_enumset1(X16,X16,X17,X18)=k1_enumset1(X16,X17,X18), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.14/0.38  fof(c_0_11, negated_conjecture, (r2_hidden(esk3_0,k2_zfmisc_1(esk4_0,k2_tarski(esk5_0,esk6_0)))&((k2_mcart_1(esk3_0)!=esk5_0|~r2_hidden(k1_mcart_1(esk3_0),esk4_0))&(k2_mcart_1(esk3_0)!=esk6_0|~r2_hidden(k1_mcart_1(esk3_0),esk4_0)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])])).
% 0.14/0.38  fof(c_0_12, plain, ![X7, X8, X9, X10, X11]:((~r1_tarski(X7,X8)|(~r2_hidden(X9,X7)|r2_hidden(X9,X8)))&((r2_hidden(esk1_2(X10,X11),X10)|r1_tarski(X10,X11))&(~r2_hidden(esk1_2(X10,X11),X11)|r1_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.14/0.38  cnf(c_0_13, plain, (r1_tarski(k2_tarski(X1,X3),X2)|~r2_hidden(X1,X2)|~r2_hidden(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.38  cnf(c_0_14, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.38  cnf(c_0_15, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.38  fof(c_0_16, plain, ![X38, X39, X40]:((r2_hidden(k1_mcart_1(X38),X39)|~r2_hidden(X38,k2_zfmisc_1(X39,X40)))&(r2_hidden(k2_mcart_1(X38),X40)|~r2_hidden(X38,k2_zfmisc_1(X39,X40)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).
% 0.14/0.38  cnf(c_0_17, negated_conjecture, (r2_hidden(esk3_0,k2_zfmisc_1(esk4_0,k2_tarski(esk5_0,esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.38  fof(c_0_18, plain, ![X25, X26, X27, X28, X29, X30, X31, X32, X33, X34, X35, X36]:(((~r2_hidden(X30,X29)|(X30=X25|X30=X26|X30=X27|X30=X28)|X29!=k2_enumset1(X25,X26,X27,X28))&((((X31!=X25|r2_hidden(X31,X29)|X29!=k2_enumset1(X25,X26,X27,X28))&(X31!=X26|r2_hidden(X31,X29)|X29!=k2_enumset1(X25,X26,X27,X28)))&(X31!=X27|r2_hidden(X31,X29)|X29!=k2_enumset1(X25,X26,X27,X28)))&(X31!=X28|r2_hidden(X31,X29)|X29!=k2_enumset1(X25,X26,X27,X28))))&(((((esk2_5(X32,X33,X34,X35,X36)!=X32|~r2_hidden(esk2_5(X32,X33,X34,X35,X36),X36)|X36=k2_enumset1(X32,X33,X34,X35))&(esk2_5(X32,X33,X34,X35,X36)!=X33|~r2_hidden(esk2_5(X32,X33,X34,X35,X36),X36)|X36=k2_enumset1(X32,X33,X34,X35)))&(esk2_5(X32,X33,X34,X35,X36)!=X34|~r2_hidden(esk2_5(X32,X33,X34,X35,X36),X36)|X36=k2_enumset1(X32,X33,X34,X35)))&(esk2_5(X32,X33,X34,X35,X36)!=X35|~r2_hidden(esk2_5(X32,X33,X34,X35,X36),X36)|X36=k2_enumset1(X32,X33,X34,X35)))&(r2_hidden(esk2_5(X32,X33,X34,X35,X36),X36)|(esk2_5(X32,X33,X34,X35,X36)=X32|esk2_5(X32,X33,X34,X35,X36)=X33|esk2_5(X32,X33,X34,X35,X36)=X34|esk2_5(X32,X33,X34,X35,X36)=X35)|X36=k2_enumset1(X32,X33,X34,X35)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_enumset1])])])])])])).
% 0.14/0.38  cnf(c_0_19, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.38  cnf(c_0_20, plain, (r1_tarski(k2_enumset1(X1,X1,X1,X3),X2)|~r2_hidden(X3,X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13, c_0_14]), c_0_15])).
% 0.14/0.38  cnf(c_0_21, plain, (r2_hidden(k2_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.38  cnf(c_0_22, negated_conjecture, (r2_hidden(esk3_0,k2_zfmisc_1(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk6_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17, c_0_14]), c_0_15])).
% 0.14/0.38  cnf(c_0_23, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X4,X5,X6,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.14/0.38  cnf(c_0_24, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k2_enumset1(X3,X3,X3,X4))|~r2_hidden(X4,X2)|~r2_hidden(X3,X2)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.14/0.38  cnf(c_0_25, negated_conjecture, (r2_hidden(k2_mcart_1(esk3_0),k2_enumset1(esk5_0,esk5_0,esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.14/0.38  cnf(c_0_26, plain, (r2_hidden(X1,X2)|X2!=k2_enumset1(X3,X4,X5,X1)), inference(er,[status(thm)],[c_0_23])).
% 0.14/0.38  cnf(c_0_27, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X2,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.14/0.38  cnf(c_0_28, negated_conjecture, (r2_hidden(k2_mcart_1(esk3_0),X1)|~r2_hidden(esk6_0,X1)|~r2_hidden(esk5_0,X1)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.14/0.38  cnf(c_0_29, plain, (r2_hidden(X1,k2_enumset1(X2,X3,X4,X1))), inference(er,[status(thm)],[c_0_26])).
% 0.14/0.38  cnf(c_0_30, plain, (r2_hidden(X1,X2)|X2!=k2_enumset1(X1,X3,X4,X5)), inference(er,[status(thm)],[c_0_27])).
% 0.14/0.38  cnf(c_0_31, plain, (r2_hidden(k1_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.38  cnf(c_0_32, plain, (X1=X3|X1=X4|X1=X5|X1=X6|~r2_hidden(X1,X2)|X2!=k2_enumset1(X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.14/0.38  cnf(c_0_33, negated_conjecture, (r2_hidden(k2_mcart_1(esk3_0),k2_enumset1(X1,X2,X3,esk6_0))|~r2_hidden(esk5_0,k2_enumset1(X1,X2,X3,esk6_0))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.14/0.38  cnf(c_0_34, plain, (r2_hidden(X1,k2_enumset1(X1,X2,X3,X4))), inference(er,[status(thm)],[c_0_30])).
% 0.14/0.38  cnf(c_0_35, negated_conjecture, (k2_mcart_1(esk3_0)!=esk5_0|~r2_hidden(k1_mcart_1(esk3_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.38  cnf(c_0_36, negated_conjecture, (r2_hidden(k1_mcart_1(esk3_0),esk4_0)), inference(spm,[status(thm)],[c_0_31, c_0_22])).
% 0.14/0.38  cnf(c_0_37, negated_conjecture, (k2_mcart_1(esk3_0)!=esk6_0|~r2_hidden(k1_mcart_1(esk3_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.38  cnf(c_0_38, plain, (X1=X2|X1=X3|X1=X4|X1=X5|~r2_hidden(X1,k2_enumset1(X2,X3,X4,X5))), inference(er,[status(thm)],[c_0_32])).
% 0.14/0.38  cnf(c_0_39, negated_conjecture, (r2_hidden(k2_mcart_1(esk3_0),k2_enumset1(esk5_0,X1,X2,esk6_0))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.14/0.38  cnf(c_0_40, negated_conjecture, (esk5_0!=k2_mcart_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_36])])).
% 0.14/0.38  cnf(c_0_41, negated_conjecture, (esk6_0!=k2_mcart_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_36])])).
% 0.14/0.38  cnf(c_0_42, negated_conjecture, (k2_mcart_1(esk3_0)=X1|k2_mcart_1(esk3_0)=X2), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40]), c_0_41])).
% 0.14/0.38  cnf(c_0_43, negated_conjecture, (k2_mcart_1(esk3_0)=X1), inference(ef,[status(thm)],[c_0_42])).
% 0.14/0.38  cnf(c_0_44, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_43])]), ['proof']).
% 0.14/0.38  # SZS output end CNFRefutation
% 0.14/0.38  # Proof object total steps             : 45
% 0.14/0.38  # Proof object clause steps            : 30
% 0.14/0.38  # Proof object formula steps           : 15
% 0.14/0.38  # Proof object conjectures             : 17
% 0.14/0.38  # Proof object clause conjectures      : 14
% 0.14/0.38  # Proof object formula conjectures     : 3
% 0.14/0.38  # Proof object initial clauses used    : 12
% 0.14/0.38  # Proof object initial formulas used   : 7
% 0.14/0.38  # Proof object generating inferences   : 11
% 0.14/0.38  # Proof object simplifying inferences  : 14
% 0.14/0.38  # Training examples: 0 positive, 0 negative
% 0.14/0.38  # Parsed axioms                        : 9
% 0.14/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.38  # Initial clauses                      : 27
% 0.14/0.38  # Removed in clause preprocessing      : 3
% 0.14/0.38  # Initial clauses in saturation        : 24
% 0.14/0.38  # Processed clauses                    : 77
% 0.14/0.38  # ...of these trivial                  : 1
% 0.14/0.38  # ...subsumed                          : 3
% 0.14/0.38  # ...remaining for further processing  : 73
% 0.14/0.38  # Other redundant clauses eliminated   : 7
% 0.14/0.38  # Clauses deleted for lack of memory   : 0
% 0.14/0.38  # Backward-subsumed                    : 1
% 0.14/0.38  # Backward-rewritten                   : 21
% 0.14/0.38  # Generated clauses                    : 219
% 0.14/0.38  # ...of the previous two non-trivial   : 164
% 0.14/0.38  # Contextual simplify-reflections      : 0
% 0.14/0.38  # Paramodulations                      : 199
% 0.14/0.38  # Factorizations                       : 8
% 0.14/0.38  # Equation resolutions                 : 12
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
% 0.14/0.38  # Current number of processed clauses  : 22
% 0.14/0.38  #    Positive orientable unit clauses  : 5
% 0.14/0.38  #    Positive unorientable unit clauses: 1
% 0.14/0.38  #    Negative unit clauses             : 1
% 0.14/0.38  #    Non-unit-clauses                  : 15
% 0.14/0.38  # Current number of unprocessed clauses: 126
% 0.14/0.38  # ...number of literals in the above   : 389
% 0.14/0.38  # Current number of archived formulas  : 0
% 0.14/0.38  # Current number of archived clauses   : 49
% 0.14/0.38  # Clause-clause subsumption calls (NU) : 160
% 0.14/0.38  # Rec. Clause-clause subsumption calls : 150
% 0.14/0.38  # Non-unit clause-clause subsumptions  : 3
% 0.14/0.38  # Unit Clause-clause subsumption calls : 28
% 0.14/0.38  # Rewrite failures with RHS unbound    : 3
% 0.14/0.38  # BW rewrite match attempts            : 64
% 0.14/0.38  # BW rewrite match successes           : 46
% 0.14/0.38  # Condensation attempts                : 0
% 0.14/0.38  # Condensation successes               : 0
% 0.14/0.38  # Termbank termtop insertions          : 3399
% 0.14/0.38  
% 0.14/0.38  # -------------------------------------------------
% 0.14/0.38  # User time                : 0.033 s
% 0.14/0.38  # System time              : 0.003 s
% 0.14/0.38  # Total time               : 0.036 s
% 0.14/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
