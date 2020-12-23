%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:39:34 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 138 expanded)
%              Number of clauses        :   31 (  60 expanded)
%              Number of leaves         :    8 (  35 expanded)
%              Depth                    :   15
%              Number of atoms          :  102 ( 354 expanded)
%              Number of equality atoms :   28 ( 130 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t41_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ~ ( X1 != k1_tarski(X2)
        & X1 != k1_xboole_0
        & ! [X3] :
            ~ ( r2_hidden(X3,X1)
              & X3 != X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_zfmisc_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t37_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_zfmisc_1)).

fof(t87_enumset1,axiom,(
    ! [X1] : k3_enumset1(X1,X1,X1,X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(t38_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,k4_xboole_0(X2,X1))
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

fof(d8_xboole_0,axiom,(
    ! [X1,X2] :
      ( r2_xboole_0(X1,X2)
    <=> ( r1_tarski(X1,X2)
        & X1 != X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(antisymmetry_r2_xboole_0,axiom,(
    ! [X1,X2] :
      ( r2_xboole_0(X1,X2)
     => ~ r2_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_xboole_0)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2] :
        ~ ( X1 != k1_tarski(X2)
          & X1 != k1_xboole_0
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & X3 != X2 ) ) ),
    inference(assume_negation,[status(cth)],[t41_zfmisc_1])).

fof(c_0_9,negated_conjecture,(
    ! [X41] :
      ( esk2_0 != k1_tarski(esk3_0)
      & esk2_0 != k1_xboole_0
      & ( ~ r2_hidden(X41,esk2_0)
        | X41 = esk3_0 ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])])).

fof(c_0_10,plain,(
    ! [X9,X10,X11,X12,X13] :
      ( ( ~ r1_tarski(X9,X10)
        | ~ r2_hidden(X11,X9)
        | r2_hidden(X11,X10) )
      & ( r2_hidden(esk1_2(X12,X13),X12)
        | r1_tarski(X12,X13) )
      & ( ~ r2_hidden(esk1_2(X12,X13),X13)
        | r1_tarski(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_11,negated_conjecture,
    ( X1 = esk3_0
    | ~ r2_hidden(X1,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_13,plain,(
    ! [X37,X38] :
      ( ( ~ r1_tarski(k1_tarski(X37),X38)
        | r2_hidden(X37,X38) )
      & ( ~ r2_hidden(X37,X38)
        | r1_tarski(k1_tarski(X37),X38) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_zfmisc_1])])).

fof(c_0_14,plain,(
    ! [X34] : k3_enumset1(X34,X34,X34,X34,X34) = k1_tarski(X34) ),
    inference(variable_rename,[status(thm)],[t87_enumset1])).

fof(c_0_15,plain,(
    ! [X29,X30,X31,X32,X33] : k4_enumset1(X29,X29,X30,X31,X32,X33) = k3_enumset1(X29,X30,X31,X32,X33) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_16,plain,(
    ! [X17,X18] :
      ( ~ r1_tarski(X17,k4_xboole_0(X18,X17))
      | X17 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_xboole_1])])).

cnf(c_0_17,negated_conjecture,
    ( esk1_2(esk2_0,X1) = esk3_0
    | r1_tarski(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_18,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( k3_enumset1(X1,X1,X1,X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk3_0,esk2_0)
    | r1_tarski(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_24,plain,
    ( r1_tarski(k4_enumset1(X1,X1,X1,X1,X1,X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_19]),c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk3_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])).

cnf(c_0_26,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_27,negated_conjecture,
    ( r1_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(X1,esk2_0)
    | ~ r2_hidden(X1,k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk1_2(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),X1),esk2_0)
    | r1_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_12])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k1_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_31,negated_conjecture,
    ( esk1_2(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),X1) = esk3_0
    | r1_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),X1) ),
    inference(spm,[status(thm)],[c_0_11,c_0_29])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k4_enumset1(X1,X1,X1,X1,X1,X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_19]),c_0_20])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk3_0,k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))
    | r1_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_31])).

fof(c_0_34,plain,(
    ! [X15,X16] :
      ( ( r1_tarski(X15,X16)
        | ~ r2_xboole_0(X15,X16) )
      & ( X15 != X16
        | ~ r2_xboole_0(X15,X16) )
      & ( ~ r1_tarski(X15,X16)
        | X15 = X16
        | r2_xboole_0(X15,X16) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).

cnf(c_0_35,negated_conjecture,
    ( esk2_0 != k1_tarski(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk3_0,k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))
    | r2_hidden(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

fof(c_0_38,plain,(
    ! [X7,X8] :
      ( ~ r2_xboole_0(X7,X8)
      | ~ r2_xboole_0(X8,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[antisymmetry_r2_xboole_0])])])).

cnf(c_0_39,plain,
    ( X1 = X2
    | r2_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( esk2_0 != k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_19]),c_0_20])).

cnf(c_0_41,negated_conjecture,
    ( r1_tarski(esk2_0,X1)
    | ~ r2_hidden(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_17])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk3_0,k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)) ),
    inference(ef,[status(thm)],[c_0_37])).

cnf(c_0_43,plain,
    ( ~ r2_xboole_0(X1,X2)
    | ~ r2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_44,negated_conjecture,
    ( r2_xboole_0(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_27]),c_0_40])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(esk2_0,k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_46,negated_conjecture,
    ( ~ r2_xboole_0(esk2_0,k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_47,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_45]),c_0_40]),c_0_46]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 18:56:04 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  # Version: 2.5pre002
% 0.13/0.33  # No SInE strategy applied
% 0.13/0.33  # Trying AutoSched0 for 299 seconds
% 0.13/0.36  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S078N
% 0.13/0.36  # and selection function SelectCQIArNpEqFirst.
% 0.13/0.36  #
% 0.13/0.36  # Preprocessing time       : 0.026 s
% 0.13/0.36  # Presaturation interreduction done
% 0.13/0.36  
% 0.13/0.36  # Proof found!
% 0.13/0.36  # SZS status Theorem
% 0.13/0.36  # SZS output start CNFRefutation
% 0.13/0.36  fof(t41_zfmisc_1, conjecture, ![X1, X2]:~(((X1!=k1_tarski(X2)&X1!=k1_xboole_0)&![X3]:~((r2_hidden(X3,X1)&X3!=X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_zfmisc_1)).
% 0.13/0.36  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.13/0.36  fof(t37_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_zfmisc_1)).
% 0.13/0.36  fof(t87_enumset1, axiom, ![X1]:k3_enumset1(X1,X1,X1,X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_enumset1)).
% 0.13/0.36  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.13/0.36  fof(t38_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,k4_xboole_0(X2,X1))=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_xboole_1)).
% 0.13/0.36  fof(d8_xboole_0, axiom, ![X1, X2]:(r2_xboole_0(X1,X2)<=>(r1_tarski(X1,X2)&X1!=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 0.13/0.36  fof(antisymmetry_r2_xboole_0, axiom, ![X1, X2]:(r2_xboole_0(X1,X2)=>~(r2_xboole_0(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', antisymmetry_r2_xboole_0)).
% 0.13/0.36  fof(c_0_8, negated_conjecture, ~(![X1, X2]:~(((X1!=k1_tarski(X2)&X1!=k1_xboole_0)&![X3]:~((r2_hidden(X3,X1)&X3!=X2))))), inference(assume_negation,[status(cth)],[t41_zfmisc_1])).
% 0.13/0.36  fof(c_0_9, negated_conjecture, ![X41]:((esk2_0!=k1_tarski(esk3_0)&esk2_0!=k1_xboole_0)&(~r2_hidden(X41,esk2_0)|X41=esk3_0)), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])])).
% 0.13/0.36  fof(c_0_10, plain, ![X9, X10, X11, X12, X13]:((~r1_tarski(X9,X10)|(~r2_hidden(X11,X9)|r2_hidden(X11,X10)))&((r2_hidden(esk1_2(X12,X13),X12)|r1_tarski(X12,X13))&(~r2_hidden(esk1_2(X12,X13),X13)|r1_tarski(X12,X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.13/0.36  cnf(c_0_11, negated_conjecture, (X1=esk3_0|~r2_hidden(X1,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.36  cnf(c_0_12, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.36  fof(c_0_13, plain, ![X37, X38]:((~r1_tarski(k1_tarski(X37),X38)|r2_hidden(X37,X38))&(~r2_hidden(X37,X38)|r1_tarski(k1_tarski(X37),X38))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_zfmisc_1])])).
% 0.13/0.36  fof(c_0_14, plain, ![X34]:k3_enumset1(X34,X34,X34,X34,X34)=k1_tarski(X34), inference(variable_rename,[status(thm)],[t87_enumset1])).
% 0.13/0.36  fof(c_0_15, plain, ![X29, X30, X31, X32, X33]:k4_enumset1(X29,X29,X30,X31,X32,X33)=k3_enumset1(X29,X30,X31,X32,X33), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.13/0.36  fof(c_0_16, plain, ![X17, X18]:(~r1_tarski(X17,k4_xboole_0(X18,X17))|X17=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_xboole_1])])).
% 0.13/0.36  cnf(c_0_17, negated_conjecture, (esk1_2(esk2_0,X1)=esk3_0|r1_tarski(esk2_0,X1)), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.13/0.36  cnf(c_0_18, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.36  cnf(c_0_19, plain, (k3_enumset1(X1,X1,X1,X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.36  cnf(c_0_20, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.36  cnf(c_0_21, plain, (X1=k1_xboole_0|~r1_tarski(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.36  cnf(c_0_22, negated_conjecture, (r2_hidden(esk3_0,esk2_0)|r1_tarski(esk2_0,X1)), inference(spm,[status(thm)],[c_0_12, c_0_17])).
% 0.13/0.36  cnf(c_0_23, negated_conjecture, (esk2_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.36  cnf(c_0_24, plain, (r1_tarski(k4_enumset1(X1,X1,X1,X1,X1,X1),X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_19]), c_0_20])).
% 0.13/0.36  cnf(c_0_25, negated_conjecture, (r2_hidden(esk3_0,esk2_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23])).
% 0.13/0.36  cnf(c_0_26, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.36  cnf(c_0_27, negated_conjecture, (r1_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),esk2_0)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.13/0.36  cnf(c_0_28, negated_conjecture, (r2_hidden(X1,esk2_0)|~r2_hidden(X1,k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.13/0.36  cnf(c_0_29, negated_conjecture, (r2_hidden(esk1_2(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),X1),esk2_0)|r1_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),X1)), inference(spm,[status(thm)],[c_0_28, c_0_12])).
% 0.13/0.36  cnf(c_0_30, plain, (r2_hidden(X1,X2)|~r1_tarski(k1_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.36  cnf(c_0_31, negated_conjecture, (esk1_2(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),X1)=esk3_0|r1_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),X1)), inference(spm,[status(thm)],[c_0_11, c_0_29])).
% 0.13/0.36  cnf(c_0_32, plain, (r2_hidden(X1,X2)|~r1_tarski(k4_enumset1(X1,X1,X1,X1,X1,X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_19]), c_0_20])).
% 0.13/0.36  cnf(c_0_33, negated_conjecture, (r2_hidden(esk3_0,k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))|r1_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),X1)), inference(spm,[status(thm)],[c_0_12, c_0_31])).
% 0.13/0.36  fof(c_0_34, plain, ![X15, X16]:(((r1_tarski(X15,X16)|~r2_xboole_0(X15,X16))&(X15!=X16|~r2_xboole_0(X15,X16)))&(~r1_tarski(X15,X16)|X15=X16|r2_xboole_0(X15,X16))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).
% 0.13/0.36  cnf(c_0_35, negated_conjecture, (esk2_0!=k1_tarski(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.36  cnf(c_0_36, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.36  cnf(c_0_37, negated_conjecture, (r2_hidden(esk3_0,k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))|r2_hidden(esk3_0,X1)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.13/0.36  fof(c_0_38, plain, ![X7, X8]:(~r2_xboole_0(X7,X8)|~r2_xboole_0(X8,X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[antisymmetry_r2_xboole_0])])])).
% 0.13/0.36  cnf(c_0_39, plain, (X1=X2|r2_xboole_0(X1,X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.13/0.36  cnf(c_0_40, negated_conjecture, (esk2_0!=k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_19]), c_0_20])).
% 0.13/0.36  cnf(c_0_41, negated_conjecture, (r1_tarski(esk2_0,X1)|~r2_hidden(esk3_0,X1)), inference(spm,[status(thm)],[c_0_36, c_0_17])).
% 0.13/0.36  cnf(c_0_42, negated_conjecture, (r2_hidden(esk3_0,k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))), inference(ef,[status(thm)],[c_0_37])).
% 0.13/0.36  cnf(c_0_43, plain, (~r2_xboole_0(X1,X2)|~r2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.13/0.36  cnf(c_0_44, negated_conjecture, (r2_xboole_0(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),esk2_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_27]), c_0_40])).
% 0.13/0.36  cnf(c_0_45, negated_conjecture, (r1_tarski(esk2_0,k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.13/0.36  cnf(c_0_46, negated_conjecture, (~r2_xboole_0(esk2_0,k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.13/0.36  cnf(c_0_47, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_45]), c_0_40]), c_0_46]), ['proof']).
% 0.13/0.36  # SZS output end CNFRefutation
% 0.13/0.36  # Proof object total steps             : 48
% 0.13/0.36  # Proof object clause steps            : 31
% 0.13/0.36  # Proof object formula steps           : 17
% 0.13/0.36  # Proof object conjectures             : 22
% 0.13/0.36  # Proof object clause conjectures      : 19
% 0.13/0.36  # Proof object formula conjectures     : 3
% 0.13/0.36  # Proof object initial clauses used    : 13
% 0.13/0.36  # Proof object initial formulas used   : 8
% 0.13/0.36  # Proof object generating inferences   : 15
% 0.13/0.36  # Proof object simplifying inferences  : 10
% 0.13/0.36  # Training examples: 0 positive, 0 negative
% 0.13/0.36  # Parsed axioms                        : 12
% 0.13/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.36  # Initial clauses                      : 19
% 0.13/0.36  # Removed in clause preprocessing      : 4
% 0.13/0.36  # Initial clauses in saturation        : 15
% 0.13/0.36  # Processed clauses                    : 51
% 0.13/0.36  # ...of these trivial                  : 0
% 0.13/0.36  # ...subsumed                          : 1
% 0.13/0.36  # ...remaining for further processing  : 50
% 0.13/0.36  # Other redundant clauses eliminated   : 1
% 0.13/0.36  # Clauses deleted for lack of memory   : 0
% 0.13/0.36  # Backward-subsumed                    : 4
% 0.13/0.36  # Backward-rewritten                   : 0
% 0.13/0.36  # Generated clauses                    : 56
% 0.13/0.36  # ...of the previous two non-trivial   : 38
% 0.13/0.36  # Contextual simplify-reflections      : 0
% 0.13/0.36  # Paramodulations                      : 53
% 0.13/0.36  # Factorizations                       : 2
% 0.13/0.36  # Equation resolutions                 : 1
% 0.13/0.36  # Propositional unsat checks           : 0
% 0.13/0.36  #    Propositional check models        : 0
% 0.13/0.36  #    Propositional check unsatisfiable : 0
% 0.13/0.36  #    Propositional clauses             : 0
% 0.13/0.36  #    Propositional clauses after purity: 0
% 0.13/0.36  #    Propositional unsat core size     : 0
% 0.13/0.36  #    Propositional preprocessing time  : 0.000
% 0.13/0.36  #    Propositional encoding time       : 0.000
% 0.13/0.36  #    Propositional solver time         : 0.000
% 0.13/0.36  #    Success case prop preproc time    : 0.000
% 0.13/0.36  #    Success case prop encoding time   : 0.000
% 0.13/0.36  #    Success case prop solver time     : 0.000
% 0.13/0.36  # Current number of processed clauses  : 30
% 0.13/0.36  #    Positive orientable unit clauses  : 8
% 0.13/0.36  #    Positive unorientable unit clauses: 0
% 0.13/0.36  #    Negative unit clauses             : 4
% 0.13/0.36  #    Non-unit-clauses                  : 18
% 0.13/0.36  # Current number of unprocessed clauses: 14
% 0.13/0.36  # ...number of literals in the above   : 27
% 0.13/0.36  # Current number of archived formulas  : 0
% 0.13/0.36  # Current number of archived clauses   : 23
% 0.13/0.36  # Clause-clause subsumption calls (NU) : 26
% 0.13/0.36  # Rec. Clause-clause subsumption calls : 25
% 0.13/0.36  # Non-unit clause-clause subsumptions  : 1
% 0.13/0.36  # Unit Clause-clause subsumption calls : 12
% 0.13/0.36  # Rewrite failures with RHS unbound    : 0
% 0.13/0.36  # BW rewrite match attempts            : 7
% 0.13/0.36  # BW rewrite match successes           : 2
% 0.13/0.36  # Condensation attempts                : 0
% 0.13/0.36  # Condensation successes               : 0
% 0.13/0.36  # Termbank termtop insertions          : 1892
% 0.13/0.36  
% 0.13/0.36  # -------------------------------------------------
% 0.13/0.36  # User time                : 0.029 s
% 0.13/0.36  # System time              : 0.003 s
% 0.13/0.36  # Total time               : 0.031 s
% 0.13/0.36  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
