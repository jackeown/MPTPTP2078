%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0757+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:52 EST 2020

% Result     : Theorem 0.73s
% Output     : CNFRefutation 0.73s
% Verified   : 
% Statistics : Number of formulae       :   26 (  45 expanded)
%              Number of clauses        :   15 (  17 expanded)
%              Number of leaves         :    5 (  11 expanded)
%              Depth                    :    9
%              Number of atoms          :   69 ( 158 expanded)
%              Number of equality atoms :    8 (  28 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t50_ordinal1,conjecture,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ~ ( ~ r2_xboole_0(X1,X2)
              & X1 != X2
              & ~ r2_xboole_0(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_ordinal1)).

fof(t25_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => r3_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_ordinal1)).

fof(symmetry_r3_xboole_0,axiom,(
    ! [X1,X2] :
      ( r3_xboole_0(X1,X2)
     => r3_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',symmetry_r3_xboole_0)).

fof(d9_xboole_0,axiom,(
    ! [X1,X2] :
      ( r3_xboole_0(X1,X2)
    <=> ( r1_tarski(X1,X2)
        | r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',d9_xboole_0)).

fof(d8_xboole_0,axiom,(
    ! [X1,X2] :
      ( r2_xboole_0(X1,X2)
    <=> ( r1_tarski(X1,X2)
        & X1 != X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',d8_xboole_0)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] :
        ( v3_ordinal1(X1)
       => ! [X2] :
            ( v3_ordinal1(X2)
           => ~ ( ~ r2_xboole_0(X1,X2)
                & X1 != X2
                & ~ r2_xboole_0(X2,X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t50_ordinal1])).

fof(c_0_6,plain,(
    ! [X3251,X3252] :
      ( ~ v3_ordinal1(X3251)
      | ~ v3_ordinal1(X3252)
      | r3_xboole_0(X3251,X3252) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_ordinal1])])])).

fof(c_0_7,negated_conjecture,
    ( v3_ordinal1(esk253_0)
    & v3_ordinal1(esk254_0)
    & ~ r2_xboole_0(esk253_0,esk254_0)
    & esk253_0 != esk254_0
    & ~ r2_xboole_0(esk254_0,esk253_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])).

cnf(c_0_8,plain,
    ( r3_xboole_0(X1,X2)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,negated_conjecture,
    ( v3_ordinal1(esk254_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_10,plain,(
    ! [X125,X126] :
      ( ~ r3_xboole_0(X125,X126)
      | r3_xboole_0(X126,X125) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r3_xboole_0])])).

cnf(c_0_11,negated_conjecture,
    ( r3_xboole_0(X1,esk254_0)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_12,negated_conjecture,
    ( v3_ordinal1(esk253_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_13,plain,(
    ! [X106,X107] :
      ( ( ~ r3_xboole_0(X106,X107)
        | r1_tarski(X106,X107)
        | r1_tarski(X107,X106) )
      & ( ~ r1_tarski(X106,X107)
        | r3_xboole_0(X106,X107) )
      & ( ~ r1_tarski(X107,X106)
        | r3_xboole_0(X106,X107) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_xboole_0])])])).

cnf(c_0_14,plain,
    ( r3_xboole_0(X2,X1)
    | ~ r3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( r3_xboole_0(esk253_0,esk254_0) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

fof(c_0_16,plain,(
    ! [X64,X65] :
      ( ( r1_tarski(X64,X65)
        | ~ r2_xboole_0(X64,X65) )
      & ( X64 != X65
        | ~ r2_xboole_0(X64,X65) )
      & ( ~ r1_tarski(X64,X65)
        | X64 = X65
        | r2_xboole_0(X64,X65) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).

cnf(c_0_17,plain,
    ( r1_tarski(X1,X2)
    | r1_tarski(X2,X1)
    | ~ r3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( r3_xboole_0(esk254_0,esk253_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_19,plain,
    ( X1 = X2
    | r2_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( r1_tarski(esk254_0,esk253_0)
    | r1_tarski(esk253_0,esk254_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_21,negated_conjecture,
    ( esk253_0 != esk254_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_22,negated_conjecture,
    ( ~ r2_xboole_0(esk254_0,esk253_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_23,negated_conjecture,
    ( r1_tarski(esk253_0,esk254_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_22])).

cnf(c_0_24,negated_conjecture,
    ( ~ r2_xboole_0(esk253_0,esk254_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_25,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_23]),c_0_21]),c_0_24]),
    [proof]).
%------------------------------------------------------------------------------
