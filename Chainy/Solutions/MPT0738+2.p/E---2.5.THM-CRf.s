%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0738+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:51 EST 2020

% Result     : Theorem 0.75s
% Output     : CNFRefutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :   38 (  75 expanded)
%              Number of clauses        :   21 (  28 expanded)
%              Number of leaves         :    8 (  18 expanded)
%              Depth                    :   10
%              Number of atoms          :  113 ( 240 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t26_ordinal1,conjecture,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r1_ordinal1(X1,X2)
            | r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

fof(t25_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => r3_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_ordinal1)).

fof(d9_xboole_0,axiom,(
    ! [X1,X2] :
      ( r3_xboole_0(X1,X2)
    <=> ( r1_tarski(X1,X2)
        | r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',d9_xboole_0)).

fof(d8_xboole_0,axiom,(
    ! [X1,X2] :
      ( r2_xboole_0(X1,X2)
    <=> ( r1_tarski(X1,X2)
        & X1 != X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',d8_xboole_0)).

fof(cc1_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ( v1_ordinal1(X1)
        & v2_ordinal1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_ordinal1)).

fof(t21_ordinal1,axiom,(
    ! [X1] :
      ( v1_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r2_xboole_0(X1,X2)
           => r2_hidden(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_ordinal1)).

fof(reflexivity_r1_ordinal1,axiom,(
    ! [X1,X2] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X2) )
     => r1_ordinal1(X1,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r1_ordinal1)).

fof(redefinition_r1_ordinal1,axiom,(
    ! [X1,X2] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X2) )
     => ( r1_ordinal1(X1,X2)
      <=> r1_tarski(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
        ( v3_ordinal1(X1)
       => ! [X2] :
            ( v3_ordinal1(X2)
           => ( r1_ordinal1(X1,X2)
              | r2_hidden(X2,X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t26_ordinal1])).

fof(c_0_9,plain,(
    ! [X3193,X3194] :
      ( ~ v3_ordinal1(X3193)
      | ~ v3_ordinal1(X3194)
      | r3_xboole_0(X3193,X3194) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_ordinal1])])])).

fof(c_0_10,negated_conjecture,
    ( v3_ordinal1(esk225_0)
    & v3_ordinal1(esk226_0)
    & ~ r1_ordinal1(esk225_0,esk226_0)
    & ~ r2_hidden(esk226_0,esk225_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

cnf(c_0_11,plain,
    ( r3_xboole_0(X1,X2)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,negated_conjecture,
    ( v3_ordinal1(esk225_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

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

cnf(c_0_14,negated_conjecture,
    ( r3_xboole_0(X1,esk225_0)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_15,negated_conjecture,
    ( v3_ordinal1(esk226_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

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
    ( r3_xboole_0(esk226_0,esk225_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

fof(c_0_19,plain,(
    ! [X3151] :
      ( ( v1_ordinal1(X3151)
        | ~ v3_ordinal1(X3151) )
      & ( v2_ordinal1(X3151)
        | ~ v3_ordinal1(X3151) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_ordinal1])])])).

fof(c_0_20,plain,(
    ! [X3184,X3185] :
      ( ~ v1_ordinal1(X3184)
      | ~ v3_ordinal1(X3185)
      | ~ r2_xboole_0(X3184,X3185)
      | r2_hidden(X3184,X3185) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_ordinal1])])])).

cnf(c_0_21,plain,
    ( X1 = X2
    | r2_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( r1_tarski(esk226_0,esk225_0)
    | r1_tarski(esk225_0,esk226_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_23,plain,
    ( v1_ordinal1(X1)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_24,plain,(
    ! [X3173,X3174] :
      ( ~ v3_ordinal1(X3173)
      | ~ v3_ordinal1(X3174)
      | r1_ordinal1(X3173,X3173) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[reflexivity_r1_ordinal1])])).

fof(c_0_25,plain,(
    ! [X3171,X3172] :
      ( ( ~ r1_ordinal1(X3171,X3172)
        | r1_tarski(X3171,X3172)
        | ~ v3_ordinal1(X3171)
        | ~ v3_ordinal1(X3172) )
      & ( ~ r1_tarski(X3171,X3172)
        | r1_ordinal1(X3171,X3172)
        | ~ v3_ordinal1(X3171)
        | ~ v3_ordinal1(X3172) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,X2)
    | ~ v1_ordinal1(X1)
    | ~ v3_ordinal1(X2)
    | ~ r2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( esk226_0 = esk225_0
    | r1_tarski(esk225_0,esk226_0)
    | r2_xboole_0(esk226_0,esk225_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( v1_ordinal1(esk226_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_15])).

cnf(c_0_29,negated_conjecture,
    ( ~ r2_hidden(esk226_0,esk225_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_30,plain,
    ( r1_ordinal1(X1,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( r1_ordinal1(X1,X2)
    | ~ r1_tarski(X1,X2)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( esk226_0 = esk225_0
    | r1_tarski(esk225_0,esk226_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_12])]),c_0_29])).

cnf(c_0_33,negated_conjecture,
    ( ~ r1_ordinal1(esk225_0,esk226_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_34,negated_conjecture,
    ( r1_ordinal1(X1,X1)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_15])).

cnf(c_0_35,negated_conjecture,
    ( esk226_0 = esk225_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_15]),c_0_12])]),c_0_33])).

cnf(c_0_36,negated_conjecture,
    ( r1_ordinal1(esk225_0,esk225_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_12])).

cnf(c_0_37,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_35]),c_0_36])]),
    [proof]).
%------------------------------------------------------------------------------
