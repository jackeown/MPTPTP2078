%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0470+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:46 EST 2020

% Result     : Theorem 0.90s
% Output     : CNFRefutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :   53 (  99 expanded)
%              Number of clauses        :   28 (  45 expanded)
%              Number of leaves         :   13 (  29 expanded)
%              Depth                    :   12
%              Number of atoms          :  115 ( 205 expanded)
%              Number of equality atoms :   28 (  60 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(cc1_relat_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

fof(t45_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => r1_tarski(k2_relat_1(k5_relat_1(X1,X2)),k2_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',fc1_xboole_0)).

fof(t62_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k5_relat_1(k1_xboole_0,X1) = k1_xboole_0
        & k5_relat_1(X1,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(d8_xboole_0,axiom,(
    ! [X1,X2] :
      ( r2_xboole_0(X1,X2)
    <=> ( r1_tarski(X1,X2)
        & X1 != X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',d8_xboole_0)).

fof(t115_xboole_1,axiom,(
    ! [X1] : ~ r2_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t115_xboole_1)).

fof(fc9_relat_1,axiom,(
    ! [X1] :
      ( ( ~ v1_xboole_0(X1)
        & v1_relat_1(X1) )
     => ~ v1_xboole_0(k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_relat_1)).

fof(t46_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(k2_relat_1(X1),k1_relat_1(X2))
           => k1_relat_1(k5_relat_1(X1,X2)) = k1_relat_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t2_xboole_1)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',l13_xboole_0)).

fof(dt_k5_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X2) )
     => v1_relat_1(k5_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(fc8_relat_1,axiom,(
    ! [X1] :
      ( ( ~ v1_xboole_0(X1)
        & v1_relat_1(X1) )
     => ~ v1_xboole_0(k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_relat_1)).

fof(c_0_13,plain,(
    ! [X2088] :
      ( ~ v1_xboole_0(X2088)
      | v1_relat_1(X2088) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relat_1])])).

fof(c_0_14,plain,(
    ! [X2234,X2235] :
      ( ~ v1_relat_1(X2234)
      | ~ v1_relat_1(X2235)
      | r1_tarski(k2_relat_1(k5_relat_1(X2234,X2235)),k2_relat_1(X2235)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_relat_1])])])).

cnf(c_0_15,plain,
    ( v1_relat_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_16,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ( k5_relat_1(k1_xboole_0,X1) = k1_xboole_0
          & k5_relat_1(X1,k1_xboole_0) = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t62_relat_1])).

cnf(c_0_18,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X1,X2)),k2_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_20,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

fof(c_0_21,negated_conjecture,
    ( v1_relat_1(esk140_0)
    & ( k5_relat_1(k1_xboole_0,esk140_0) != k1_xboole_0
      | k5_relat_1(esk140_0,k1_xboole_0) != k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

fof(c_0_22,plain,(
    ! [X64,X65] :
      ( ( r1_tarski(X64,X65)
        | ~ r2_xboole_0(X64,X65) )
      & ( X64 != X65
        | ~ r2_xboole_0(X64,X65) )
      & ( ~ r1_tarski(X64,X65)
        | X64 = X65
        | r2_xboole_0(X64,X65) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).

cnf(c_0_23,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X1,k1_xboole_0)),k1_xboole_0)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( v1_relat_1(esk140_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_25,plain,(
    ! [X172] : ~ r2_xboole_0(X172,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t115_xboole_1])])).

fof(c_0_26,plain,(
    ! [X2177] :
      ( v1_xboole_0(X2177)
      | ~ v1_relat_1(X2177)
      | ~ v1_xboole_0(k2_relat_1(X2177)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc9_relat_1])])])).

cnf(c_0_27,plain,
    ( X1 = X2
    | r2_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(k2_relat_1(k5_relat_1(esk140_0,k1_xboole_0)),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_29,plain,
    ( ~ r2_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_30,plain,(
    ! [X2236,X2237] :
      ( ~ v1_relat_1(X2236)
      | ~ v1_relat_1(X2237)
      | ~ r1_tarski(k2_relat_1(X2236),k1_relat_1(X2237))
      | k1_relat_1(k5_relat_1(X2236,X2237)) = k1_relat_1(X2236) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t46_relat_1])])])).

fof(c_0_31,plain,(
    ! [X239] : r1_tarski(k1_xboole_0,X239) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_32,plain,(
    ! [X69] :
      ( ~ v1_xboole_0(X69)
      | X69 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_33,plain,
    ( v1_xboole_0(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_xboole_0(k2_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( k2_relat_1(k5_relat_1(esk140_0,k1_xboole_0)) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])).

cnf(c_0_35,plain,
    ( k1_relat_1(k5_relat_1(X1,X2)) = k1_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_37,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_39,negated_conjecture,
    ( v1_xboole_0(k5_relat_1(esk140_0,k1_xboole_0))
    | ~ v1_relat_1(k5_relat_1(esk140_0,k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_16])])).

fof(c_0_40,plain,(
    ! [X2159,X2160] :
      ( ~ v1_relat_1(X2159)
      | ~ v1_relat_1(X2160)
      | v1_relat_1(k5_relat_1(X2159,X2160)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).

fof(c_0_41,plain,(
    ! [X2176] :
      ( v1_xboole_0(X2176)
      | ~ v1_relat_1(X2176)
      | ~ v1_xboole_0(k1_relat_1(X2176)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc8_relat_1])])])).

cnf(c_0_42,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,X1)) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_20]),c_0_36]),c_0_19]),c_0_37])])).

cnf(c_0_43,negated_conjecture,
    ( k5_relat_1(esk140_0,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k5_relat_1(esk140_0,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_44,plain,
    ( v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_45,plain,
    ( v1_xboole_0(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_xboole_0(k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_46,negated_conjecture,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,esk140_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_42,c_0_24])).

cnf(c_0_47,negated_conjecture,
    ( k5_relat_1(k1_xboole_0,esk140_0) != k1_xboole_0
    | k5_relat_1(esk140_0,k1_xboole_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_48,negated_conjecture,
    ( k5_relat_1(esk140_0,k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_19]),c_0_24])])).

cnf(c_0_49,negated_conjecture,
    ( v1_xboole_0(k5_relat_1(k1_xboole_0,esk140_0))
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,esk140_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_16])])).

cnf(c_0_50,negated_conjecture,
    ( k5_relat_1(k1_xboole_0,esk140_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_48])])).

cnf(c_0_51,negated_conjecture,
    ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,esk140_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_49]),c_0_50])).

cnf(c_0_52,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_44]),c_0_24]),c_0_19])]),
    [proof]).
%------------------------------------------------------------------------------
