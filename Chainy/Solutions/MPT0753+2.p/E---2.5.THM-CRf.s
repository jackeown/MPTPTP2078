%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0753+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:51 EST 2020

% Result     : Theorem 0.65s
% Output     : CNFRefutation 0.65s
% Verified   : 
% Statistics : Number of formulae       :   22 (  35 expanded)
%              Number of clauses        :   13 (  14 expanded)
%              Number of leaves         :    4 (   8 expanded)
%              Depth                    :    6
%              Number of atoms          :   68 ( 153 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t46_ordinal1,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v3_ordinal1(k1_relat_1(X1))
       => ( v1_relat_1(X1)
          & v5_relat_1(X1,k2_relat_1(X1))
          & v1_funct_1(X1)
          & v5_ordinal1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_ordinal1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',d10_xboole_0)).

fof(d7_ordinal1,axiom,(
    ! [X1] :
      ( v5_ordinal1(X1)
    <=> v3_ordinal1(k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_ordinal1)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT007+2.ax',d19_relat_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ( v3_ordinal1(k1_relat_1(X1))
         => ( v1_relat_1(X1)
            & v5_relat_1(X1,k2_relat_1(X1))
            & v1_funct_1(X1)
            & v5_ordinal1(X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t46_ordinal1])).

fof(c_0_5,plain,(
    ! [X104,X105] :
      ( ( r1_tarski(X104,X105)
        | X104 != X105 )
      & ( r1_tarski(X105,X104)
        | X104 != X105 )
      & ( ~ r1_tarski(X104,X105)
        | ~ r1_tarski(X105,X104)
        | X104 = X105 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_6,negated_conjecture,
    ( v1_relat_1(esk239_0)
    & v1_funct_1(esk239_0)
    & v3_ordinal1(k1_relat_1(esk239_0))
    & ( ~ v1_relat_1(esk239_0)
      | ~ v5_relat_1(esk239_0,k2_relat_1(esk239_0))
      | ~ v1_funct_1(esk239_0)
      | ~ v5_ordinal1(esk239_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

fof(c_0_7,plain,(
    ! [X3170] :
      ( ( ~ v5_ordinal1(X3170)
        | v3_ordinal1(k1_relat_1(X3170)) )
      & ( ~ v3_ordinal1(k1_relat_1(X3170))
        | v5_ordinal1(X3170) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_ordinal1])])).

fof(c_0_8,plain,(
    ! [X2154,X2155] :
      ( ( ~ v5_relat_1(X2155,X2154)
        | r1_tarski(k2_relat_1(X2155),X2154)
        | ~ v1_relat_1(X2155) )
      & ( ~ r1_tarski(k2_relat_1(X2155),X2154)
        | v5_relat_1(X2155,X2154)
        | ~ v1_relat_1(X2155) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

cnf(c_0_9,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,negated_conjecture,
    ( ~ v1_relat_1(esk239_0)
    | ~ v5_relat_1(esk239_0,k2_relat_1(esk239_0))
    | ~ v1_funct_1(esk239_0)
    | ~ v5_ordinal1(esk239_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( v1_relat_1(esk239_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,negated_conjecture,
    ( v1_funct_1(esk239_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_13,plain,
    ( v5_ordinal1(X1)
    | ~ v3_ordinal1(k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,negated_conjecture,
    ( v3_ordinal1(k1_relat_1(esk239_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_15,plain,
    ( v5_relat_1(X1,X2)
    | ~ r1_tarski(k2_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_16,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_9])).

cnf(c_0_17,negated_conjecture,
    ( ~ v5_ordinal1(esk239_0)
    | ~ v5_relat_1(esk239_0,k2_relat_1(esk239_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_10,c_0_11]),c_0_12])])).

cnf(c_0_18,negated_conjecture,
    ( v5_ordinal1(esk239_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_19,plain,
    ( v5_relat_1(X1,k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( ~ v5_relat_1(esk239_0,k2_relat_1(esk239_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_18])])).

cnf(c_0_21,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_11]),c_0_20]),
    [proof]).
%------------------------------------------------------------------------------
