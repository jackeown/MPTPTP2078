%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0616+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:48 EST 2020

% Result     : Theorem 1.21s
% Output     : CNFRefutation 1.21s
% Verified   : 
% Statistics : Number of formulae       :   25 ( 153 expanded)
%              Number of clauses        :   18 (  66 expanded)
%              Number of leaves         :    3 (  34 expanded)
%              Depth                    :   10
%              Number of atoms          :   99 ( 800 expanded)
%              Number of equality atoms :   28 ( 209 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT007+2.ax',d4_relat_1)).

fof(d4_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2,X3] :
          ( ( r2_hidden(X2,k1_relat_1(X1))
           => ( X3 = k1_funct_1(X1,X2)
            <=> r2_hidden(k4_tarski(X2,X3),X1) ) )
          & ( ~ r2_hidden(X2,k1_relat_1(X1))
           => ( X3 = k1_funct_1(X1,X2)
            <=> X3 = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).

fof(t8_funct_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & X2 = k1_funct_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(c_0_3,plain,(
    ! [X2179,X2180,X2181,X2183,X2184,X2185,X2186,X2188] :
      ( ( ~ r2_hidden(X2181,X2180)
        | r2_hidden(k4_tarski(X2181,esk135_3(X2179,X2180,X2181)),X2179)
        | X2180 != k1_relat_1(X2179) )
      & ( ~ r2_hidden(k4_tarski(X2183,X2184),X2179)
        | r2_hidden(X2183,X2180)
        | X2180 != k1_relat_1(X2179) )
      & ( ~ r2_hidden(esk136_2(X2185,X2186),X2186)
        | ~ r2_hidden(k4_tarski(esk136_2(X2185,X2186),X2188),X2185)
        | X2186 = k1_relat_1(X2185) )
      & ( r2_hidden(esk136_2(X2185,X2186),X2186)
        | r2_hidden(k4_tarski(esk136_2(X2185,X2186),esk137_2(X2185,X2186)),X2185)
        | X2186 = k1_relat_1(X2185) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

fof(c_0_4,plain,(
    ! [X2718,X2719,X2720] :
      ( ( X2720 != k1_funct_1(X2718,X2719)
        | r2_hidden(k4_tarski(X2719,X2720),X2718)
        | ~ r2_hidden(X2719,k1_relat_1(X2718))
        | ~ v1_relat_1(X2718)
        | ~ v1_funct_1(X2718) )
      & ( ~ r2_hidden(k4_tarski(X2719,X2720),X2718)
        | X2720 = k1_funct_1(X2718,X2719)
        | ~ r2_hidden(X2719,k1_relat_1(X2718))
        | ~ v1_relat_1(X2718)
        | ~ v1_funct_1(X2718) )
      & ( X2720 != k1_funct_1(X2718,X2719)
        | X2720 = k1_xboole_0
        | r2_hidden(X2719,k1_relat_1(X2718))
        | ~ v1_relat_1(X2718)
        | ~ v1_funct_1(X2718) )
      & ( X2720 != k1_xboole_0
        | X2720 = k1_funct_1(X2718,X2719)
        | r2_hidden(X2719,k1_relat_1(X2718))
        | ~ v1_relat_1(X2718)
        | ~ v1_funct_1(X2718) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_funct_1])])])])])).

cnf(c_0_5,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_relat_1(X3)
          & v1_funct_1(X3) )
       => ( r2_hidden(k4_tarski(X1,X2),X3)
        <=> ( r2_hidden(X1,k1_relat_1(X3))
            & X2 = k1_funct_1(X3,X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t8_funct_1])).

cnf(c_0_7,plain,
    ( X2 = k1_funct_1(X3,X1)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,k1_relat_1(X3))
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2) ),
    inference(er,[status(thm)],[c_0_5])).

fof(c_0_9,negated_conjecture,
    ( v1_relat_1(esk161_0)
    & v1_funct_1(esk161_0)
    & ( ~ r2_hidden(k4_tarski(esk159_0,esk160_0),esk161_0)
      | ~ r2_hidden(esk159_0,k1_relat_1(esk161_0))
      | esk160_0 != k1_funct_1(esk161_0,esk159_0) )
    & ( r2_hidden(esk159_0,k1_relat_1(esk161_0))
      | r2_hidden(k4_tarski(esk159_0,esk160_0),esk161_0) )
    & ( esk160_0 = k1_funct_1(esk161_0,esk159_0)
      | r2_hidden(k4_tarski(esk159_0,esk160_0),esk161_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])])).

cnf(c_0_10,plain,
    ( X1 = k1_funct_1(X2,X3)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X3,X1),X2) ),
    inference(csr,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( v1_funct_1(esk161_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,negated_conjecture,
    ( v1_relat_1(esk161_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( X1 = k1_funct_1(esk161_0,X2)
    | ~ r2_hidden(k4_tarski(X2,X1),esk161_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12])])).

cnf(c_0_14,negated_conjecture,
    ( esk160_0 = k1_funct_1(esk161_0,esk159_0)
    | r2_hidden(k4_tarski(esk159_0,esk160_0),esk161_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( r2_hidden(k4_tarski(X1,esk135_3(X3,X2,X1)),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_16,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk159_0,esk160_0),esk161_0)
    | ~ r2_hidden(esk159_0,k1_relat_1(esk161_0))
    | esk160_0 != k1_funct_1(esk161_0,esk159_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,negated_conjecture,
    ( k1_funct_1(esk161_0,esk159_0) = esk160_0 ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_18,plain,
    ( r2_hidden(k4_tarski(X1,esk135_3(X2,k1_relat_1(X2),X1)),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(esk159_0,k1_relat_1(esk161_0))
    | r2_hidden(k4_tarski(esk159_0,esk160_0),esk161_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_20,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk159_0,esk160_0),esk161_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_16,c_0_17])]),c_0_8])).

cnf(c_0_21,negated_conjecture,
    ( esk135_3(esk161_0,k1_relat_1(esk161_0),X1) = k1_funct_1(esk161_0,X1)
    | ~ r2_hidden(X1,k1_relat_1(esk161_0)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk159_0,k1_relat_1(esk161_0)) ),
    inference(sr,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_23,negated_conjecture,
    ( esk135_3(esk161_0,k1_relat_1(esk161_0),esk159_0) = esk160_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_23]),c_0_22])]),c_0_20]),
    [proof]).
%------------------------------------------------------------------------------
