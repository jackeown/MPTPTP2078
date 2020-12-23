%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0616+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:54 EST 2020

% Result     : Theorem 0.15s
% Output     : CNFRefutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :   23 (  79 expanded)
%              Number of clauses        :   16 (  32 expanded)
%              Number of leaves         :    3 (  18 expanded)
%              Depth                    :    7
%              Number of atoms          :  100 ( 425 expanded)
%              Number of equality atoms :   26 ( 104 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t8_funct_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & X2 = k1_funct_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_relat_1(X3)
          & v1_funct_1(X3) )
       => ( r2_hidden(k4_tarski(X1,X2),X3)
        <=> ( r2_hidden(X1,k1_relat_1(X3))
            & X2 = k1_funct_1(X3,X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t8_funct_1])).

fof(c_0_4,plain,(
    ! [X8,X9,X10,X12,X13,X14,X15,X17] :
      ( ( ~ r2_hidden(X10,X9)
        | r2_hidden(k4_tarski(X10,esk1_3(X8,X9,X10)),X8)
        | X9 != k1_relat_1(X8) )
      & ( ~ r2_hidden(k4_tarski(X12,X13),X8)
        | r2_hidden(X12,X9)
        | X9 != k1_relat_1(X8) )
      & ( ~ r2_hidden(esk2_2(X14,X15),X15)
        | ~ r2_hidden(k4_tarski(esk2_2(X14,X15),X17),X14)
        | X15 = k1_relat_1(X14) )
      & ( r2_hidden(esk2_2(X14,X15),X15)
        | r2_hidden(k4_tarski(esk2_2(X14,X15),esk3_2(X14,X15)),X14)
        | X15 = k1_relat_1(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

fof(c_0_5,plain,(
    ! [X5,X6,X7] :
      ( ( X7 != k1_funct_1(X5,X6)
        | r2_hidden(k4_tarski(X6,X7),X5)
        | ~ r2_hidden(X6,k1_relat_1(X5))
        | ~ v1_relat_1(X5)
        | ~ v1_funct_1(X5) )
      & ( ~ r2_hidden(k4_tarski(X6,X7),X5)
        | X7 = k1_funct_1(X5,X6)
        | ~ r2_hidden(X6,k1_relat_1(X5))
        | ~ v1_relat_1(X5)
        | ~ v1_funct_1(X5) )
      & ( X7 != k1_funct_1(X5,X6)
        | X7 = k1_xboole_0
        | r2_hidden(X6,k1_relat_1(X5))
        | ~ v1_relat_1(X5)
        | ~ v1_funct_1(X5) )
      & ( X7 != k1_xboole_0
        | X7 = k1_funct_1(X5,X6)
        | r2_hidden(X6,k1_relat_1(X5))
        | ~ v1_relat_1(X5)
        | ~ v1_funct_1(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_funct_1])])])])])).

fof(c_0_6,negated_conjecture,
    ( v1_relat_1(esk6_0)
    & v1_funct_1(esk6_0)
    & ( ~ r2_hidden(k4_tarski(esk4_0,esk5_0),esk6_0)
      | ~ r2_hidden(esk4_0,k1_relat_1(esk6_0))
      | esk5_0 != k1_funct_1(esk6_0,esk4_0) )
    & ( r2_hidden(esk4_0,k1_relat_1(esk6_0))
      | r2_hidden(k4_tarski(esk4_0,esk5_0),esk6_0) )
    & ( esk5_0 = k1_funct_1(esk6_0,esk4_0)
      | r2_hidden(k4_tarski(esk4_0,esk5_0),esk6_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])])).

cnf(c_0_7,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,plain,
    ( r2_hidden(k4_tarski(X3,X1),X2)
    | X1 != k1_funct_1(X2,X3)
    | ~ r2_hidden(X3,k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( r2_hidden(esk4_0,k1_relat_1(esk6_0))
    | r2_hidden(k4_tarski(esk4_0,esk5_0),esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2) ),
    inference(er,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk4_0,esk5_0),esk6_0)
    | ~ r2_hidden(esk4_0,k1_relat_1(esk6_0))
    | esk5_0 != k1_funct_1(esk6_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,plain,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(er,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( esk5_0 = k1_funct_1(esk6_0,esk4_0)
    | r2_hidden(k4_tarski(esk4_0,esk5_0),esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_14,negated_conjecture,
    ( r2_hidden(esk4_0,k1_relat_1(esk6_0)) ),
    inference(csr,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_16,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_17,negated_conjecture,
    ( k1_funct_1(esk6_0,esk4_0) != esk5_0
    | ~ r2_hidden(k4_tarski(esk4_0,esk5_0),esk6_0) ),
    inference(csr,[status(thm)],[c_0_11,c_0_10])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(k4_tarski(esk4_0,esk5_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14]),c_0_15]),c_0_16])])).

cnf(c_0_19,plain,
    ( X2 = k1_funct_1(X3,X1)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,k1_relat_1(X3))
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_20,negated_conjecture,
    ( k1_funct_1(esk6_0,esk4_0) != esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_18])])).

cnf(c_0_21,plain,
    ( X1 = k1_funct_1(X2,X3)
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[c_0_19,c_0_10])).

cnf(c_0_22,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_15]),c_0_16])])]),c_0_18])]),
    [proof]).

%------------------------------------------------------------------------------
