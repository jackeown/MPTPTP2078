%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0617+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:55 EST 2020

% Result     : Theorem 0.15s
% Output     : CNFRefutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :   36 ( 316 expanded)
%              Number of clauses        :   27 ( 125 expanded)
%              Number of leaves         :    4 (  73 expanded)
%              Depth                    :   11
%              Number of atoms          :  151 (1933 expanded)
%              Number of equality atoms :   41 ( 632 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t9_funct_1,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ( ( k1_relat_1(X1) = k1_relat_1(X2)
              & ! [X3] :
                  ( r2_hidden(X3,k1_relat_1(X1))
                 => k1_funct_1(X1,X3) = k1_funct_1(X2,X3) ) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).

fof(d2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( X1 = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X1)
              <=> r2_hidden(k4_tarski(X3,X4),X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_relat_1)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

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

fof(c_0_4,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( v1_relat_1(X2)
              & v1_funct_1(X2) )
           => ( ( k1_relat_1(X1) = k1_relat_1(X2)
                & ! [X3] :
                    ( r2_hidden(X3,k1_relat_1(X1))
                   => k1_funct_1(X1,X3) = k1_funct_1(X2,X3) ) )
             => X1 = X2 ) ) ) ),
    inference(assume_negation,[status(cth)],[t9_funct_1])).

fof(c_0_5,plain,(
    ! [X5,X6,X7,X8,X9,X10] :
      ( ( ~ r2_hidden(k4_tarski(X7,X8),X5)
        | r2_hidden(k4_tarski(X7,X8),X6)
        | X5 != X6
        | ~ v1_relat_1(X6)
        | ~ v1_relat_1(X5) )
      & ( ~ r2_hidden(k4_tarski(X9,X10),X6)
        | r2_hidden(k4_tarski(X9,X10),X5)
        | X5 != X6
        | ~ v1_relat_1(X6)
        | ~ v1_relat_1(X5) )
      & ( ~ r2_hidden(k4_tarski(esk1_2(X5,X6),esk2_2(X5,X6)),X5)
        | ~ r2_hidden(k4_tarski(esk1_2(X5,X6),esk2_2(X5,X6)),X6)
        | X5 = X6
        | ~ v1_relat_1(X6)
        | ~ v1_relat_1(X5) )
      & ( r2_hidden(k4_tarski(esk1_2(X5,X6),esk2_2(X5,X6)),X5)
        | r2_hidden(k4_tarski(esk1_2(X5,X6),esk2_2(X5,X6)),X6)
        | X5 = X6
        | ~ v1_relat_1(X6)
        | ~ v1_relat_1(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_relat_1])])])])])])).

fof(c_0_6,negated_conjecture,(
    ! [X29] :
      ( v1_relat_1(esk6_0)
      & v1_funct_1(esk6_0)
      & v1_relat_1(esk7_0)
      & v1_funct_1(esk7_0)
      & k1_relat_1(esk6_0) = k1_relat_1(esk7_0)
      & ( ~ r2_hidden(X29,k1_relat_1(esk6_0))
        | k1_funct_1(esk6_0,X29) = k1_funct_1(esk7_0,X29) )
      & esk6_0 != esk7_0 ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])])).

fof(c_0_7,plain,(
    ! [X16,X17,X18,X20,X21,X22,X23,X25] :
      ( ( ~ r2_hidden(X18,X17)
        | r2_hidden(k4_tarski(X18,esk3_3(X16,X17,X18)),X16)
        | X17 != k1_relat_1(X16) )
      & ( ~ r2_hidden(k4_tarski(X20,X21),X16)
        | r2_hidden(X20,X17)
        | X17 != k1_relat_1(X16) )
      & ( ~ r2_hidden(esk4_2(X22,X23),X23)
        | ~ r2_hidden(k4_tarski(esk4_2(X22,X23),X25),X22)
        | X23 = k1_relat_1(X22) )
      & ( r2_hidden(esk4_2(X22,X23),X23)
        | r2_hidden(k4_tarski(esk4_2(X22,X23),esk5_2(X22,X23)),X22)
        | X23 = k1_relat_1(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

cnf(c_0_8,plain,
    ( r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X1)
    | r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X2)
    | X1 = X2
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( esk7_0 = X1
    | r2_hidden(k4_tarski(esk1_2(esk7_0,X1),esk2_2(esk7_0,X1)),esk7_0)
    | r2_hidden(k4_tarski(esk1_2(esk7_0,X1),esk2_2(esk7_0,X1)),X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_12,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_13,negated_conjecture,
    ( esk6_0 != esk7_0 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_14,plain,(
    ! [X13,X14,X15] :
      ( ( X15 != k1_funct_1(X13,X14)
        | r2_hidden(k4_tarski(X14,X15),X13)
        | ~ r2_hidden(X14,k1_relat_1(X13))
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13) )
      & ( ~ r2_hidden(k4_tarski(X14,X15),X13)
        | X15 = k1_funct_1(X13,X14)
        | ~ r2_hidden(X14,k1_relat_1(X13))
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13) )
      & ( X15 != k1_funct_1(X13,X14)
        | X15 = k1_xboole_0
        | r2_hidden(X14,k1_relat_1(X13))
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13) )
      & ( X15 != k1_xboole_0
        | X15 = k1_funct_1(X13,X14)
        | r2_hidden(X14,k1_relat_1(X13))
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_funct_1])])])])])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2) ),
    inference(er,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_2(esk7_0,esk6_0),esk2_2(esk7_0,esk6_0)),esk6_0)
    | r2_hidden(k4_tarski(esk1_2(esk7_0,esk6_0),esk2_2(esk7_0,esk6_0)),esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( k1_relat_1(esk6_0) = k1_relat_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_18,plain,
    ( X2 = k1_funct_1(X3,X1)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,k1_relat_1(X3))
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( k1_funct_1(esk6_0,X1) = k1_funct_1(esk7_0,X1)
    | ~ r2_hidden(X1,k1_relat_1(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(esk1_2(esk7_0,esk6_0),k1_relat_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_15])).

cnf(c_0_21,plain,
    ( r2_hidden(k4_tarski(X3,X1),X2)
    | X1 != k1_funct_1(X2,X3)
    | ~ r2_hidden(X3,k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( X1 = k1_funct_1(X2,X3)
    | ~ v1_funct_1(X2)
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[c_0_18,c_0_15])).

cnf(c_0_23,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_24,negated_conjecture,
    ( k1_funct_1(esk7_0,esk1_2(esk7_0,esk6_0)) = k1_funct_1(esk6_0,esk1_2(esk7_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_25,plain,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)
    | ~ v1_funct_1(X2)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X2) ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_27,negated_conjecture,
    ( k1_funct_1(esk6_0,esk1_2(esk7_0,esk6_0)) = esk2_2(esk7_0,esk6_0)
    | r2_hidden(k4_tarski(esk1_2(esk7_0,esk6_0),esk2_2(esk7_0,esk6_0)),esk6_0) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_16]),c_0_23]),c_0_9])]),c_0_24])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(esk7_0,X1)),esk7_0)
    | ~ r2_hidden(X1,k1_relat_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_17]),c_0_23]),c_0_9])])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_2(esk7_0,esk6_0),k1_funct_1(esk6_0,esk1_2(esk7_0,esk6_0))),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_20]),c_0_26]),c_0_12])])).

cnf(c_0_30,negated_conjecture,
    ( k1_funct_1(esk6_0,esk1_2(esk7_0,esk6_0)) = esk2_2(esk7_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_27]),c_0_26]),c_0_12])])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_2(esk7_0,esk6_0),k1_funct_1(esk6_0,esk1_2(esk7_0,esk6_0))),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_24]),c_0_20])])).

cnf(c_0_32,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X1)
    | ~ r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_2(esk7_0,esk6_0),esk2_2(esk7_0,esk6_0)),esk6_0) ),
    inference(rw,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_2(esk7_0,esk6_0),esk2_2(esk7_0,esk6_0)),esk7_0) ),
    inference(rw,[status(thm)],[c_0_31,c_0_30])).

cnf(c_0_35,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_12]),c_0_9])]),c_0_13]),
    [proof]).

%------------------------------------------------------------------------------
