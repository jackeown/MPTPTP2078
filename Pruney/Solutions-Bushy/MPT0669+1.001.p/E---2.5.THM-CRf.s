%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0669+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:00 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   33 ( 187 expanded)
%              Number of clauses        :   24 (  67 expanded)
%              Number of leaves         :    4 (  45 expanded)
%              Depth                    :   12
%              Number of atoms          :  207 (1269 expanded)
%              Number of equality atoms :   26 (  98 expanded)
%              Maximal formula depth    :   24 (   5 average)
%              Maximal clause size      :   79 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t86_funct_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(X1,k1_relat_1(k8_relat_1(X2,X3)))
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & r2_hidden(k1_funct_1(X3,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_funct_1)).

fof(t85_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v1_funct_1(X3) )
         => ( X2 = k8_relat_1(X1,X3)
          <=> ( ! [X4] :
                  ( r2_hidden(X4,k1_relat_1(X2))
                <=> ( r2_hidden(X4,k1_relat_1(X3))
                    & r2_hidden(k1_funct_1(X3,X4),X1) ) )
              & ! [X4] :
                  ( r2_hidden(X4,k1_relat_1(X2))
                 => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_funct_1)).

fof(fc9_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( v1_relat_1(k8_relat_1(X1,X2))
        & v1_funct_1(k8_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_funct_1)).

fof(dt_k8_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => v1_relat_1(k8_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_relat_1(X3)
          & v1_funct_1(X3) )
       => ( r2_hidden(X1,k1_relat_1(k8_relat_1(X2,X3)))
        <=> ( r2_hidden(X1,k1_relat_1(X3))
            & r2_hidden(k1_funct_1(X3,X1),X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t86_funct_1])).

fof(c_0_5,plain,(
    ! [X9,X10,X11,X12,X13,X14] :
      ( ( r2_hidden(X12,k1_relat_1(X11))
        | ~ r2_hidden(X12,k1_relat_1(X10))
        | X10 != k8_relat_1(X9,X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) )
      & ( r2_hidden(k1_funct_1(X11,X12),X9)
        | ~ r2_hidden(X12,k1_relat_1(X10))
        | X10 != k8_relat_1(X9,X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) )
      & ( ~ r2_hidden(X13,k1_relat_1(X11))
        | ~ r2_hidden(k1_funct_1(X11,X13),X9)
        | r2_hidden(X13,k1_relat_1(X10))
        | X10 != k8_relat_1(X9,X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) )
      & ( ~ r2_hidden(X14,k1_relat_1(X10))
        | k1_funct_1(X10,X14) = k1_funct_1(X11,X14)
        | X10 != k8_relat_1(X9,X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) )
      & ( r2_hidden(esk2_3(X9,X10,X11),k1_relat_1(X10))
        | ~ r2_hidden(esk1_3(X9,X10,X11),k1_relat_1(X10))
        | ~ r2_hidden(esk1_3(X9,X10,X11),k1_relat_1(X11))
        | ~ r2_hidden(k1_funct_1(X11,esk1_3(X9,X10,X11)),X9)
        | X10 = k8_relat_1(X9,X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) )
      & ( k1_funct_1(X10,esk2_3(X9,X10,X11)) != k1_funct_1(X11,esk2_3(X9,X10,X11))
        | ~ r2_hidden(esk1_3(X9,X10,X11),k1_relat_1(X10))
        | ~ r2_hidden(esk1_3(X9,X10,X11),k1_relat_1(X11))
        | ~ r2_hidden(k1_funct_1(X11,esk1_3(X9,X10,X11)),X9)
        | X10 = k8_relat_1(X9,X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) )
      & ( r2_hidden(esk2_3(X9,X10,X11),k1_relat_1(X10))
        | r2_hidden(esk1_3(X9,X10,X11),k1_relat_1(X11))
        | r2_hidden(esk1_3(X9,X10,X11),k1_relat_1(X10))
        | X10 = k8_relat_1(X9,X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) )
      & ( k1_funct_1(X10,esk2_3(X9,X10,X11)) != k1_funct_1(X11,esk2_3(X9,X10,X11))
        | r2_hidden(esk1_3(X9,X10,X11),k1_relat_1(X11))
        | r2_hidden(esk1_3(X9,X10,X11),k1_relat_1(X10))
        | X10 = k8_relat_1(X9,X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) )
      & ( r2_hidden(esk2_3(X9,X10,X11),k1_relat_1(X10))
        | r2_hidden(k1_funct_1(X11,esk1_3(X9,X10,X11)),X9)
        | r2_hidden(esk1_3(X9,X10,X11),k1_relat_1(X10))
        | X10 = k8_relat_1(X9,X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) )
      & ( k1_funct_1(X10,esk2_3(X9,X10,X11)) != k1_funct_1(X11,esk2_3(X9,X10,X11))
        | r2_hidden(k1_funct_1(X11,esk1_3(X9,X10,X11)),X9)
        | r2_hidden(esk1_3(X9,X10,X11),k1_relat_1(X10))
        | X10 = k8_relat_1(X9,X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t85_funct_1])])])])])])).

fof(c_0_6,negated_conjecture,
    ( v1_relat_1(esk5_0)
    & v1_funct_1(esk5_0)
    & ( ~ r2_hidden(esk3_0,k1_relat_1(k8_relat_1(esk4_0,esk5_0)))
      | ~ r2_hidden(esk3_0,k1_relat_1(esk5_0))
      | ~ r2_hidden(k1_funct_1(esk5_0,esk3_0),esk4_0) )
    & ( r2_hidden(esk3_0,k1_relat_1(esk5_0))
      | r2_hidden(esk3_0,k1_relat_1(k8_relat_1(esk4_0,esk5_0))) )
    & ( r2_hidden(k1_funct_1(esk5_0,esk3_0),esk4_0)
      | r2_hidden(esk3_0,k1_relat_1(k8_relat_1(esk4_0,esk5_0))) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])])).

cnf(c_0_7,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(X1,k1_relat_1(X3))
    | X3 != k8_relat_1(X4,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,negated_conjecture,
    ( r2_hidden(esk3_0,k1_relat_1(esk5_0))
    | r2_hidden(esk3_0,k1_relat_1(k8_relat_1(esk4_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_9,plain,(
    ! [X7,X8] :
      ( ( v1_relat_1(k8_relat_1(X7,X8))
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8) )
      & ( v1_funct_1(k8_relat_1(X7,X8))
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_funct_1])])])).

cnf(c_0_10,plain,
    ( r2_hidden(k1_funct_1(X1,X2),X3)
    | ~ r2_hidden(X2,k1_relat_1(X4))
    | X4 != k8_relat_1(X3,X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X4)
    | ~ v1_funct_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_11,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk5_0,esk3_0),esk4_0)
    | r2_hidden(esk3_0,k1_relat_1(k8_relat_1(esk4_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,negated_conjecture,
    ( r2_hidden(esk3_0,k1_relat_1(esk5_0))
    | r2_hidden(esk3_0,k1_relat_1(X1))
    | k8_relat_1(esk4_0,esk5_0) != k8_relat_1(X2,X1)
    | ~ v1_funct_1(k8_relat_1(esk4_0,esk5_0))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k8_relat_1(esk4_0,esk5_0))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_13,plain,
    ( v1_funct_1(k8_relat_1(X1,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_15,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_16,plain,(
    ! [X5,X6] :
      ( ~ v1_relat_1(X6)
      | v1_relat_1(k8_relat_1(X5,X6)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_relat_1])])).

cnf(c_0_17,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk5_0,esk3_0),esk4_0)
    | r2_hidden(k1_funct_1(X1,esk3_0),X2)
    | k8_relat_1(esk4_0,esk5_0) != k8_relat_1(X2,X1)
    | ~ v1_funct_1(k8_relat_1(esk4_0,esk5_0))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k8_relat_1(esk4_0,esk5_0))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(esk3_0,k1_relat_1(esk5_0))
    | r2_hidden(esk3_0,k1_relat_1(X1))
    | k8_relat_1(esk4_0,esk5_0) != k8_relat_1(X2,X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k8_relat_1(esk4_0,esk5_0))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14]),c_0_15])])).

cnf(c_0_19,plain,
    ( v1_relat_1(k8_relat_1(X2,X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk5_0,esk3_0),esk4_0)
    | r2_hidden(k1_funct_1(X1,esk3_0),X2)
    | k8_relat_1(esk4_0,esk5_0) != k8_relat_1(X2,X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k8_relat_1(esk4_0,esk5_0))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_13]),c_0_14]),c_0_15])])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(esk3_0,k1_relat_1(esk5_0))
    | r2_hidden(esk3_0,k1_relat_1(X1))
    | k8_relat_1(esk4_0,esk5_0) != k8_relat_1(X2,X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_15])])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk5_0,esk3_0),esk4_0)
    | r2_hidden(k1_funct_1(X1,esk3_0),X2)
    | k8_relat_1(esk4_0,esk5_0) != k8_relat_1(X2,X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_19]),c_0_15])])).

cnf(c_0_23,negated_conjecture,
    ( ~ r2_hidden(esk3_0,k1_relat_1(k8_relat_1(esk4_0,esk5_0)))
    | ~ r2_hidden(esk3_0,k1_relat_1(esk5_0))
    | ~ r2_hidden(k1_funct_1(esk5_0,esk3_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk3_0,k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_21]),c_0_14]),c_0_15])])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,k1_relat_1(X4))
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k1_funct_1(X2,X1),X3)
    | X4 != k8_relat_1(X3,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X4)
    | ~ v1_funct_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk5_0,esk3_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_22]),c_0_14]),c_0_15])])).

cnf(c_0_27,negated_conjecture,
    ( ~ r2_hidden(esk3_0,k1_relat_1(k8_relat_1(esk4_0,esk5_0)))
    | ~ r2_hidden(k1_funct_1(esk5_0,esk3_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_24])])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk3_0,k1_relat_1(X1))
    | X1 != k8_relat_1(esk4_0,esk5_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_24]),c_0_14]),c_0_15])])).

cnf(c_0_29,negated_conjecture,
    ( ~ r2_hidden(esk3_0,k1_relat_1(k8_relat_1(esk4_0,esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_26])])).

cnf(c_0_30,negated_conjecture,
    ( ~ v1_funct_1(k8_relat_1(esk4_0,esk5_0))
    | ~ v1_relat_1(k8_relat_1(esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_28]),c_0_29])).

cnf(c_0_31,negated_conjecture,
    ( ~ v1_relat_1(k8_relat_1(esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_13]),c_0_14]),c_0_15])])).

cnf(c_0_32,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_19]),c_0_15])]),
    [proof]).

%------------------------------------------------------------------------------
