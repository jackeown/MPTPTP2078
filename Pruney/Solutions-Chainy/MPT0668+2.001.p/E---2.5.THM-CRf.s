%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:54:19 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   93 (42174 expanded)
%              Number of clauses        :   86 (15919 expanded)
%              Number of leaves         :    3 (9895 expanded)
%              Depth                    :   26
%              Number of atoms          :  406 (553268 expanded)
%              Number of equality atoms :  127 (146517 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   43 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t85_funct_1,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_funct_1)).

fof(t8_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & X2 = k1_funct_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(d12_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( X3 = k8_relat_1(X1,X2)
          <=> ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X3)
              <=> ( r2_hidden(X5,X1)
                  & r2_hidden(k4_tarski(X4,X5),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_relat_1)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2] :
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
    inference(assume_negation,[status(cth)],[t85_funct_1])).

fof(c_0_4,plain,(
    ! [X15,X16,X17] :
      ( ( r2_hidden(X15,k1_relat_1(X17))
        | ~ r2_hidden(k4_tarski(X15,X16),X17)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) )
      & ( X16 = k1_funct_1(X17,X15)
        | ~ r2_hidden(k4_tarski(X15,X16),X17)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) )
      & ( ~ r2_hidden(X15,k1_relat_1(X17))
        | X16 != k1_funct_1(X17,X15)
        | r2_hidden(k4_tarski(X15,X16),X17)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).

fof(c_0_5,plain,(
    ! [X6,X7,X8,X9,X10,X11,X12] :
      ( ( r2_hidden(X10,X6)
        | ~ r2_hidden(k4_tarski(X9,X10),X8)
        | X8 != k8_relat_1(X6,X7)
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(X7) )
      & ( r2_hidden(k4_tarski(X9,X10),X7)
        | ~ r2_hidden(k4_tarski(X9,X10),X8)
        | X8 != k8_relat_1(X6,X7)
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(X7) )
      & ( ~ r2_hidden(X12,X6)
        | ~ r2_hidden(k4_tarski(X11,X12),X7)
        | r2_hidden(k4_tarski(X11,X12),X8)
        | X8 != k8_relat_1(X6,X7)
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(X7) )
      & ( ~ r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X8)
        | ~ r2_hidden(esk2_3(X6,X7,X8),X6)
        | ~ r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X7)
        | X8 = k8_relat_1(X6,X7)
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(X7) )
      & ( r2_hidden(esk2_3(X6,X7,X8),X6)
        | r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X8)
        | X8 = k8_relat_1(X6,X7)
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(X7) )
      & ( r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X7)
        | r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X8)
        | X8 = k8_relat_1(X6,X7)
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_relat_1])])])])])])).

fof(c_0_6,negated_conjecture,(
    ! [X23,X24] :
      ( v1_relat_1(esk4_0)
      & v1_funct_1(esk4_0)
      & v1_relat_1(esk5_0)
      & v1_funct_1(esk5_0)
      & ( r2_hidden(esk7_0,k1_relat_1(esk4_0))
        | ~ r2_hidden(esk6_0,k1_relat_1(esk4_0))
        | ~ r2_hidden(esk6_0,k1_relat_1(esk5_0))
        | ~ r2_hidden(k1_funct_1(esk5_0,esk6_0),esk3_0)
        | esk4_0 != k8_relat_1(esk3_0,esk5_0) )
      & ( k1_funct_1(esk4_0,esk7_0) != k1_funct_1(esk5_0,esk7_0)
        | ~ r2_hidden(esk6_0,k1_relat_1(esk4_0))
        | ~ r2_hidden(esk6_0,k1_relat_1(esk5_0))
        | ~ r2_hidden(k1_funct_1(esk5_0,esk6_0),esk3_0)
        | esk4_0 != k8_relat_1(esk3_0,esk5_0) )
      & ( r2_hidden(esk7_0,k1_relat_1(esk4_0))
        | r2_hidden(esk6_0,k1_relat_1(esk5_0))
        | r2_hidden(esk6_0,k1_relat_1(esk4_0))
        | esk4_0 != k8_relat_1(esk3_0,esk5_0) )
      & ( k1_funct_1(esk4_0,esk7_0) != k1_funct_1(esk5_0,esk7_0)
        | r2_hidden(esk6_0,k1_relat_1(esk5_0))
        | r2_hidden(esk6_0,k1_relat_1(esk4_0))
        | esk4_0 != k8_relat_1(esk3_0,esk5_0) )
      & ( r2_hidden(esk7_0,k1_relat_1(esk4_0))
        | r2_hidden(k1_funct_1(esk5_0,esk6_0),esk3_0)
        | r2_hidden(esk6_0,k1_relat_1(esk4_0))
        | esk4_0 != k8_relat_1(esk3_0,esk5_0) )
      & ( k1_funct_1(esk4_0,esk7_0) != k1_funct_1(esk5_0,esk7_0)
        | r2_hidden(k1_funct_1(esk5_0,esk6_0),esk3_0)
        | r2_hidden(esk6_0,k1_relat_1(esk4_0))
        | esk4_0 != k8_relat_1(esk3_0,esk5_0) )
      & ( r2_hidden(X23,k1_relat_1(esk5_0))
        | ~ r2_hidden(X23,k1_relat_1(esk4_0))
        | esk4_0 = k8_relat_1(esk3_0,esk5_0) )
      & ( r2_hidden(k1_funct_1(esk5_0,X23),esk3_0)
        | ~ r2_hidden(X23,k1_relat_1(esk4_0))
        | esk4_0 = k8_relat_1(esk3_0,esk5_0) )
      & ( ~ r2_hidden(X23,k1_relat_1(esk5_0))
        | ~ r2_hidden(k1_funct_1(esk5_0,X23),esk3_0)
        | r2_hidden(X23,k1_relat_1(esk4_0))
        | esk4_0 = k8_relat_1(esk3_0,esk5_0) )
      & ( ~ r2_hidden(X24,k1_relat_1(esk4_0))
        | k1_funct_1(esk4_0,X24) = k1_funct_1(esk5_0,X24)
        | esk4_0 = k8_relat_1(esk3_0,esk5_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])])])).

cnf(c_0_7,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X1)
    | r2_hidden(k4_tarski(esk1_3(X1,X2,X3),esk2_3(X1,X2,X3)),X3)
    | X3 = k8_relat_1(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk5_0,X1),esk3_0)
    | esk4_0 = k8_relat_1(esk3_0,esk5_0)
    | ~ r2_hidden(X1,k1_relat_1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( X1 = k8_relat_1(X2,X3)
    | r2_hidden(esk1_3(X2,X3,X1),k1_relat_1(X1))
    | r2_hidden(esk2_3(X2,X3,X1),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X3) ),
    inference(spm,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_13,negated_conjecture,
    ( k1_funct_1(esk4_0,X1) = k1_funct_1(esk5_0,X1)
    | esk4_0 = k8_relat_1(esk3_0,esk5_0)
    | ~ r2_hidden(X1,k1_relat_1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_14,negated_conjecture,
    ( k8_relat_1(esk3_0,esk5_0) = esk4_0
    | esk4_0 = k8_relat_1(X1,X2)
    | r2_hidden(k1_funct_1(esk5_0,esk1_3(X1,X2,esk4_0)),esk3_0)
    | r2_hidden(esk2_3(X1,X2,esk4_0),X1)
    | ~ v1_relat_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11]),c_0_12])])).

cnf(c_0_15,negated_conjecture,
    ( k1_funct_1(esk5_0,esk1_3(X1,X2,esk4_0)) = k1_funct_1(esk4_0,esk1_3(X1,X2,esk4_0))
    | k8_relat_1(esk3_0,esk5_0) = esk4_0
    | esk4_0 = k8_relat_1(X1,X2)
    | r2_hidden(esk2_3(X1,X2,esk4_0),X1)
    | ~ v1_relat_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_10]),c_0_11]),c_0_12])])).

cnf(c_0_16,plain,
    ( X1 = k1_funct_1(X2,X3)
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_17,plain,
    ( r2_hidden(k4_tarski(esk1_3(X1,X2,X3),esk2_3(X1,X2,X3)),X2)
    | r2_hidden(k4_tarski(esk1_3(X1,X2,X3),esk2_3(X1,X2,X3)),X3)
    | X3 = k8_relat_1(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_18,negated_conjecture,
    ( k8_relat_1(esk3_0,esk5_0) = esk4_0
    | esk4_0 = k8_relat_1(X1,X2)
    | r2_hidden(k1_funct_1(esk4_0,esk1_3(X1,X2,esk4_0)),esk3_0)
    | r2_hidden(esk2_3(X1,X2,esk4_0),X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_19,plain,
    ( k1_funct_1(X1,esk1_3(X2,X3,X1)) = esk2_3(X2,X3,X1)
    | X1 = k8_relat_1(X2,X3)
    | r2_hidden(esk2_3(X2,X3,X1),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X3) ),
    inference(spm,[status(thm)],[c_0_16,c_0_8])).

cnf(c_0_20,negated_conjecture,
    ( esk4_0 = k8_relat_1(X1,X2)
    | r2_hidden(k4_tarski(esk1_3(X1,X2,esk4_0),esk2_3(X1,X2,esk4_0)),esk4_0)
    | r2_hidden(k4_tarski(esk1_3(X1,X2,esk4_0),esk2_3(X1,X2,esk4_0)),X2)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_17,c_0_12])).

cnf(c_0_21,negated_conjecture,
    ( k8_relat_1(esk3_0,esk5_0) = esk4_0
    | esk4_0 = k8_relat_1(X1,X2)
    | r2_hidden(esk2_3(X1,X2,esk4_0),esk3_0)
    | r2_hidden(esk2_3(X1,X2,esk4_0),X1)
    | ~ v1_relat_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_11]),c_0_12])])).

cnf(c_0_22,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_23,plain,
    ( X3 = k8_relat_1(X1,X2)
    | ~ r2_hidden(k4_tarski(esk1_3(X1,X2,X3),esk2_3(X1,X2,X3)),X3)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X1)
    | ~ r2_hidden(k4_tarski(esk1_3(X1,X2,X3),esk2_3(X1,X2,X3)),X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_24,negated_conjecture,
    ( k8_relat_1(X1,esk4_0) = esk4_0
    | r2_hidden(k4_tarski(esk1_3(X1,esk4_0,esk4_0),esk2_3(X1,esk4_0,esk4_0)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_12])).

cnf(c_0_25,negated_conjecture,
    ( k8_relat_1(esk3_0,esk5_0) = esk4_0
    | k8_relat_1(X1,esk4_0) = esk4_0
    | r2_hidden(esk2_3(X1,esk4_0,esk4_0),esk3_0)
    | r2_hidden(esk2_3(X1,esk4_0,esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_12])).

cnf(c_0_26,negated_conjecture,
    ( k8_relat_1(X1,esk5_0) = esk4_0
    | r2_hidden(k4_tarski(esk1_3(X1,esk5_0,esk4_0),esk2_3(X1,esk5_0,esk4_0)),esk5_0)
    | r2_hidden(k4_tarski(esk1_3(X1,esk5_0,esk4_0),esk2_3(X1,esk5_0,esk4_0)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),X4)
    | X4 != k8_relat_1(X2,X5)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X5) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_29,negated_conjecture,
    ( k8_relat_1(X1,esk4_0) = esk4_0
    | ~ r2_hidden(esk2_3(X1,esk4_0,esk4_0),X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_12])]),c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( k8_relat_1(esk3_0,esk4_0) = esk4_0
    | k8_relat_1(esk3_0,esk5_0) = esk4_0
    | r2_hidden(esk2_3(esk3_0,esk4_0,esk4_0),esk3_0) ),
    inference(ef,[status(thm)],[c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( k1_funct_1(esk5_0,esk1_3(X1,esk5_0,esk4_0)) = esk2_3(X1,esk5_0,esk4_0)
    | k8_relat_1(X1,esk5_0) = esk4_0
    | r2_hidden(k4_tarski(esk1_3(X1,esk5_0,esk4_0),esk2_3(X1,esk5_0,esk4_0)),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_26]),c_0_27]),c_0_22])])).

cnf(c_0_32,negated_conjecture,
    ( k8_relat_1(X1,esk5_0) = esk4_0
    | r2_hidden(k4_tarski(esk1_3(X1,esk5_0,esk4_0),esk2_3(X1,esk5_0,esk4_0)),esk4_0)
    | r2_hidden(esk1_3(X1,esk5_0,esk4_0),k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_26]),c_0_27]),c_0_22])])).

cnf(c_0_33,negated_conjecture,
    ( k8_relat_1(X1,esk4_0) = esk4_0
    | r2_hidden(esk2_3(X1,esk4_0,esk4_0),X2)
    | esk4_0 != k8_relat_1(X2,X3)
    | ~ v1_relat_1(X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_24]),c_0_12])])).

cnf(c_0_34,negated_conjecture,
    ( k8_relat_1(esk3_0,esk5_0) = esk4_0
    | k8_relat_1(esk3_0,esk4_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(X1,k1_relat_1(esk4_0))
    | esk4_0 = k8_relat_1(esk3_0,esk5_0)
    | ~ r2_hidden(X1,k1_relat_1(esk5_0))
    | ~ r2_hidden(k1_funct_1(esk5_0,X1),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_36,negated_conjecture,
    ( k1_funct_1(esk5_0,esk1_3(X1,esk5_0,esk4_0)) = esk2_3(X1,esk5_0,esk4_0)
    | k8_relat_1(X1,esk5_0) = esk4_0
    | r2_hidden(esk1_3(X1,esk5_0,esk4_0),k1_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_31]),c_0_11]),c_0_12])])).

cnf(c_0_37,negated_conjecture,
    ( k8_relat_1(X1,esk5_0) = esk4_0
    | r2_hidden(esk1_3(X1,esk5_0,esk4_0),k1_relat_1(esk5_0))
    | r2_hidden(esk1_3(X1,esk5_0,esk4_0),k1_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_32]),c_0_11]),c_0_12])])).

cnf(c_0_38,negated_conjecture,
    ( k8_relat_1(esk3_0,esk4_0) = esk4_0
    | k8_relat_1(X1,esk4_0) = esk4_0
    | r2_hidden(esk2_3(X1,esk4_0,esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_22])])).

cnf(c_0_39,plain,
    ( r2_hidden(k4_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_40,negated_conjecture,
    ( k8_relat_1(esk3_0,esk5_0) = esk4_0
    | k8_relat_1(X1,esk5_0) = esk4_0
    | r2_hidden(esk1_3(X1,esk5_0,esk4_0),k1_relat_1(esk4_0))
    | ~ r2_hidden(esk2_3(X1,esk5_0,esk4_0),esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37])).

cnf(c_0_41,negated_conjecture,
    ( k8_relat_1(X1,esk5_0) = esk4_0
    | r2_hidden(esk1_3(X1,esk5_0,esk4_0),k1_relat_1(esk5_0))
    | r2_hidden(esk2_3(X1,esk5_0,esk4_0),X2)
    | esk4_0 != k8_relat_1(X2,X3)
    | ~ v1_relat_1(X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_32]),c_0_12])])).

cnf(c_0_42,negated_conjecture,
    ( k8_relat_1(esk3_0,esk4_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_29,c_0_38])).

cnf(c_0_43,plain,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)
    | ~ v1_funct_1(X2)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X2) ),
    inference(er,[status(thm)],[c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( k1_funct_1(esk5_0,esk1_3(X1,esk5_0,esk4_0)) = esk2_3(X1,esk5_0,esk4_0)
    | k1_funct_1(esk4_0,esk1_3(X1,esk5_0,esk4_0)) = esk2_3(X1,esk5_0,esk4_0)
    | k8_relat_1(X1,esk5_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_31]),c_0_11]),c_0_12])])).

cnf(c_0_45,negated_conjecture,
    ( k1_funct_1(esk5_0,esk1_3(X1,esk5_0,esk4_0)) = k1_funct_1(esk4_0,esk1_3(X1,esk5_0,esk4_0))
    | k8_relat_1(esk3_0,esk5_0) = esk4_0
    | k8_relat_1(X1,esk5_0) = esk4_0
    | ~ r2_hidden(esk2_3(X1,esk5_0,esk4_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_40])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(X1,k1_relat_1(esk5_0))
    | esk4_0 = k8_relat_1(esk3_0,esk5_0)
    | ~ r2_hidden(X1,k1_relat_1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_47,negated_conjecture,
    ( k8_relat_1(X1,esk5_0) = esk4_0
    | r2_hidden(esk1_3(X1,esk5_0,esk4_0),k1_relat_1(esk5_0))
    | r2_hidden(esk2_3(X1,esk5_0,esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_12])])).

cnf(c_0_48,negated_conjecture,
    ( k1_funct_1(esk5_0,esk1_3(X1,esk5_0,esk4_0)) = esk2_3(X1,esk5_0,esk4_0)
    | k8_relat_1(X1,esk5_0) = esk4_0
    | r2_hidden(esk2_3(X1,esk5_0,esk4_0),X2)
    | esk4_0 != k8_relat_1(X2,X3)
    | ~ v1_relat_1(X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_31]),c_0_12])])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(esk4_0,X1)),esk4_0)
    | ~ r2_hidden(X1,k1_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_11]),c_0_12])])).

cnf(c_0_50,negated_conjecture,
    ( k1_funct_1(esk4_0,esk1_3(X1,esk5_0,esk4_0)) = esk2_3(X1,esk5_0,esk4_0)
    | k8_relat_1(esk3_0,esk5_0) = esk4_0
    | k8_relat_1(X1,esk5_0) = esk4_0
    | ~ r2_hidden(esk2_3(X1,esk5_0,esk4_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(esk5_0,X1)),esk5_0)
    | ~ r2_hidden(X1,k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_27]),c_0_22])])).

cnf(c_0_52,negated_conjecture,
    ( k8_relat_1(esk3_0,esk5_0) = esk4_0
    | k8_relat_1(X1,esk5_0) = esk4_0
    | r2_hidden(esk1_3(X1,esk5_0,esk4_0),k1_relat_1(esk5_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_40]),c_0_47])).

cnf(c_0_53,negated_conjecture,
    ( k1_funct_1(esk5_0,esk1_3(X1,esk5_0,esk4_0)) = esk2_3(X1,esk5_0,esk4_0)
    | k8_relat_1(X1,esk5_0) = esk4_0
    | r2_hidden(esk2_3(X1,esk5_0,esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_42]),c_0_12])])).

cnf(c_0_54,negated_conjecture,
    ( k8_relat_1(esk3_0,esk5_0) = esk4_0
    | k8_relat_1(X1,esk5_0) = esk4_0
    | r2_hidden(k4_tarski(esk1_3(X1,esk5_0,esk4_0),esk2_3(X1,esk5_0,esk4_0)),esk4_0)
    | ~ r2_hidden(esk2_3(X1,esk5_0,esk4_0),esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_40])).

cnf(c_0_55,negated_conjecture,
    ( k8_relat_1(esk3_0,esk5_0) = esk4_0
    | k8_relat_1(X1,esk5_0) = esk4_0
    | r2_hidden(k4_tarski(esk1_3(X1,esk5_0,esk4_0),k1_funct_1(esk4_0,esk1_3(X1,esk5_0,esk4_0))),esk5_0)
    | ~ r2_hidden(esk2_3(X1,esk5_0,esk4_0),esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_45]),c_0_52])).

cnf(c_0_56,negated_conjecture,
    ( k8_relat_1(X1,esk5_0) = esk4_0
    | r2_hidden(k4_tarski(esk1_3(X1,esk5_0,esk4_0),esk2_3(X1,esk5_0,esk4_0)),esk5_0)
    | r2_hidden(esk2_3(X1,esk5_0,esk4_0),esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_53]),c_0_47])).

cnf(c_0_57,negated_conjecture,
    ( k8_relat_1(esk3_0,esk5_0) = esk4_0
    | k8_relat_1(X1,esk5_0) = esk4_0
    | ~ r2_hidden(k4_tarski(esk1_3(X1,esk5_0,esk4_0),esk2_3(X1,esk5_0,esk4_0)),esk5_0)
    | ~ r2_hidden(esk2_3(X1,esk5_0,esk4_0),esk3_0)
    | ~ r2_hidden(esk2_3(X1,esk5_0,esk4_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_54]),c_0_12]),c_0_22])])).

cnf(c_0_58,negated_conjecture,
    ( k8_relat_1(esk3_0,esk5_0) = esk4_0
    | k8_relat_1(X1,esk5_0) = esk4_0
    | r2_hidden(k4_tarski(esk1_3(X1,esk5_0,esk4_0),esk2_3(X1,esk5_0,esk4_0)),esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_50]),c_0_56])).

cnf(c_0_59,negated_conjecture,
    ( k8_relat_1(esk3_0,esk5_0) = esk4_0
    | k8_relat_1(X1,esk5_0) = esk4_0
    | r2_hidden(esk2_3(X1,esk5_0,esk4_0),esk3_0)
    | r2_hidden(esk2_3(X1,esk5_0,esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_60,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(k4_tarski(X1,X2),X4)
    | X4 != k8_relat_1(X5,X3)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_61,negated_conjecture,
    ( k8_relat_1(esk3_0,esk5_0) = esk4_0
    | k8_relat_1(X1,esk5_0) = esk4_0
    | ~ r2_hidden(esk2_3(X1,esk5_0,esk4_0),esk3_0)
    | ~ r2_hidden(esk2_3(X1,esk5_0,esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_62,negated_conjecture,
    ( k8_relat_1(esk3_0,esk5_0) = esk4_0
    | r2_hidden(esk2_3(esk3_0,esk5_0,esk4_0),esk3_0) ),
    inference(ef,[status(thm)],[c_0_59])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(esk4_0,X1)),X2)
    | esk4_0 != k8_relat_1(X3,X2)
    | ~ r2_hidden(X1,k1_relat_1(esk4_0))
    | ~ v1_relat_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_49]),c_0_12])])).

cnf(c_0_64,negated_conjecture,
    ( k8_relat_1(esk3_0,esk5_0) = esk4_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_62])).

cnf(c_0_65,negated_conjecture,
    ( k1_funct_1(esk4_0,esk7_0) != k1_funct_1(esk5_0,esk7_0)
    | ~ r2_hidden(esk6_0,k1_relat_1(esk4_0))
    | ~ r2_hidden(esk6_0,k1_relat_1(esk5_0))
    | ~ r2_hidden(k1_funct_1(esk5_0,esk6_0),esk3_0)
    | esk4_0 != k8_relat_1(esk3_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(esk4_0,X1)),esk5_0)
    | ~ r2_hidden(X1,k1_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_22])])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(esk7_0,k1_relat_1(esk4_0))
    | ~ r2_hidden(esk6_0,k1_relat_1(esk4_0))
    | ~ r2_hidden(esk6_0,k1_relat_1(esk5_0))
    | ~ r2_hidden(k1_funct_1(esk5_0,esk6_0),esk3_0)
    | esk4_0 != k8_relat_1(esk3_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_68,negated_conjecture,
    ( k1_funct_1(esk5_0,esk7_0) != k1_funct_1(esk4_0,esk7_0)
    | ~ r2_hidden(k1_funct_1(esk5_0,esk6_0),esk3_0)
    | ~ r2_hidden(esk6_0,k1_relat_1(esk4_0))
    | ~ r2_hidden(esk6_0,k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_64])])).

cnf(c_0_69,negated_conjecture,
    ( k1_funct_1(esk5_0,X1) = k1_funct_1(esk4_0,X1)
    | ~ r2_hidden(X1,k1_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_66]),c_0_27]),c_0_22])])).

cnf(c_0_70,negated_conjecture,
    ( r2_hidden(esk7_0,k1_relat_1(esk4_0))
    | ~ r2_hidden(k1_funct_1(esk5_0,esk6_0),esk3_0)
    | ~ r2_hidden(esk6_0,k1_relat_1(esk4_0))
    | ~ r2_hidden(esk6_0,k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_64])])).

cnf(c_0_71,negated_conjecture,
    ( r2_hidden(X1,k1_relat_1(esk5_0))
    | ~ r2_hidden(X1,k1_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_66]),c_0_27]),c_0_22])])).

cnf(c_0_72,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk4_0,X1),X2)
    | esk4_0 != k8_relat_1(X2,X3)
    | ~ r2_hidden(X1,k1_relat_1(esk4_0))
    | ~ v1_relat_1(X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_49]),c_0_12])])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(esk7_0,k1_relat_1(esk4_0))
    | r2_hidden(k1_funct_1(esk5_0,esk6_0),esk3_0)
    | r2_hidden(esk6_0,k1_relat_1(esk4_0))
    | esk4_0 != k8_relat_1(esk3_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_74,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(esk5_0,esk6_0),esk3_0)
    | ~ r2_hidden(esk6_0,k1_relat_1(esk4_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_70]),c_0_71])).

cnf(c_0_75,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk4_0,X1),esk3_0)
    | ~ r2_hidden(X1,k1_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_42]),c_0_12])])).

cnf(c_0_76,negated_conjecture,
    ( r2_hidden(esk7_0,k1_relat_1(esk4_0))
    | r2_hidden(esk6_0,k1_relat_1(esk5_0))
    | r2_hidden(esk6_0,k1_relat_1(esk4_0))
    | esk4_0 != k8_relat_1(esk3_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_77,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk5_0,esk6_0),esk3_0)
    | r2_hidden(esk6_0,k1_relat_1(esk4_0))
    | k1_funct_1(esk4_0,esk7_0) != k1_funct_1(esk5_0,esk7_0)
    | esk4_0 != k8_relat_1(esk3_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_78,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk5_0,esk6_0),esk3_0)
    | r2_hidden(esk7_0,k1_relat_1(esk4_0))
    | r2_hidden(esk6_0,k1_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_64])])).

cnf(c_0_79,negated_conjecture,
    ( ~ r2_hidden(esk6_0,k1_relat_1(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_69]),c_0_75])).

cnf(c_0_80,negated_conjecture,
    ( r2_hidden(esk6_0,k1_relat_1(esk5_0))
    | r2_hidden(esk6_0,k1_relat_1(esk4_0))
    | k1_funct_1(esk4_0,esk7_0) != k1_funct_1(esk5_0,esk7_0)
    | esk4_0 != k8_relat_1(esk3_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_81,negated_conjecture,
    ( r2_hidden(esk7_0,k1_relat_1(esk4_0))
    | r2_hidden(esk6_0,k1_relat_1(esk5_0))
    | r2_hidden(esk6_0,k1_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_64])])).

cnf(c_0_82,plain,
    ( r2_hidden(k4_tarski(X3,X1),X5)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),X4)
    | X5 != k8_relat_1(X2,X4)
    | ~ v1_relat_1(X5)
    | ~ v1_relat_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_83,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk5_0,esk6_0),esk3_0)
    | r2_hidden(esk6_0,k1_relat_1(esk4_0))
    | k1_funct_1(esk5_0,esk7_0) != k1_funct_1(esk4_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_77,c_0_64])])).

cnf(c_0_84,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk5_0,esk6_0),esk3_0)
    | r2_hidden(esk7_0,k1_relat_1(esk4_0)) ),
    inference(sr,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_85,negated_conjecture,
    ( r2_hidden(esk6_0,k1_relat_1(esk5_0))
    | r2_hidden(esk6_0,k1_relat_1(esk4_0))
    | k1_funct_1(esk5_0,esk7_0) != k1_funct_1(esk4_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_64])])).

cnf(c_0_86,negated_conjecture,
    ( r2_hidden(esk6_0,k1_relat_1(esk5_0))
    | r2_hidden(esk7_0,k1_relat_1(esk4_0)) ),
    inference(sr,[status(thm)],[c_0_81,c_0_79])).

cnf(c_0_87,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(esk5_0,X1)),X2)
    | X2 != k8_relat_1(X3,esk5_0)
    | ~ r2_hidden(k1_funct_1(esk5_0,X1),X3)
    | ~ r2_hidden(X1,k1_relat_1(esk5_0))
    | ~ v1_relat_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_51]),c_0_22])])).

cnf(c_0_88,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk5_0,esk6_0),esk3_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_69]),c_0_79]),c_0_84])).

cnf(c_0_89,negated_conjecture,
    ( r2_hidden(esk6_0,k1_relat_1(esk5_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_69]),c_0_79]),c_0_86])).

cnf(c_0_90,negated_conjecture,
    ( r2_hidden(k4_tarski(esk6_0,k1_funct_1(esk5_0,esk6_0)),X1)
    | X1 != esk4_0
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_64]),c_0_89])])).

cnf(c_0_91,negated_conjecture,
    ( r2_hidden(k4_tarski(esk6_0,k1_funct_1(esk5_0,esk6_0)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_90,c_0_12])).

cnf(c_0_92,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_91]),c_0_11]),c_0_12])]),c_0_79]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:22:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.50  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 0.19/0.50  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.50  #
% 0.19/0.50  # Preprocessing time       : 0.028 s
% 0.19/0.50  # Presaturation interreduction done
% 0.19/0.50  
% 0.19/0.50  # Proof found!
% 0.19/0.50  # SZS status Theorem
% 0.19/0.50  # SZS output start CNFRefutation
% 0.19/0.50  fof(t85_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(X2=k8_relat_1(X1,X3)<=>(![X4]:(r2_hidden(X4,k1_relat_1(X2))<=>(r2_hidden(X4,k1_relat_1(X3))&r2_hidden(k1_funct_1(X3,X4),X1)))&![X4]:(r2_hidden(X4,k1_relat_1(X2))=>k1_funct_1(X2,X4)=k1_funct_1(X3,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_funct_1)).
% 0.19/0.50  fof(t8_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>(r2_hidden(X1,k1_relat_1(X3))&X2=k1_funct_1(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 0.19/0.50  fof(d12_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(X3=k8_relat_1(X1,X2)<=>![X4, X5]:(r2_hidden(k4_tarski(X4,X5),X3)<=>(r2_hidden(X5,X1)&r2_hidden(k4_tarski(X4,X5),X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_relat_1)).
% 0.19/0.50  fof(c_0_3, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(X2=k8_relat_1(X1,X3)<=>(![X4]:(r2_hidden(X4,k1_relat_1(X2))<=>(r2_hidden(X4,k1_relat_1(X3))&r2_hidden(k1_funct_1(X3,X4),X1)))&![X4]:(r2_hidden(X4,k1_relat_1(X2))=>k1_funct_1(X2,X4)=k1_funct_1(X3,X4))))))), inference(assume_negation,[status(cth)],[t85_funct_1])).
% 0.19/0.50  fof(c_0_4, plain, ![X15, X16, X17]:(((r2_hidden(X15,k1_relat_1(X17))|~r2_hidden(k4_tarski(X15,X16),X17)|(~v1_relat_1(X17)|~v1_funct_1(X17)))&(X16=k1_funct_1(X17,X15)|~r2_hidden(k4_tarski(X15,X16),X17)|(~v1_relat_1(X17)|~v1_funct_1(X17))))&(~r2_hidden(X15,k1_relat_1(X17))|X16!=k1_funct_1(X17,X15)|r2_hidden(k4_tarski(X15,X16),X17)|(~v1_relat_1(X17)|~v1_funct_1(X17)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).
% 0.19/0.50  fof(c_0_5, plain, ![X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X10,X6)|~r2_hidden(k4_tarski(X9,X10),X8)|X8!=k8_relat_1(X6,X7)|~v1_relat_1(X8)|~v1_relat_1(X7))&(r2_hidden(k4_tarski(X9,X10),X7)|~r2_hidden(k4_tarski(X9,X10),X8)|X8!=k8_relat_1(X6,X7)|~v1_relat_1(X8)|~v1_relat_1(X7)))&(~r2_hidden(X12,X6)|~r2_hidden(k4_tarski(X11,X12),X7)|r2_hidden(k4_tarski(X11,X12),X8)|X8!=k8_relat_1(X6,X7)|~v1_relat_1(X8)|~v1_relat_1(X7)))&((~r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X8)|(~r2_hidden(esk2_3(X6,X7,X8),X6)|~r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X7))|X8=k8_relat_1(X6,X7)|~v1_relat_1(X8)|~v1_relat_1(X7))&((r2_hidden(esk2_3(X6,X7,X8),X6)|r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X8)|X8=k8_relat_1(X6,X7)|~v1_relat_1(X8)|~v1_relat_1(X7))&(r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X7)|r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X8)|X8=k8_relat_1(X6,X7)|~v1_relat_1(X8)|~v1_relat_1(X7))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_relat_1])])])])])])).
% 0.19/0.50  fof(c_0_6, negated_conjecture, ![X23, X24]:((v1_relat_1(esk4_0)&v1_funct_1(esk4_0))&((v1_relat_1(esk5_0)&v1_funct_1(esk5_0))&((((r2_hidden(esk7_0,k1_relat_1(esk4_0))|(~r2_hidden(esk6_0,k1_relat_1(esk4_0))|(~r2_hidden(esk6_0,k1_relat_1(esk5_0))|~r2_hidden(k1_funct_1(esk5_0,esk6_0),esk3_0)))|esk4_0!=k8_relat_1(esk3_0,esk5_0))&(k1_funct_1(esk4_0,esk7_0)!=k1_funct_1(esk5_0,esk7_0)|(~r2_hidden(esk6_0,k1_relat_1(esk4_0))|(~r2_hidden(esk6_0,k1_relat_1(esk5_0))|~r2_hidden(k1_funct_1(esk5_0,esk6_0),esk3_0)))|esk4_0!=k8_relat_1(esk3_0,esk5_0)))&(((r2_hidden(esk7_0,k1_relat_1(esk4_0))|(r2_hidden(esk6_0,k1_relat_1(esk5_0))|r2_hidden(esk6_0,k1_relat_1(esk4_0)))|esk4_0!=k8_relat_1(esk3_0,esk5_0))&(k1_funct_1(esk4_0,esk7_0)!=k1_funct_1(esk5_0,esk7_0)|(r2_hidden(esk6_0,k1_relat_1(esk5_0))|r2_hidden(esk6_0,k1_relat_1(esk4_0)))|esk4_0!=k8_relat_1(esk3_0,esk5_0)))&((r2_hidden(esk7_0,k1_relat_1(esk4_0))|(r2_hidden(k1_funct_1(esk5_0,esk6_0),esk3_0)|r2_hidden(esk6_0,k1_relat_1(esk4_0)))|esk4_0!=k8_relat_1(esk3_0,esk5_0))&(k1_funct_1(esk4_0,esk7_0)!=k1_funct_1(esk5_0,esk7_0)|(r2_hidden(k1_funct_1(esk5_0,esk6_0),esk3_0)|r2_hidden(esk6_0,k1_relat_1(esk4_0)))|esk4_0!=k8_relat_1(esk3_0,esk5_0)))))&((((r2_hidden(X23,k1_relat_1(esk5_0))|~r2_hidden(X23,k1_relat_1(esk4_0))|esk4_0=k8_relat_1(esk3_0,esk5_0))&(r2_hidden(k1_funct_1(esk5_0,X23),esk3_0)|~r2_hidden(X23,k1_relat_1(esk4_0))|esk4_0=k8_relat_1(esk3_0,esk5_0)))&(~r2_hidden(X23,k1_relat_1(esk5_0))|~r2_hidden(k1_funct_1(esk5_0,X23),esk3_0)|r2_hidden(X23,k1_relat_1(esk4_0))|esk4_0=k8_relat_1(esk3_0,esk5_0)))&(~r2_hidden(X24,k1_relat_1(esk4_0))|k1_funct_1(esk4_0,X24)=k1_funct_1(esk5_0,X24)|esk4_0=k8_relat_1(esk3_0,esk5_0)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])])])).
% 0.19/0.50  cnf(c_0_7, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.19/0.50  cnf(c_0_8, plain, (r2_hidden(esk2_3(X1,X2,X3),X1)|r2_hidden(k4_tarski(esk1_3(X1,X2,X3),esk2_3(X1,X2,X3)),X3)|X3=k8_relat_1(X1,X2)|~v1_relat_1(X3)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.50  cnf(c_0_9, negated_conjecture, (r2_hidden(k1_funct_1(esk5_0,X1),esk3_0)|esk4_0=k8_relat_1(esk3_0,esk5_0)|~r2_hidden(X1,k1_relat_1(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.50  cnf(c_0_10, plain, (X1=k8_relat_1(X2,X3)|r2_hidden(esk1_3(X2,X3,X1),k1_relat_1(X1))|r2_hidden(esk2_3(X2,X3,X1),X2)|~v1_funct_1(X1)|~v1_relat_1(X1)|~v1_relat_1(X3)), inference(spm,[status(thm)],[c_0_7, c_0_8])).
% 0.19/0.50  cnf(c_0_11, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.50  cnf(c_0_12, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.50  cnf(c_0_13, negated_conjecture, (k1_funct_1(esk4_0,X1)=k1_funct_1(esk5_0,X1)|esk4_0=k8_relat_1(esk3_0,esk5_0)|~r2_hidden(X1,k1_relat_1(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.50  cnf(c_0_14, negated_conjecture, (k8_relat_1(esk3_0,esk5_0)=esk4_0|esk4_0=k8_relat_1(X1,X2)|r2_hidden(k1_funct_1(esk5_0,esk1_3(X1,X2,esk4_0)),esk3_0)|r2_hidden(esk2_3(X1,X2,esk4_0),X1)|~v1_relat_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9, c_0_10]), c_0_11]), c_0_12])])).
% 0.19/0.50  cnf(c_0_15, negated_conjecture, (k1_funct_1(esk5_0,esk1_3(X1,X2,esk4_0))=k1_funct_1(esk4_0,esk1_3(X1,X2,esk4_0))|k8_relat_1(esk3_0,esk5_0)=esk4_0|esk4_0=k8_relat_1(X1,X2)|r2_hidden(esk2_3(X1,X2,esk4_0),X1)|~v1_relat_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_10]), c_0_11]), c_0_12])])).
% 0.19/0.50  cnf(c_0_16, plain, (X1=k1_funct_1(X2,X3)|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.19/0.50  cnf(c_0_17, plain, (r2_hidden(k4_tarski(esk1_3(X1,X2,X3),esk2_3(X1,X2,X3)),X2)|r2_hidden(k4_tarski(esk1_3(X1,X2,X3),esk2_3(X1,X2,X3)),X3)|X3=k8_relat_1(X1,X2)|~v1_relat_1(X3)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.50  cnf(c_0_18, negated_conjecture, (k8_relat_1(esk3_0,esk5_0)=esk4_0|esk4_0=k8_relat_1(X1,X2)|r2_hidden(k1_funct_1(esk4_0,esk1_3(X1,X2,esk4_0)),esk3_0)|r2_hidden(esk2_3(X1,X2,esk4_0),X1)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.19/0.50  cnf(c_0_19, plain, (k1_funct_1(X1,esk1_3(X2,X3,X1))=esk2_3(X2,X3,X1)|X1=k8_relat_1(X2,X3)|r2_hidden(esk2_3(X2,X3,X1),X2)|~v1_funct_1(X1)|~v1_relat_1(X1)|~v1_relat_1(X3)), inference(spm,[status(thm)],[c_0_16, c_0_8])).
% 0.19/0.50  cnf(c_0_20, negated_conjecture, (esk4_0=k8_relat_1(X1,X2)|r2_hidden(k4_tarski(esk1_3(X1,X2,esk4_0),esk2_3(X1,X2,esk4_0)),esk4_0)|r2_hidden(k4_tarski(esk1_3(X1,X2,esk4_0),esk2_3(X1,X2,esk4_0)),X2)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_17, c_0_12])).
% 0.19/0.50  cnf(c_0_21, negated_conjecture, (k8_relat_1(esk3_0,esk5_0)=esk4_0|esk4_0=k8_relat_1(X1,X2)|r2_hidden(esk2_3(X1,X2,esk4_0),esk3_0)|r2_hidden(esk2_3(X1,X2,esk4_0),X1)|~v1_relat_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_11]), c_0_12])])).
% 0.19/0.50  cnf(c_0_22, negated_conjecture, (v1_relat_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.50  cnf(c_0_23, plain, (X3=k8_relat_1(X1,X2)|~r2_hidden(k4_tarski(esk1_3(X1,X2,X3),esk2_3(X1,X2,X3)),X3)|~r2_hidden(esk2_3(X1,X2,X3),X1)|~r2_hidden(k4_tarski(esk1_3(X1,X2,X3),esk2_3(X1,X2,X3)),X2)|~v1_relat_1(X3)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.50  cnf(c_0_24, negated_conjecture, (k8_relat_1(X1,esk4_0)=esk4_0|r2_hidden(k4_tarski(esk1_3(X1,esk4_0,esk4_0),esk2_3(X1,esk4_0,esk4_0)),esk4_0)), inference(spm,[status(thm)],[c_0_20, c_0_12])).
% 0.19/0.50  cnf(c_0_25, negated_conjecture, (k8_relat_1(esk3_0,esk5_0)=esk4_0|k8_relat_1(X1,esk4_0)=esk4_0|r2_hidden(esk2_3(X1,esk4_0,esk4_0),esk3_0)|r2_hidden(esk2_3(X1,esk4_0,esk4_0),X1)), inference(spm,[status(thm)],[c_0_21, c_0_12])).
% 0.19/0.50  cnf(c_0_26, negated_conjecture, (k8_relat_1(X1,esk5_0)=esk4_0|r2_hidden(k4_tarski(esk1_3(X1,esk5_0,esk4_0),esk2_3(X1,esk5_0,esk4_0)),esk5_0)|r2_hidden(k4_tarski(esk1_3(X1,esk5_0,esk4_0),esk2_3(X1,esk5_0,esk4_0)),esk4_0)), inference(spm,[status(thm)],[c_0_20, c_0_22])).
% 0.19/0.50  cnf(c_0_27, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.50  cnf(c_0_28, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X3,X1),X4)|X4!=k8_relat_1(X2,X5)|~v1_relat_1(X4)|~v1_relat_1(X5)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.50  cnf(c_0_29, negated_conjecture, (k8_relat_1(X1,esk4_0)=esk4_0|~r2_hidden(esk2_3(X1,esk4_0,esk4_0),X1)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_12])]), c_0_24])).
% 0.19/0.50  cnf(c_0_30, negated_conjecture, (k8_relat_1(esk3_0,esk4_0)=esk4_0|k8_relat_1(esk3_0,esk5_0)=esk4_0|r2_hidden(esk2_3(esk3_0,esk4_0,esk4_0),esk3_0)), inference(ef,[status(thm)],[c_0_25])).
% 0.19/0.50  cnf(c_0_31, negated_conjecture, (k1_funct_1(esk5_0,esk1_3(X1,esk5_0,esk4_0))=esk2_3(X1,esk5_0,esk4_0)|k8_relat_1(X1,esk5_0)=esk4_0|r2_hidden(k4_tarski(esk1_3(X1,esk5_0,esk4_0),esk2_3(X1,esk5_0,esk4_0)),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_26]), c_0_27]), c_0_22])])).
% 0.19/0.50  cnf(c_0_32, negated_conjecture, (k8_relat_1(X1,esk5_0)=esk4_0|r2_hidden(k4_tarski(esk1_3(X1,esk5_0,esk4_0),esk2_3(X1,esk5_0,esk4_0)),esk4_0)|r2_hidden(esk1_3(X1,esk5_0,esk4_0),k1_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7, c_0_26]), c_0_27]), c_0_22])])).
% 0.19/0.50  cnf(c_0_33, negated_conjecture, (k8_relat_1(X1,esk4_0)=esk4_0|r2_hidden(esk2_3(X1,esk4_0,esk4_0),X2)|esk4_0!=k8_relat_1(X2,X3)|~v1_relat_1(X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_24]), c_0_12])])).
% 0.19/0.50  cnf(c_0_34, negated_conjecture, (k8_relat_1(esk3_0,esk5_0)=esk4_0|k8_relat_1(esk3_0,esk4_0)=esk4_0), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.19/0.50  cnf(c_0_35, negated_conjecture, (r2_hidden(X1,k1_relat_1(esk4_0))|esk4_0=k8_relat_1(esk3_0,esk5_0)|~r2_hidden(X1,k1_relat_1(esk5_0))|~r2_hidden(k1_funct_1(esk5_0,X1),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.50  cnf(c_0_36, negated_conjecture, (k1_funct_1(esk5_0,esk1_3(X1,esk5_0,esk4_0))=esk2_3(X1,esk5_0,esk4_0)|k8_relat_1(X1,esk5_0)=esk4_0|r2_hidden(esk1_3(X1,esk5_0,esk4_0),k1_relat_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7, c_0_31]), c_0_11]), c_0_12])])).
% 0.19/0.50  cnf(c_0_37, negated_conjecture, (k8_relat_1(X1,esk5_0)=esk4_0|r2_hidden(esk1_3(X1,esk5_0,esk4_0),k1_relat_1(esk5_0))|r2_hidden(esk1_3(X1,esk5_0,esk4_0),k1_relat_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7, c_0_32]), c_0_11]), c_0_12])])).
% 0.19/0.50  cnf(c_0_38, negated_conjecture, (k8_relat_1(esk3_0,esk4_0)=esk4_0|k8_relat_1(X1,esk4_0)=esk4_0|r2_hidden(esk2_3(X1,esk4_0,esk4_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_22])])).
% 0.19/0.50  cnf(c_0_39, plain, (r2_hidden(k4_tarski(X1,X3),X2)|~r2_hidden(X1,k1_relat_1(X2))|X3!=k1_funct_1(X2,X1)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.19/0.50  cnf(c_0_40, negated_conjecture, (k8_relat_1(esk3_0,esk5_0)=esk4_0|k8_relat_1(X1,esk5_0)=esk4_0|r2_hidden(esk1_3(X1,esk5_0,esk4_0),k1_relat_1(esk4_0))|~r2_hidden(esk2_3(X1,esk5_0,esk4_0),esk3_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37])).
% 0.19/0.50  cnf(c_0_41, negated_conjecture, (k8_relat_1(X1,esk5_0)=esk4_0|r2_hidden(esk1_3(X1,esk5_0,esk4_0),k1_relat_1(esk5_0))|r2_hidden(esk2_3(X1,esk5_0,esk4_0),X2)|esk4_0!=k8_relat_1(X2,X3)|~v1_relat_1(X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_32]), c_0_12])])).
% 0.19/0.50  cnf(c_0_42, negated_conjecture, (k8_relat_1(esk3_0,esk4_0)=esk4_0), inference(spm,[status(thm)],[c_0_29, c_0_38])).
% 0.19/0.50  cnf(c_0_43, plain, (r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)|~v1_funct_1(X2)|~r2_hidden(X1,k1_relat_1(X2))|~v1_relat_1(X2)), inference(er,[status(thm)],[c_0_39])).
% 0.19/0.50  cnf(c_0_44, negated_conjecture, (k1_funct_1(esk5_0,esk1_3(X1,esk5_0,esk4_0))=esk2_3(X1,esk5_0,esk4_0)|k1_funct_1(esk4_0,esk1_3(X1,esk5_0,esk4_0))=esk2_3(X1,esk5_0,esk4_0)|k8_relat_1(X1,esk5_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_31]), c_0_11]), c_0_12])])).
% 0.19/0.50  cnf(c_0_45, negated_conjecture, (k1_funct_1(esk5_0,esk1_3(X1,esk5_0,esk4_0))=k1_funct_1(esk4_0,esk1_3(X1,esk5_0,esk4_0))|k8_relat_1(esk3_0,esk5_0)=esk4_0|k8_relat_1(X1,esk5_0)=esk4_0|~r2_hidden(esk2_3(X1,esk5_0,esk4_0),esk3_0)), inference(spm,[status(thm)],[c_0_13, c_0_40])).
% 0.19/0.50  cnf(c_0_46, negated_conjecture, (r2_hidden(X1,k1_relat_1(esk5_0))|esk4_0=k8_relat_1(esk3_0,esk5_0)|~r2_hidden(X1,k1_relat_1(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.50  cnf(c_0_47, negated_conjecture, (k8_relat_1(X1,esk5_0)=esk4_0|r2_hidden(esk1_3(X1,esk5_0,esk4_0),k1_relat_1(esk5_0))|r2_hidden(esk2_3(X1,esk5_0,esk4_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_12])])).
% 0.19/0.50  cnf(c_0_48, negated_conjecture, (k1_funct_1(esk5_0,esk1_3(X1,esk5_0,esk4_0))=esk2_3(X1,esk5_0,esk4_0)|k8_relat_1(X1,esk5_0)=esk4_0|r2_hidden(esk2_3(X1,esk5_0,esk4_0),X2)|esk4_0!=k8_relat_1(X2,X3)|~v1_relat_1(X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_31]), c_0_12])])).
% 0.19/0.50  cnf(c_0_49, negated_conjecture, (r2_hidden(k4_tarski(X1,k1_funct_1(esk4_0,X1)),esk4_0)|~r2_hidden(X1,k1_relat_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_11]), c_0_12])])).
% 0.19/0.50  cnf(c_0_50, negated_conjecture, (k1_funct_1(esk4_0,esk1_3(X1,esk5_0,esk4_0))=esk2_3(X1,esk5_0,esk4_0)|k8_relat_1(esk3_0,esk5_0)=esk4_0|k8_relat_1(X1,esk5_0)=esk4_0|~r2_hidden(esk2_3(X1,esk5_0,esk4_0),esk3_0)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.19/0.50  cnf(c_0_51, negated_conjecture, (r2_hidden(k4_tarski(X1,k1_funct_1(esk5_0,X1)),esk5_0)|~r2_hidden(X1,k1_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_27]), c_0_22])])).
% 0.19/0.50  cnf(c_0_52, negated_conjecture, (k8_relat_1(esk3_0,esk5_0)=esk4_0|k8_relat_1(X1,esk5_0)=esk4_0|r2_hidden(esk1_3(X1,esk5_0,esk4_0),k1_relat_1(esk5_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_40]), c_0_47])).
% 0.19/0.50  cnf(c_0_53, negated_conjecture, (k1_funct_1(esk5_0,esk1_3(X1,esk5_0,esk4_0))=esk2_3(X1,esk5_0,esk4_0)|k8_relat_1(X1,esk5_0)=esk4_0|r2_hidden(esk2_3(X1,esk5_0,esk4_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_42]), c_0_12])])).
% 0.19/0.50  cnf(c_0_54, negated_conjecture, (k8_relat_1(esk3_0,esk5_0)=esk4_0|k8_relat_1(X1,esk5_0)=esk4_0|r2_hidden(k4_tarski(esk1_3(X1,esk5_0,esk4_0),esk2_3(X1,esk5_0,esk4_0)),esk4_0)|~r2_hidden(esk2_3(X1,esk5_0,esk4_0),esk3_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_40])).
% 0.19/0.50  cnf(c_0_55, negated_conjecture, (k8_relat_1(esk3_0,esk5_0)=esk4_0|k8_relat_1(X1,esk5_0)=esk4_0|r2_hidden(k4_tarski(esk1_3(X1,esk5_0,esk4_0),k1_funct_1(esk4_0,esk1_3(X1,esk5_0,esk4_0))),esk5_0)|~r2_hidden(esk2_3(X1,esk5_0,esk4_0),esk3_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_45]), c_0_52])).
% 0.19/0.50  cnf(c_0_56, negated_conjecture, (k8_relat_1(X1,esk5_0)=esk4_0|r2_hidden(k4_tarski(esk1_3(X1,esk5_0,esk4_0),esk2_3(X1,esk5_0,esk4_0)),esk5_0)|r2_hidden(esk2_3(X1,esk5_0,esk4_0),esk3_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_53]), c_0_47])).
% 0.19/0.50  cnf(c_0_57, negated_conjecture, (k8_relat_1(esk3_0,esk5_0)=esk4_0|k8_relat_1(X1,esk5_0)=esk4_0|~r2_hidden(k4_tarski(esk1_3(X1,esk5_0,esk4_0),esk2_3(X1,esk5_0,esk4_0)),esk5_0)|~r2_hidden(esk2_3(X1,esk5_0,esk4_0),esk3_0)|~r2_hidden(esk2_3(X1,esk5_0,esk4_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_54]), c_0_12]), c_0_22])])).
% 0.19/0.50  cnf(c_0_58, negated_conjecture, (k8_relat_1(esk3_0,esk5_0)=esk4_0|k8_relat_1(X1,esk5_0)=esk4_0|r2_hidden(k4_tarski(esk1_3(X1,esk5_0,esk4_0),esk2_3(X1,esk5_0,esk4_0)),esk5_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_50]), c_0_56])).
% 0.19/0.50  cnf(c_0_59, negated_conjecture, (k8_relat_1(esk3_0,esk5_0)=esk4_0|k8_relat_1(X1,esk5_0)=esk4_0|r2_hidden(esk2_3(X1,esk5_0,esk4_0),esk3_0)|r2_hidden(esk2_3(X1,esk5_0,esk4_0),X1)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.19/0.50  cnf(c_0_60, plain, (r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(k4_tarski(X1,X2),X4)|X4!=k8_relat_1(X5,X3)|~v1_relat_1(X4)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.50  cnf(c_0_61, negated_conjecture, (k8_relat_1(esk3_0,esk5_0)=esk4_0|k8_relat_1(X1,esk5_0)=esk4_0|~r2_hidden(esk2_3(X1,esk5_0,esk4_0),esk3_0)|~r2_hidden(esk2_3(X1,esk5_0,esk4_0),X1)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.19/0.50  cnf(c_0_62, negated_conjecture, (k8_relat_1(esk3_0,esk5_0)=esk4_0|r2_hidden(esk2_3(esk3_0,esk5_0,esk4_0),esk3_0)), inference(ef,[status(thm)],[c_0_59])).
% 0.19/0.50  cnf(c_0_63, negated_conjecture, (r2_hidden(k4_tarski(X1,k1_funct_1(esk4_0,X1)),X2)|esk4_0!=k8_relat_1(X3,X2)|~r2_hidden(X1,k1_relat_1(esk4_0))|~v1_relat_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_49]), c_0_12])])).
% 0.19/0.50  cnf(c_0_64, negated_conjecture, (k8_relat_1(esk3_0,esk5_0)=esk4_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_62])).
% 0.19/0.50  cnf(c_0_65, negated_conjecture, (k1_funct_1(esk4_0,esk7_0)!=k1_funct_1(esk5_0,esk7_0)|~r2_hidden(esk6_0,k1_relat_1(esk4_0))|~r2_hidden(esk6_0,k1_relat_1(esk5_0))|~r2_hidden(k1_funct_1(esk5_0,esk6_0),esk3_0)|esk4_0!=k8_relat_1(esk3_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.50  cnf(c_0_66, negated_conjecture, (r2_hidden(k4_tarski(X1,k1_funct_1(esk4_0,X1)),esk5_0)|~r2_hidden(X1,k1_relat_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_22])])).
% 0.19/0.50  cnf(c_0_67, negated_conjecture, (r2_hidden(esk7_0,k1_relat_1(esk4_0))|~r2_hidden(esk6_0,k1_relat_1(esk4_0))|~r2_hidden(esk6_0,k1_relat_1(esk5_0))|~r2_hidden(k1_funct_1(esk5_0,esk6_0),esk3_0)|esk4_0!=k8_relat_1(esk3_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.50  cnf(c_0_68, negated_conjecture, (k1_funct_1(esk5_0,esk7_0)!=k1_funct_1(esk4_0,esk7_0)|~r2_hidden(k1_funct_1(esk5_0,esk6_0),esk3_0)|~r2_hidden(esk6_0,k1_relat_1(esk4_0))|~r2_hidden(esk6_0,k1_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_65, c_0_64])])).
% 0.19/0.50  cnf(c_0_69, negated_conjecture, (k1_funct_1(esk5_0,X1)=k1_funct_1(esk4_0,X1)|~r2_hidden(X1,k1_relat_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_66]), c_0_27]), c_0_22])])).
% 0.19/0.50  cnf(c_0_70, negated_conjecture, (r2_hidden(esk7_0,k1_relat_1(esk4_0))|~r2_hidden(k1_funct_1(esk5_0,esk6_0),esk3_0)|~r2_hidden(esk6_0,k1_relat_1(esk4_0))|~r2_hidden(esk6_0,k1_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_67, c_0_64])])).
% 0.19/0.50  cnf(c_0_71, negated_conjecture, (r2_hidden(X1,k1_relat_1(esk5_0))|~r2_hidden(X1,k1_relat_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7, c_0_66]), c_0_27]), c_0_22])])).
% 0.19/0.50  cnf(c_0_72, negated_conjecture, (r2_hidden(k1_funct_1(esk4_0,X1),X2)|esk4_0!=k8_relat_1(X2,X3)|~r2_hidden(X1,k1_relat_1(esk4_0))|~v1_relat_1(X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_49]), c_0_12])])).
% 0.19/0.50  cnf(c_0_73, negated_conjecture, (r2_hidden(esk7_0,k1_relat_1(esk4_0))|r2_hidden(k1_funct_1(esk5_0,esk6_0),esk3_0)|r2_hidden(esk6_0,k1_relat_1(esk4_0))|esk4_0!=k8_relat_1(esk3_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.50  cnf(c_0_74, negated_conjecture, (~r2_hidden(k1_funct_1(esk5_0,esk6_0),esk3_0)|~r2_hidden(esk6_0,k1_relat_1(esk4_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_70]), c_0_71])).
% 0.19/0.50  cnf(c_0_75, negated_conjecture, (r2_hidden(k1_funct_1(esk4_0,X1),esk3_0)|~r2_hidden(X1,k1_relat_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_42]), c_0_12])])).
% 0.19/0.50  cnf(c_0_76, negated_conjecture, (r2_hidden(esk7_0,k1_relat_1(esk4_0))|r2_hidden(esk6_0,k1_relat_1(esk5_0))|r2_hidden(esk6_0,k1_relat_1(esk4_0))|esk4_0!=k8_relat_1(esk3_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.50  cnf(c_0_77, negated_conjecture, (r2_hidden(k1_funct_1(esk5_0,esk6_0),esk3_0)|r2_hidden(esk6_0,k1_relat_1(esk4_0))|k1_funct_1(esk4_0,esk7_0)!=k1_funct_1(esk5_0,esk7_0)|esk4_0!=k8_relat_1(esk3_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.50  cnf(c_0_78, negated_conjecture, (r2_hidden(k1_funct_1(esk5_0,esk6_0),esk3_0)|r2_hidden(esk7_0,k1_relat_1(esk4_0))|r2_hidden(esk6_0,k1_relat_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_73, c_0_64])])).
% 0.19/0.50  cnf(c_0_79, negated_conjecture, (~r2_hidden(esk6_0,k1_relat_1(esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_69]), c_0_75])).
% 0.19/0.50  cnf(c_0_80, negated_conjecture, (r2_hidden(esk6_0,k1_relat_1(esk5_0))|r2_hidden(esk6_0,k1_relat_1(esk4_0))|k1_funct_1(esk4_0,esk7_0)!=k1_funct_1(esk5_0,esk7_0)|esk4_0!=k8_relat_1(esk3_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.50  cnf(c_0_81, negated_conjecture, (r2_hidden(esk7_0,k1_relat_1(esk4_0))|r2_hidden(esk6_0,k1_relat_1(esk5_0))|r2_hidden(esk6_0,k1_relat_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_76, c_0_64])])).
% 0.19/0.50  cnf(c_0_82, plain, (r2_hidden(k4_tarski(X3,X1),X5)|~r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X3,X1),X4)|X5!=k8_relat_1(X2,X4)|~v1_relat_1(X5)|~v1_relat_1(X4)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.50  cnf(c_0_83, negated_conjecture, (r2_hidden(k1_funct_1(esk5_0,esk6_0),esk3_0)|r2_hidden(esk6_0,k1_relat_1(esk4_0))|k1_funct_1(esk5_0,esk7_0)!=k1_funct_1(esk4_0,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_77, c_0_64])])).
% 0.19/0.50  cnf(c_0_84, negated_conjecture, (r2_hidden(k1_funct_1(esk5_0,esk6_0),esk3_0)|r2_hidden(esk7_0,k1_relat_1(esk4_0))), inference(sr,[status(thm)],[c_0_78, c_0_79])).
% 0.19/0.50  cnf(c_0_85, negated_conjecture, (r2_hidden(esk6_0,k1_relat_1(esk5_0))|r2_hidden(esk6_0,k1_relat_1(esk4_0))|k1_funct_1(esk5_0,esk7_0)!=k1_funct_1(esk4_0,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_80, c_0_64])])).
% 0.19/0.50  cnf(c_0_86, negated_conjecture, (r2_hidden(esk6_0,k1_relat_1(esk5_0))|r2_hidden(esk7_0,k1_relat_1(esk4_0))), inference(sr,[status(thm)],[c_0_81, c_0_79])).
% 0.19/0.50  cnf(c_0_87, negated_conjecture, (r2_hidden(k4_tarski(X1,k1_funct_1(esk5_0,X1)),X2)|X2!=k8_relat_1(X3,esk5_0)|~r2_hidden(k1_funct_1(esk5_0,X1),X3)|~r2_hidden(X1,k1_relat_1(esk5_0))|~v1_relat_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_51]), c_0_22])])).
% 0.19/0.50  cnf(c_0_88, negated_conjecture, (r2_hidden(k1_funct_1(esk5_0,esk6_0),esk3_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_69]), c_0_79]), c_0_84])).
% 0.19/0.50  cnf(c_0_89, negated_conjecture, (r2_hidden(esk6_0,k1_relat_1(esk5_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_69]), c_0_79]), c_0_86])).
% 0.19/0.50  cnf(c_0_90, negated_conjecture, (r2_hidden(k4_tarski(esk6_0,k1_funct_1(esk5_0,esk6_0)),X1)|X1!=esk4_0|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_64]), c_0_89])])).
% 0.19/0.50  cnf(c_0_91, negated_conjecture, (r2_hidden(k4_tarski(esk6_0,k1_funct_1(esk5_0,esk6_0)),esk4_0)), inference(spm,[status(thm)],[c_0_90, c_0_12])).
% 0.19/0.50  cnf(c_0_92, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7, c_0_91]), c_0_11]), c_0_12])]), c_0_79]), ['proof']).
% 0.19/0.50  # SZS output end CNFRefutation
% 0.19/0.50  # Proof object total steps             : 93
% 0.19/0.50  # Proof object clause steps            : 86
% 0.19/0.50  # Proof object formula steps           : 7
% 0.19/0.50  # Proof object conjectures             : 77
% 0.19/0.50  # Proof object clause conjectures      : 74
% 0.19/0.50  # Proof object formula conjectures     : 3
% 0.19/0.50  # Proof object initial clauses used    : 23
% 0.19/0.50  # Proof object initial formulas used   : 3
% 0.19/0.50  # Proof object generating inferences   : 55
% 0.19/0.50  # Proof object simplifying inferences  : 97
% 0.19/0.50  # Training examples: 0 positive, 0 negative
% 0.19/0.50  # Parsed axioms                        : 3
% 0.19/0.50  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.50  # Initial clauses                      : 23
% 0.19/0.50  # Removed in clause preprocessing      : 0
% 0.19/0.50  # Initial clauses in saturation        : 23
% 0.19/0.50  # Processed clauses                    : 1441
% 0.19/0.50  # ...of these trivial                  : 56
% 0.19/0.50  # ...subsumed                          : 813
% 0.19/0.50  # ...remaining for further processing  : 572
% 0.19/0.50  # Other redundant clauses eliminated   : 0
% 0.19/0.50  # Clauses deleted for lack of memory   : 0
% 0.19/0.50  # Backward-subsumed                    : 116
% 0.19/0.50  # Backward-rewritten                   : 174
% 0.19/0.50  # Generated clauses                    : 2190
% 0.19/0.50  # ...of the previous two non-trivial   : 2067
% 0.19/0.50  # Contextual simplify-reflections      : 72
% 0.19/0.50  # Paramodulations                      : 2113
% 0.19/0.50  # Factorizations                       : 6
% 0.19/0.50  # Equation resolutions                 : 69
% 0.19/0.50  # Propositional unsat checks           : 0
% 0.19/0.50  #    Propositional check models        : 0
% 0.19/0.50  #    Propositional check unsatisfiable : 0
% 0.19/0.50  #    Propositional clauses             : 0
% 0.19/0.50  #    Propositional clauses after purity: 0
% 0.19/0.50  #    Propositional unsat core size     : 0
% 0.19/0.50  #    Propositional preprocessing time  : 0.000
% 0.19/0.50  #    Propositional encoding time       : 0.000
% 0.19/0.50  #    Propositional solver time         : 0.000
% 0.19/0.50  #    Success case prop preproc time    : 0.000
% 0.19/0.50  #    Success case prop encoding time   : 0.000
% 0.19/0.50  #    Success case prop solver time     : 0.000
% 0.19/0.50  # Current number of processed clauses  : 257
% 0.19/0.50  #    Positive orientable unit clauses  : 9
% 0.19/0.50  #    Positive unorientable unit clauses: 0
% 0.19/0.50  #    Negative unit clauses             : 1
% 0.19/0.50  #    Non-unit-clauses                  : 247
% 0.19/0.50  # Current number of unprocessed clauses: 579
% 0.19/0.50  # ...number of literals in the above   : 3860
% 0.19/0.50  # Current number of archived formulas  : 0
% 0.19/0.50  # Current number of archived clauses   : 315
% 0.19/0.50  # Clause-clause subsumption calls (NU) : 36751
% 0.19/0.50  # Rec. Clause-clause subsumption calls : 3403
% 0.19/0.50  # Non-unit clause-clause subsumptions  : 997
% 0.19/0.50  # Unit Clause-clause subsumption calls : 429
% 0.19/0.50  # Rewrite failures with RHS unbound    : 0
% 0.19/0.50  # BW rewrite match attempts            : 4
% 0.19/0.50  # BW rewrite match successes           : 4
% 0.19/0.50  # Condensation attempts                : 0
% 0.19/0.50  # Condensation successes               : 0
% 0.19/0.50  # Termbank termtop insertions          : 68040
% 0.19/0.50  
% 0.19/0.50  # -------------------------------------------------
% 0.19/0.50  # User time                : 0.160 s
% 0.19/0.50  # System time              : 0.006 s
% 0.19/0.50  # Total time               : 0.166 s
% 0.19/0.50  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
