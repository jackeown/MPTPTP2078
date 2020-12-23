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
% DateTime   : Thu Dec  3 10:55:35 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 745 expanded)
%              Number of clauses        :   36 ( 263 expanded)
%              Number of leaves         :    6 ( 182 expanded)
%              Depth                    :   14
%              Number of atoms          :  183 (4844 expanded)
%              Number of equality atoms :   64 (1390 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t165_funct_1,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ! [X3] :
              ( ( r1_tarski(X3,k1_relat_1(X1))
                & r1_tarski(X3,k1_relat_1(X2)) )
             => ( k7_relat_1(X1,X3) = k7_relat_1(X2,X3)
              <=> ! [X4] :
                    ( r2_hidden(X4,X3)
                   => k1_funct_1(X1,X4) = k1_funct_1(X2,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t165_funct_1)).

fof(t68_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v1_funct_1(X3) )
         => ( ( k1_relat_1(X2) = k3_xboole_0(k1_relat_1(X3),X1)
              & ! [X4] :
                  ( r2_hidden(X4,k1_relat_1(X2))
                 => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) ) )
           => X2 = k7_relat_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_funct_1)).

fof(t90_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k1_relat_1(k7_relat_1(X2,X1)) = k3_xboole_0(k1_relat_1(X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(t91_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X1,k1_relat_1(X2))
       => k1_relat_1(k7_relat_1(X2,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(t70_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))
       => k1_funct_1(k7_relat_1(X3,X2),X1) = k1_funct_1(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_funct_1)).

fof(fc8_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k7_relat_1(X1,X2))
        & v1_funct_1(k7_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( v1_relat_1(X2)
              & v1_funct_1(X2) )
           => ! [X3] :
                ( ( r1_tarski(X3,k1_relat_1(X1))
                  & r1_tarski(X3,k1_relat_1(X2)) )
               => ( k7_relat_1(X1,X3) = k7_relat_1(X2,X3)
                <=> ! [X4] :
                      ( r2_hidden(X4,X3)
                     => k1_funct_1(X1,X4) = k1_funct_1(X2,X4) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t165_funct_1])).

fof(c_0_7,plain,(
    ! [X11,X12,X13] :
      ( ( r2_hidden(esk1_3(X11,X12,X13),k1_relat_1(X12))
        | k1_relat_1(X12) != k3_xboole_0(k1_relat_1(X13),X11)
        | X12 = k7_relat_1(X13,X11)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( k1_funct_1(X12,esk1_3(X11,X12,X13)) != k1_funct_1(X13,esk1_3(X11,X12,X13))
        | k1_relat_1(X12) != k3_xboole_0(k1_relat_1(X13),X11)
        | X12 = k7_relat_1(X13,X11)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t68_funct_1])])])])])).

fof(c_0_8,plain,(
    ! [X5,X6] :
      ( ~ v1_relat_1(X6)
      | k1_relat_1(k7_relat_1(X6,X5)) = k3_xboole_0(k1_relat_1(X6),X5) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).

fof(c_0_9,plain,(
    ! [X7,X8] :
      ( ~ v1_relat_1(X8)
      | ~ r1_tarski(X7,k1_relat_1(X8))
      | k1_relat_1(k7_relat_1(X8,X7)) = X7 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_relat_1])])).

fof(c_0_10,negated_conjecture,(
    ! [X22] :
      ( v1_relat_1(esk2_0)
      & v1_funct_1(esk2_0)
      & v1_relat_1(esk3_0)
      & v1_funct_1(esk3_0)
      & r1_tarski(esk4_0,k1_relat_1(esk2_0))
      & r1_tarski(esk4_0,k1_relat_1(esk3_0))
      & ( r2_hidden(esk5_0,esk4_0)
        | k7_relat_1(esk2_0,esk4_0) != k7_relat_1(esk3_0,esk4_0) )
      & ( k1_funct_1(esk2_0,esk5_0) != k1_funct_1(esk3_0,esk5_0)
        | k7_relat_1(esk2_0,esk4_0) != k7_relat_1(esk3_0,esk4_0) )
      & ( k7_relat_1(esk2_0,esk4_0) = k7_relat_1(esk3_0,esk4_0)
        | ~ r2_hidden(X22,esk4_0)
        | k1_funct_1(esk2_0,X22) = k1_funct_1(esk3_0,X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])])])).

cnf(c_0_11,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),k1_relat_1(X2))
    | X2 = k7_relat_1(X3,X1)
    | k1_relat_1(X2) != k3_xboole_0(k1_relat_1(X3),X1)
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k3_xboole_0(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = X2
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( r1_tarski(esk4_0,k1_relat_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_16,plain,(
    ! [X15,X16,X17] :
      ( ~ v1_relat_1(X17)
      | ~ v1_funct_1(X17)
      | ~ r2_hidden(X15,k1_relat_1(k7_relat_1(X17,X16)))
      | k1_funct_1(k7_relat_1(X17,X16),X15) = k1_funct_1(X17,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t70_funct_1])])).

cnf(c_0_17,negated_conjecture,
    ( r1_tarski(esk4_0,k1_relat_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_19,plain,
    ( X1 = k7_relat_1(X2,X3)
    | r2_hidden(esk1_3(X3,X1,X2),k1_relat_1(X1))
    | k1_relat_1(X1) != k1_relat_1(k7_relat_1(X2,X3))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_20,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk2_0,esk4_0)) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15])])).

cnf(c_0_21,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_22,plain,
    ( k1_funct_1(k7_relat_1(X1,X3),X2) = k1_funct_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(k7_relat_1(X1,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk3_0,esk4_0)) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_17]),c_0_18])])).

cnf(c_0_24,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_25,negated_conjecture,
    ( X1 = k7_relat_1(esk2_0,esk4_0)
    | r2_hidden(esk1_3(esk4_0,X1,esk2_0),k1_relat_1(X1))
    | k1_relat_1(X1) != esk4_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_15])])).

fof(c_0_26,plain,(
    ! [X9,X10] :
      ( ( v1_relat_1(k7_relat_1(X9,X10))
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9) )
      & ( v1_funct_1(k7_relat_1(X9,X10))
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc8_funct_1])])])).

cnf(c_0_27,plain,
    ( X1 = k7_relat_1(X3,X2)
    | k1_funct_1(X1,esk1_3(X2,X1,X3)) != k1_funct_1(X3,esk1_3(X2,X1,X3))
    | k1_relat_1(X1) != k3_xboole_0(k1_relat_1(X3),X2)
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_28,negated_conjecture,
    ( k1_funct_1(k7_relat_1(esk3_0,esk4_0),X1) = k1_funct_1(esk3_0,X1)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_18])])).

cnf(c_0_29,negated_conjecture,
    ( k7_relat_1(esk2_0,esk4_0) = k7_relat_1(esk3_0,esk4_0)
    | r2_hidden(esk1_3(esk4_0,k7_relat_1(esk3_0,esk4_0),esk2_0),esk4_0)
    | ~ v1_funct_1(k7_relat_1(esk3_0,esk4_0))
    | ~ v1_relat_1(k7_relat_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_23])).

cnf(c_0_30,plain,
    ( v1_funct_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( k7_relat_1(esk3_0,esk4_0) = k7_relat_1(X1,X2)
    | k1_funct_1(esk3_0,esk1_3(X2,k7_relat_1(esk3_0,esk4_0),X1)) != k1_funct_1(X1,esk1_3(X2,k7_relat_1(esk3_0,esk4_0),X1))
    | k3_xboole_0(k1_relat_1(X1),X2) != esk4_0
    | ~ r2_hidden(esk1_3(X2,k7_relat_1(esk3_0,esk4_0),X1),esk4_0)
    | ~ v1_funct_1(k7_relat_1(esk3_0,esk4_0))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k7_relat_1(esk3_0,esk4_0))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_23])).

cnf(c_0_32,negated_conjecture,
    ( k7_relat_1(esk2_0,esk4_0) = k7_relat_1(esk3_0,esk4_0)
    | r2_hidden(esk1_3(esk4_0,k7_relat_1(esk3_0,esk4_0),esk2_0),esk4_0)
    | ~ v1_relat_1(k7_relat_1(esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_24]),c_0_18])])).

cnf(c_0_33,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( k7_relat_1(esk3_0,esk4_0) = k7_relat_1(X1,X2)
    | k1_funct_1(esk3_0,esk1_3(X2,k7_relat_1(esk3_0,esk4_0),X1)) != k1_funct_1(X1,esk1_3(X2,k7_relat_1(esk3_0,esk4_0),X1))
    | k3_xboole_0(k1_relat_1(X1),X2) != esk4_0
    | ~ r2_hidden(esk1_3(X2,k7_relat_1(esk3_0,esk4_0),X1),esk4_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k7_relat_1(esk3_0,esk4_0))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_30]),c_0_24]),c_0_18])])).

cnf(c_0_35,negated_conjecture,
    ( k7_relat_1(esk2_0,esk4_0) = k7_relat_1(esk3_0,esk4_0)
    | k1_funct_1(esk2_0,X1) = k1_funct_1(esk3_0,X1)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_36,negated_conjecture,
    ( k7_relat_1(esk2_0,esk4_0) = k7_relat_1(esk3_0,esk4_0)
    | r2_hidden(esk1_3(esk4_0,k7_relat_1(esk3_0,esk4_0),esk2_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_24]),c_0_18])])).

cnf(c_0_37,negated_conjecture,
    ( k7_relat_1(esk3_0,esk4_0) = k7_relat_1(X1,X2)
    | k1_funct_1(esk3_0,esk1_3(X2,k7_relat_1(esk3_0,esk4_0),X1)) != k1_funct_1(X1,esk1_3(X2,k7_relat_1(esk3_0,esk4_0),X1))
    | k3_xboole_0(k1_relat_1(X1),X2) != esk4_0
    | ~ r2_hidden(esk1_3(X2,k7_relat_1(esk3_0,esk4_0),X1),esk4_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_33]),c_0_24]),c_0_18])])).

cnf(c_0_38,negated_conjecture,
    ( k1_funct_1(esk2_0,esk1_3(esk4_0,k7_relat_1(esk3_0,esk4_0),esk2_0)) = k1_funct_1(esk3_0,esk1_3(esk4_0,k7_relat_1(esk3_0,esk4_0),esk2_0))
    | k7_relat_1(esk2_0,esk4_0) = k7_relat_1(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_39,negated_conjecture,
    ( k7_relat_1(esk2_0,esk4_0) = k7_relat_1(esk3_0,esk4_0)
    | k3_xboole_0(k1_relat_1(esk2_0),esk4_0) != esk4_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_36]),c_0_21]),c_0_15])]),c_0_38])).

cnf(c_0_40,negated_conjecture,
    ( k1_funct_1(k7_relat_1(esk2_0,esk4_0),X1) = k1_funct_1(esk2_0,X1)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_20]),c_0_21]),c_0_15])])).

cnf(c_0_41,negated_conjecture,
    ( k7_relat_1(esk2_0,esk4_0) = k7_relat_1(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_12]),c_0_20]),c_0_15])])).

cnf(c_0_42,negated_conjecture,
    ( k1_funct_1(k7_relat_1(esk3_0,esk4_0),X1) = k1_funct_1(esk2_0,X1)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(rw,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk5_0,esk4_0)
    | k7_relat_1(esk2_0,esk4_0) != k7_relat_1(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_44,negated_conjecture,
    ( k1_funct_1(esk2_0,esk5_0) != k1_funct_1(esk3_0,esk5_0)
    | k7_relat_1(esk2_0,esk4_0) != k7_relat_1(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_45,negated_conjecture,
    ( k1_funct_1(esk2_0,X1) = k1_funct_1(esk3_0,X1)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_42])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk5_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_41])])).

cnf(c_0_47,negated_conjecture,
    ( k1_funct_1(esk2_0,esk5_0) != k1_funct_1(esk3_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_41])])).

cnf(c_0_48,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:55:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.19/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.39  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.39  #
% 0.19/0.39  # Preprocessing time       : 0.028 s
% 0.19/0.39  # Presaturation interreduction done
% 0.19/0.39  
% 0.19/0.39  # Proof found!
% 0.19/0.39  # SZS status Theorem
% 0.19/0.39  # SZS output start CNFRefutation
% 0.19/0.39  fof(t165_funct_1, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((r1_tarski(X3,k1_relat_1(X1))&r1_tarski(X3,k1_relat_1(X2)))=>(k7_relat_1(X1,X3)=k7_relat_1(X2,X3)<=>![X4]:(r2_hidden(X4,X3)=>k1_funct_1(X1,X4)=k1_funct_1(X2,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t165_funct_1)).
% 0.19/0.39  fof(t68_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((k1_relat_1(X2)=k3_xboole_0(k1_relat_1(X3),X1)&![X4]:(r2_hidden(X4,k1_relat_1(X2))=>k1_funct_1(X2,X4)=k1_funct_1(X3,X4)))=>X2=k7_relat_1(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_funct_1)).
% 0.19/0.39  fof(t90_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k1_relat_1(k7_relat_1(X2,X1))=k3_xboole_0(k1_relat_1(X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 0.19/0.39  fof(t91_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>k1_relat_1(k7_relat_1(X2,X1))=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 0.19/0.39  fof(t70_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))=>k1_funct_1(k7_relat_1(X3,X2),X1)=k1_funct_1(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_funct_1)).
% 0.19/0.39  fof(fc8_funct_1, axiom, ![X1, X2]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k7_relat_1(X1,X2))&v1_funct_1(k7_relat_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_funct_1)).
% 0.19/0.39  fof(c_0_6, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((r1_tarski(X3,k1_relat_1(X1))&r1_tarski(X3,k1_relat_1(X2)))=>(k7_relat_1(X1,X3)=k7_relat_1(X2,X3)<=>![X4]:(r2_hidden(X4,X3)=>k1_funct_1(X1,X4)=k1_funct_1(X2,X4))))))), inference(assume_negation,[status(cth)],[t165_funct_1])).
% 0.19/0.39  fof(c_0_7, plain, ![X11, X12, X13]:((r2_hidden(esk1_3(X11,X12,X13),k1_relat_1(X12))|k1_relat_1(X12)!=k3_xboole_0(k1_relat_1(X13),X11)|X12=k7_relat_1(X13,X11)|(~v1_relat_1(X13)|~v1_funct_1(X13))|(~v1_relat_1(X12)|~v1_funct_1(X12)))&(k1_funct_1(X12,esk1_3(X11,X12,X13))!=k1_funct_1(X13,esk1_3(X11,X12,X13))|k1_relat_1(X12)!=k3_xboole_0(k1_relat_1(X13),X11)|X12=k7_relat_1(X13,X11)|(~v1_relat_1(X13)|~v1_funct_1(X13))|(~v1_relat_1(X12)|~v1_funct_1(X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t68_funct_1])])])])])).
% 0.19/0.39  fof(c_0_8, plain, ![X5, X6]:(~v1_relat_1(X6)|k1_relat_1(k7_relat_1(X6,X5))=k3_xboole_0(k1_relat_1(X6),X5)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).
% 0.19/0.39  fof(c_0_9, plain, ![X7, X8]:(~v1_relat_1(X8)|(~r1_tarski(X7,k1_relat_1(X8))|k1_relat_1(k7_relat_1(X8,X7))=X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_relat_1])])).
% 0.19/0.39  fof(c_0_10, negated_conjecture, ![X22]:((v1_relat_1(esk2_0)&v1_funct_1(esk2_0))&((v1_relat_1(esk3_0)&v1_funct_1(esk3_0))&((r1_tarski(esk4_0,k1_relat_1(esk2_0))&r1_tarski(esk4_0,k1_relat_1(esk3_0)))&(((r2_hidden(esk5_0,esk4_0)|k7_relat_1(esk2_0,esk4_0)!=k7_relat_1(esk3_0,esk4_0))&(k1_funct_1(esk2_0,esk5_0)!=k1_funct_1(esk3_0,esk5_0)|k7_relat_1(esk2_0,esk4_0)!=k7_relat_1(esk3_0,esk4_0)))&(k7_relat_1(esk2_0,esk4_0)=k7_relat_1(esk3_0,esk4_0)|(~r2_hidden(X22,esk4_0)|k1_funct_1(esk2_0,X22)=k1_funct_1(esk3_0,X22))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])])])).
% 0.19/0.39  cnf(c_0_11, plain, (r2_hidden(esk1_3(X1,X2,X3),k1_relat_1(X2))|X2=k7_relat_1(X3,X1)|k1_relat_1(X2)!=k3_xboole_0(k1_relat_1(X3),X1)|~v1_relat_1(X3)|~v1_funct_1(X3)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.39  cnf(c_0_12, plain, (k1_relat_1(k7_relat_1(X1,X2))=k3_xboole_0(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.39  cnf(c_0_13, plain, (k1_relat_1(k7_relat_1(X1,X2))=X2|~v1_relat_1(X1)|~r1_tarski(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.39  cnf(c_0_14, negated_conjecture, (r1_tarski(esk4_0,k1_relat_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.39  cnf(c_0_15, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.39  fof(c_0_16, plain, ![X15, X16, X17]:(~v1_relat_1(X17)|~v1_funct_1(X17)|(~r2_hidden(X15,k1_relat_1(k7_relat_1(X17,X16)))|k1_funct_1(k7_relat_1(X17,X16),X15)=k1_funct_1(X17,X15))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t70_funct_1])])).
% 0.19/0.39  cnf(c_0_17, negated_conjecture, (r1_tarski(esk4_0,k1_relat_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.39  cnf(c_0_18, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.39  cnf(c_0_19, plain, (X1=k7_relat_1(X2,X3)|r2_hidden(esk1_3(X3,X1,X2),k1_relat_1(X1))|k1_relat_1(X1)!=k1_relat_1(k7_relat_1(X2,X3))|~v1_funct_1(X2)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.19/0.39  cnf(c_0_20, negated_conjecture, (k1_relat_1(k7_relat_1(esk2_0,esk4_0))=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_15])])).
% 0.19/0.39  cnf(c_0_21, negated_conjecture, (v1_funct_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.39  cnf(c_0_22, plain, (k1_funct_1(k7_relat_1(X1,X3),X2)=k1_funct_1(X1,X2)|~v1_relat_1(X1)|~v1_funct_1(X1)|~r2_hidden(X2,k1_relat_1(k7_relat_1(X1,X3)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.39  cnf(c_0_23, negated_conjecture, (k1_relat_1(k7_relat_1(esk3_0,esk4_0))=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_17]), c_0_18])])).
% 0.19/0.39  cnf(c_0_24, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.39  cnf(c_0_25, negated_conjecture, (X1=k7_relat_1(esk2_0,esk4_0)|r2_hidden(esk1_3(esk4_0,X1,esk2_0),k1_relat_1(X1))|k1_relat_1(X1)!=esk4_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21]), c_0_15])])).
% 0.19/0.39  fof(c_0_26, plain, ![X9, X10]:((v1_relat_1(k7_relat_1(X9,X10))|(~v1_relat_1(X9)|~v1_funct_1(X9)))&(v1_funct_1(k7_relat_1(X9,X10))|(~v1_relat_1(X9)|~v1_funct_1(X9)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc8_funct_1])])])).
% 0.19/0.39  cnf(c_0_27, plain, (X1=k7_relat_1(X3,X2)|k1_funct_1(X1,esk1_3(X2,X1,X3))!=k1_funct_1(X3,esk1_3(X2,X1,X3))|k1_relat_1(X1)!=k3_xboole_0(k1_relat_1(X3),X2)|~v1_relat_1(X3)|~v1_funct_1(X3)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.39  cnf(c_0_28, negated_conjecture, (k1_funct_1(k7_relat_1(esk3_0,esk4_0),X1)=k1_funct_1(esk3_0,X1)|~r2_hidden(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24]), c_0_18])])).
% 0.19/0.39  cnf(c_0_29, negated_conjecture, (k7_relat_1(esk2_0,esk4_0)=k7_relat_1(esk3_0,esk4_0)|r2_hidden(esk1_3(esk4_0,k7_relat_1(esk3_0,esk4_0),esk2_0),esk4_0)|~v1_funct_1(k7_relat_1(esk3_0,esk4_0))|~v1_relat_1(k7_relat_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_25, c_0_23])).
% 0.19/0.39  cnf(c_0_30, plain, (v1_funct_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.39  cnf(c_0_31, negated_conjecture, (k7_relat_1(esk3_0,esk4_0)=k7_relat_1(X1,X2)|k1_funct_1(esk3_0,esk1_3(X2,k7_relat_1(esk3_0,esk4_0),X1))!=k1_funct_1(X1,esk1_3(X2,k7_relat_1(esk3_0,esk4_0),X1))|k3_xboole_0(k1_relat_1(X1),X2)!=esk4_0|~r2_hidden(esk1_3(X2,k7_relat_1(esk3_0,esk4_0),X1),esk4_0)|~v1_funct_1(k7_relat_1(esk3_0,esk4_0))|~v1_funct_1(X1)|~v1_relat_1(k7_relat_1(esk3_0,esk4_0))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_23])).
% 0.19/0.39  cnf(c_0_32, negated_conjecture, (k7_relat_1(esk2_0,esk4_0)=k7_relat_1(esk3_0,esk4_0)|r2_hidden(esk1_3(esk4_0,k7_relat_1(esk3_0,esk4_0),esk2_0),esk4_0)|~v1_relat_1(k7_relat_1(esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_24]), c_0_18])])).
% 0.19/0.39  cnf(c_0_33, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.39  cnf(c_0_34, negated_conjecture, (k7_relat_1(esk3_0,esk4_0)=k7_relat_1(X1,X2)|k1_funct_1(esk3_0,esk1_3(X2,k7_relat_1(esk3_0,esk4_0),X1))!=k1_funct_1(X1,esk1_3(X2,k7_relat_1(esk3_0,esk4_0),X1))|k3_xboole_0(k1_relat_1(X1),X2)!=esk4_0|~r2_hidden(esk1_3(X2,k7_relat_1(esk3_0,esk4_0),X1),esk4_0)|~v1_funct_1(X1)|~v1_relat_1(k7_relat_1(esk3_0,esk4_0))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_30]), c_0_24]), c_0_18])])).
% 0.19/0.39  cnf(c_0_35, negated_conjecture, (k7_relat_1(esk2_0,esk4_0)=k7_relat_1(esk3_0,esk4_0)|k1_funct_1(esk2_0,X1)=k1_funct_1(esk3_0,X1)|~r2_hidden(X1,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.39  cnf(c_0_36, negated_conjecture, (k7_relat_1(esk2_0,esk4_0)=k7_relat_1(esk3_0,esk4_0)|r2_hidden(esk1_3(esk4_0,k7_relat_1(esk3_0,esk4_0),esk2_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_24]), c_0_18])])).
% 0.19/0.39  cnf(c_0_37, negated_conjecture, (k7_relat_1(esk3_0,esk4_0)=k7_relat_1(X1,X2)|k1_funct_1(esk3_0,esk1_3(X2,k7_relat_1(esk3_0,esk4_0),X1))!=k1_funct_1(X1,esk1_3(X2,k7_relat_1(esk3_0,esk4_0),X1))|k3_xboole_0(k1_relat_1(X1),X2)!=esk4_0|~r2_hidden(esk1_3(X2,k7_relat_1(esk3_0,esk4_0),X1),esk4_0)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_33]), c_0_24]), c_0_18])])).
% 0.19/0.39  cnf(c_0_38, negated_conjecture, (k1_funct_1(esk2_0,esk1_3(esk4_0,k7_relat_1(esk3_0,esk4_0),esk2_0))=k1_funct_1(esk3_0,esk1_3(esk4_0,k7_relat_1(esk3_0,esk4_0),esk2_0))|k7_relat_1(esk2_0,esk4_0)=k7_relat_1(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.19/0.39  cnf(c_0_39, negated_conjecture, (k7_relat_1(esk2_0,esk4_0)=k7_relat_1(esk3_0,esk4_0)|k3_xboole_0(k1_relat_1(esk2_0),esk4_0)!=esk4_0), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_36]), c_0_21]), c_0_15])]), c_0_38])).
% 0.19/0.39  cnf(c_0_40, negated_conjecture, (k1_funct_1(k7_relat_1(esk2_0,esk4_0),X1)=k1_funct_1(esk2_0,X1)|~r2_hidden(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_20]), c_0_21]), c_0_15])])).
% 0.19/0.39  cnf(c_0_41, negated_conjecture, (k7_relat_1(esk2_0,esk4_0)=k7_relat_1(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_12]), c_0_20]), c_0_15])])).
% 0.19/0.39  cnf(c_0_42, negated_conjecture, (k1_funct_1(k7_relat_1(esk3_0,esk4_0),X1)=k1_funct_1(esk2_0,X1)|~r2_hidden(X1,esk4_0)), inference(rw,[status(thm)],[c_0_40, c_0_41])).
% 0.19/0.39  cnf(c_0_43, negated_conjecture, (r2_hidden(esk5_0,esk4_0)|k7_relat_1(esk2_0,esk4_0)!=k7_relat_1(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.39  cnf(c_0_44, negated_conjecture, (k1_funct_1(esk2_0,esk5_0)!=k1_funct_1(esk3_0,esk5_0)|k7_relat_1(esk2_0,esk4_0)!=k7_relat_1(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.39  cnf(c_0_45, negated_conjecture, (k1_funct_1(esk2_0,X1)=k1_funct_1(esk3_0,X1)|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_28, c_0_42])).
% 0.19/0.39  cnf(c_0_46, negated_conjecture, (r2_hidden(esk5_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_41])])).
% 0.19/0.39  cnf(c_0_47, negated_conjecture, (k1_funct_1(esk2_0,esk5_0)!=k1_funct_1(esk3_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_41])])).
% 0.19/0.39  cnf(c_0_48, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_47]), ['proof']).
% 0.19/0.39  # SZS output end CNFRefutation
% 0.19/0.39  # Proof object total steps             : 49
% 0.19/0.39  # Proof object clause steps            : 36
% 0.19/0.39  # Proof object formula steps           : 13
% 0.19/0.39  # Proof object conjectures             : 31
% 0.19/0.39  # Proof object clause conjectures      : 28
% 0.19/0.39  # Proof object formula conjectures     : 3
% 0.19/0.39  # Proof object initial clauses used    : 16
% 0.19/0.39  # Proof object initial formulas used   : 6
% 0.19/0.39  # Proof object generating inferences   : 17
% 0.19/0.39  # Proof object simplifying inferences  : 39
% 0.19/0.39  # Training examples: 0 positive, 0 negative
% 0.19/0.39  # Parsed axioms                        : 6
% 0.19/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.39  # Initial clauses                      : 16
% 0.19/0.39  # Removed in clause preprocessing      : 0
% 0.19/0.39  # Initial clauses in saturation        : 16
% 0.19/0.39  # Processed clauses                    : 133
% 0.19/0.39  # ...of these trivial                  : 1
% 0.19/0.39  # ...subsumed                          : 9
% 0.19/0.39  # ...remaining for further processing  : 123
% 0.19/0.39  # Other redundant clauses eliminated   : 0
% 0.19/0.39  # Clauses deleted for lack of memory   : 0
% 0.19/0.39  # Backward-subsumed                    : 30
% 0.19/0.39  # Backward-rewritten                   : 44
% 0.19/0.39  # Generated clauses                    : 141
% 0.19/0.39  # ...of the previous two non-trivial   : 167
% 0.19/0.39  # Contextual simplify-reflections      : 3
% 0.19/0.39  # Paramodulations                      : 135
% 0.19/0.39  # Factorizations                       : 0
% 0.19/0.39  # Equation resolutions                 : 6
% 0.19/0.39  # Propositional unsat checks           : 0
% 0.19/0.39  #    Propositional check models        : 0
% 0.19/0.39  #    Propositional check unsatisfiable : 0
% 0.19/0.39  #    Propositional clauses             : 0
% 0.19/0.39  #    Propositional clauses after purity: 0
% 0.19/0.39  #    Propositional unsat core size     : 0
% 0.19/0.39  #    Propositional preprocessing time  : 0.000
% 0.19/0.39  #    Propositional encoding time       : 0.000
% 0.19/0.39  #    Propositional solver time         : 0.000
% 0.19/0.39  #    Success case prop preproc time    : 0.000
% 0.19/0.39  #    Success case prop encoding time   : 0.000
% 0.19/0.39  #    Success case prop solver time     : 0.000
% 0.19/0.39  # Current number of processed clauses  : 33
% 0.19/0.39  #    Positive orientable unit clauses  : 12
% 0.19/0.39  #    Positive unorientable unit clauses: 0
% 0.19/0.39  #    Negative unit clauses             : 1
% 0.19/0.39  #    Non-unit-clauses                  : 20
% 0.19/0.39  # Current number of unprocessed clauses: 66
% 0.19/0.39  # ...number of literals in the above   : 434
% 0.19/0.39  # Current number of archived formulas  : 0
% 0.19/0.39  # Current number of archived clauses   : 90
% 0.19/0.39  # Clause-clause subsumption calls (NU) : 2094
% 0.19/0.39  # Rec. Clause-clause subsumption calls : 262
% 0.19/0.39  # Non-unit clause-clause subsumptions  : 42
% 0.19/0.39  # Unit Clause-clause subsumption calls : 24
% 0.19/0.39  # Rewrite failures with RHS unbound    : 0
% 0.19/0.39  # BW rewrite match attempts            : 3
% 0.19/0.39  # BW rewrite match successes           : 3
% 0.19/0.39  # Condensation attempts                : 0
% 0.19/0.39  # Condensation successes               : 0
% 0.19/0.39  # Termbank termtop insertions          : 8152
% 0.19/0.39  
% 0.19/0.39  # -------------------------------------------------
% 0.19/0.39  # User time                : 0.040 s
% 0.19/0.39  # System time              : 0.005 s
% 0.19/0.39  # Total time               : 0.045 s
% 0.19/0.39  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
