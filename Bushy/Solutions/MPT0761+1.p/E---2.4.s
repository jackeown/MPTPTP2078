%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : wellord1__t5_wellord1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:15 EDT 2019

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   35 ( 353 expanded)
%              Number of clauses        :   28 ( 135 expanded)
%              Number of leaves         :    3 (  85 expanded)
%              Depth                    :   11
%              Number of atoms          :  149 (1829 expanded)
%              Number of equality atoms :   19 ( 192 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t5_wellord1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v1_wellord1(X1)
      <=> r1_wellord1(X1,k3_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t5_wellord1.p',t5_wellord1)).

fof(d2_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v1_wellord1(X1)
      <=> ! [X2] :
            ~ ( r1_tarski(X2,k3_relat_1(X1))
              & X2 != k1_xboole_0
              & ! [X3] :
                  ~ ( r2_hidden(X3,X2)
                    & r1_xboole_0(k1_wellord1(X1,X3),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t5_wellord1.p',d2_wellord1)).

fof(d3_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r1_wellord1(X1,X2)
        <=> ! [X3] :
              ~ ( r1_tarski(X3,X2)
                & X3 != k1_xboole_0
                & ! [X4] :
                    ~ ( r2_hidden(X4,X3)
                      & r1_xboole_0(k1_wellord1(X1,X4),X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t5_wellord1.p',d3_wellord1)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ( v1_wellord1(X1)
        <=> r1_wellord1(X1,k3_relat_1(X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t5_wellord1])).

fof(c_0_4,plain,(
    ! [X10,X11,X14] :
      ( ( r2_hidden(esk2_2(X10,X11),X11)
        | ~ r1_tarski(X11,k3_relat_1(X10))
        | X11 = k1_xboole_0
        | ~ v1_wellord1(X10)
        | ~ v1_relat_1(X10) )
      & ( r1_xboole_0(k1_wellord1(X10,esk2_2(X10,X11)),X11)
        | ~ r1_tarski(X11,k3_relat_1(X10))
        | X11 = k1_xboole_0
        | ~ v1_wellord1(X10)
        | ~ v1_relat_1(X10) )
      & ( r1_tarski(esk3_1(X10),k3_relat_1(X10))
        | v1_wellord1(X10)
        | ~ v1_relat_1(X10) )
      & ( esk3_1(X10) != k1_xboole_0
        | v1_wellord1(X10)
        | ~ v1_relat_1(X10) )
      & ( ~ r2_hidden(X14,esk3_1(X10))
        | ~ r1_xboole_0(k1_wellord1(X10,X14),esk3_1(X10))
        | v1_wellord1(X10)
        | ~ v1_relat_1(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_wellord1])])])])])).

fof(c_0_5,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & ( ~ v1_wellord1(esk1_0)
      | ~ r1_wellord1(esk1_0,k3_relat_1(esk1_0)) )
    & ( v1_wellord1(esk1_0)
      | r1_wellord1(esk1_0,k3_relat_1(esk1_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

fof(c_0_6,plain,(
    ! [X15,X16,X17,X19,X21] :
      ( ( r2_hidden(esk4_3(X15,X16,X17),X17)
        | ~ r1_tarski(X17,X16)
        | X17 = k1_xboole_0
        | ~ r1_wellord1(X15,X16)
        | ~ v1_relat_1(X15) )
      & ( r1_xboole_0(k1_wellord1(X15,esk4_3(X15,X16,X17)),X17)
        | ~ r1_tarski(X17,X16)
        | X17 = k1_xboole_0
        | ~ r1_wellord1(X15,X16)
        | ~ v1_relat_1(X15) )
      & ( r1_tarski(esk5_2(X15,X19),X19)
        | r1_wellord1(X15,X19)
        | ~ v1_relat_1(X15) )
      & ( esk5_2(X15,X19) != k1_xboole_0
        | r1_wellord1(X15,X19)
        | ~ v1_relat_1(X15) )
      & ( ~ r2_hidden(X21,esk5_2(X15,X19))
        | ~ r1_xboole_0(k1_wellord1(X15,X21),esk5_2(X15,X19))
        | r1_wellord1(X15,X19)
        | ~ v1_relat_1(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_wellord1])])])])])])).

cnf(c_0_7,plain,
    ( r1_tarski(esk3_1(X1),k3_relat_1(X1))
    | v1_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( r1_xboole_0(k1_wellord1(X1,esk4_3(X1,X2,X3)),X3)
    | X3 = k1_xboole_0
    | ~ r1_tarski(X3,X2)
    | ~ r1_wellord1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( r1_tarski(esk3_1(esk1_0),k3_relat_1(esk1_0))
    | v1_wellord1(esk1_0) ),
    inference(spm,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_11,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),X3)
    | X3 = k1_xboole_0
    | ~ r1_tarski(X3,X2)
    | ~ r1_wellord1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,negated_conjecture,
    ( esk3_1(esk1_0) = k1_xboole_0
    | r1_xboole_0(k1_wellord1(X1,esk4_3(X1,k3_relat_1(esk1_0),esk3_1(esk1_0))),esk3_1(esk1_0))
    | v1_wellord1(esk1_0)
    | ~ r1_wellord1(X1,k3_relat_1(esk1_0))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( v1_wellord1(esk1_0)
    | r1_wellord1(esk1_0,k3_relat_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_14,negated_conjecture,
    ( esk3_1(esk1_0) = k1_xboole_0
    | r2_hidden(esk4_3(X1,k3_relat_1(esk1_0),esk3_1(esk1_0)),esk3_1(esk1_0))
    | v1_wellord1(esk1_0)
    | ~ r1_wellord1(X1,k3_relat_1(esk1_0))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_11,c_0_10])).

cnf(c_0_15,plain,
    ( v1_wellord1(X2)
    | ~ r2_hidden(X1,esk3_1(X2))
    | ~ r1_xboole_0(k1_wellord1(X2,X1),esk3_1(X2))
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_16,negated_conjecture,
    ( esk3_1(esk1_0) = k1_xboole_0
    | r1_xboole_0(k1_wellord1(esk1_0,esk4_3(esk1_0,k3_relat_1(esk1_0),esk3_1(esk1_0))),esk3_1(esk1_0))
    | v1_wellord1(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_8])])).

cnf(c_0_17,negated_conjecture,
    ( esk3_1(esk1_0) = k1_xboole_0
    | r2_hidden(esk4_3(esk1_0,k3_relat_1(esk1_0),esk3_1(esk1_0)),esk3_1(esk1_0))
    | v1_wellord1(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_13]),c_0_8])])).

cnf(c_0_18,plain,
    ( r1_xboole_0(k1_wellord1(X1,esk2_2(X1,X2)),X2)
    | X2 = k1_xboole_0
    | ~ r1_tarski(X2,k3_relat_1(X1))
    | ~ v1_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_19,plain,
    ( r1_tarski(esk5_2(X1,X2),X2)
    | r1_wellord1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_20,plain,
    ( r1_wellord1(X1,X2)
    | esk5_2(X1,X2) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_21,plain,
    ( v1_wellord1(X1)
    | esk3_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_22,negated_conjecture,
    ( esk3_1(esk1_0) = k1_xboole_0
    | v1_wellord1(esk1_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_8])]),c_0_17])).

cnf(c_0_23,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | X2 = k1_xboole_0
    | ~ r1_tarski(X2,k3_relat_1(X1))
    | ~ v1_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_24,plain,
    ( r1_xboole_0(k1_wellord1(X1,esk2_2(X1,esk5_2(X2,k3_relat_1(X1)))),esk5_2(X2,k3_relat_1(X1)))
    | r1_wellord1(X2,k3_relat_1(X1))
    | ~ v1_wellord1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( v1_wellord1(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_8])])).

cnf(c_0_26,negated_conjecture,
    ( ~ v1_wellord1(esk1_0)
    | ~ r1_wellord1(esk1_0,k3_relat_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_27,plain,
    ( r2_hidden(esk2_2(X1,esk5_2(X2,k3_relat_1(X1))),esk5_2(X2,k3_relat_1(X1)))
    | r1_wellord1(X2,k3_relat_1(X1))
    | ~ v1_wellord1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_19]),c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( r1_xboole_0(k1_wellord1(esk1_0,esk2_2(esk1_0,esk5_2(X1,k3_relat_1(esk1_0)))),esk5_2(X1,k3_relat_1(esk1_0)))
    | r1_wellord1(X1,k3_relat_1(esk1_0))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_8])])).

cnf(c_0_29,negated_conjecture,
    ( ~ r1_wellord1(esk1_0,k3_relat_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_25])])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk2_2(esk1_0,esk5_2(X1,k3_relat_1(esk1_0))),esk5_2(X1,k3_relat_1(esk1_0)))
    | r1_wellord1(X1,k3_relat_1(esk1_0))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_25]),c_0_8])])).

cnf(c_0_31,plain,
    ( r1_wellord1(X2,X3)
    | ~ r2_hidden(X1,esk5_2(X2,X3))
    | ~ r1_xboole_0(k1_wellord1(X2,X1),esk5_2(X2,X3))
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_32,negated_conjecture,
    ( r1_xboole_0(k1_wellord1(esk1_0,esk2_2(esk1_0,esk5_2(esk1_0,k3_relat_1(esk1_0)))),esk5_2(esk1_0,k3_relat_1(esk1_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_8]),c_0_29])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk2_2(esk1_0,esk5_2(esk1_0,k3_relat_1(esk1_0))),esk5_2(esk1_0,k3_relat_1(esk1_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_8]),c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_8])]),c_0_29]),
    [proof]).
%------------------------------------------------------------------------------
