%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0761+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:09 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   27 (  79 expanded)
%              Number of clauses        :   20 (  31 expanded)
%              Number of leaves         :    3 (  21 expanded)
%              Depth                    :    7
%              Number of atoms          :  125 ( 550 expanded)
%              Number of equality atoms :   14 (  69 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_wellord1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_wellord1)).

fof(t5_wellord1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v1_wellord1(X1)
      <=> r1_wellord1(X1,k3_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_wellord1)).

fof(c_0_3,plain,(
    ! [X10,X11,X12,X14,X16] :
      ( ( r2_hidden(esk3_3(X10,X11,X12),X12)
        | ~ r1_tarski(X12,X11)
        | X12 = k1_xboole_0
        | ~ r1_wellord1(X10,X11)
        | ~ v1_relat_1(X10) )
      & ( r1_xboole_0(k1_wellord1(X10,esk3_3(X10,X11,X12)),X12)
        | ~ r1_tarski(X12,X11)
        | X12 = k1_xboole_0
        | ~ r1_wellord1(X10,X11)
        | ~ v1_relat_1(X10) )
      & ( r1_tarski(esk4_2(X10,X14),X14)
        | r1_wellord1(X10,X14)
        | ~ v1_relat_1(X10) )
      & ( esk4_2(X10,X14) != k1_xboole_0
        | r1_wellord1(X10,X14)
        | ~ v1_relat_1(X10) )
      & ( ~ r2_hidden(X16,esk4_2(X10,X14))
        | ~ r1_xboole_0(k1_wellord1(X10,X16),esk4_2(X10,X14))
        | r1_wellord1(X10,X14)
        | ~ v1_relat_1(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_wellord1])])])])])])).

fof(c_0_4,plain,(
    ! [X5,X6,X9] :
      ( ( r2_hidden(esk1_2(X5,X6),X6)
        | ~ r1_tarski(X6,k3_relat_1(X5))
        | X6 = k1_xboole_0
        | ~ v1_wellord1(X5)
        | ~ v1_relat_1(X5) )
      & ( r1_xboole_0(k1_wellord1(X5,esk1_2(X5,X6)),X6)
        | ~ r1_tarski(X6,k3_relat_1(X5))
        | X6 = k1_xboole_0
        | ~ v1_wellord1(X5)
        | ~ v1_relat_1(X5) )
      & ( r1_tarski(esk2_1(X5),k3_relat_1(X5))
        | v1_wellord1(X5)
        | ~ v1_relat_1(X5) )
      & ( esk2_1(X5) != k1_xboole_0
        | v1_wellord1(X5)
        | ~ v1_relat_1(X5) )
      & ( ~ r2_hidden(X9,esk2_1(X5))
        | ~ r1_xboole_0(k1_wellord1(X5,X9),esk2_1(X5))
        | v1_wellord1(X5)
        | ~ v1_relat_1(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_wellord1])])])])])).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ( v1_wellord1(X1)
        <=> r1_wellord1(X1,k3_relat_1(X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t5_wellord1])).

cnf(c_0_6,plain,
    ( r1_wellord1(X2,X3)
    | ~ r2_hidden(X1,esk4_2(X2,X3))
    | ~ r1_xboole_0(k1_wellord1(X2,X1),esk4_2(X2,X3))
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_7,plain,
    ( r1_xboole_0(k1_wellord1(X1,esk1_2(X1,X2)),X2)
    | X2 = k1_xboole_0
    | ~ r1_tarski(X2,k3_relat_1(X1))
    | ~ v1_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | X2 = k1_xboole_0
    | ~ r1_tarski(X2,k3_relat_1(X1))
    | ~ v1_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_9,plain,
    ( r1_wellord1(X1,X2)
    | esk4_2(X1,X2) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

fof(c_0_10,negated_conjecture,
    ( v1_relat_1(esk5_0)
    & ( ~ v1_wellord1(esk5_0)
      | ~ r1_wellord1(esk5_0,k3_relat_1(esk5_0)) )
    & ( v1_wellord1(esk5_0)
      | r1_wellord1(esk5_0,k3_relat_1(esk5_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

cnf(c_0_11,plain,
    ( r1_wellord1(X1,X2)
    | ~ r1_tarski(esk4_2(X1,X2),k3_relat_1(X1))
    | ~ v1_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_6,c_0_7]),c_0_8]),c_0_9])).

cnf(c_0_12,plain,
    ( r1_tarski(esk4_2(X1,X2),X2)
    | r1_wellord1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_13,plain,
    ( v1_wellord1(X2)
    | ~ r2_hidden(X1,esk2_1(X2))
    | ~ r1_xboole_0(k1_wellord1(X2,X1),esk2_1(X2))
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_14,plain,
    ( r1_xboole_0(k1_wellord1(X1,esk3_3(X1,X2,X3)),X3)
    | X3 = k1_xboole_0
    | ~ r1_tarski(X3,X2)
    | ~ r1_wellord1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_15,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),X3)
    | X3 = k1_xboole_0
    | ~ r1_tarski(X3,X2)
    | ~ r1_wellord1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_16,plain,
    ( v1_wellord1(X1)
    | esk2_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_17,negated_conjecture,
    ( ~ v1_wellord1(esk5_0)
    | ~ r1_wellord1(esk5_0,k3_relat_1(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( r1_wellord1(X1,k3_relat_1(X1))
    | ~ v1_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_20,plain,
    ( v1_wellord1(X1)
    | ~ r1_wellord1(X1,X2)
    | ~ r1_tarski(esk2_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15]),c_0_16])).

cnf(c_0_21,plain,
    ( r1_tarski(esk2_1(X1),k3_relat_1(X1))
    | v1_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_22,negated_conjecture,
    ( v1_wellord1(esk5_0)
    | r1_wellord1(esk5_0,k3_relat_1(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_23,negated_conjecture,
    ( ~ v1_wellord1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])])).

cnf(c_0_24,plain,
    ( v1_wellord1(X1)
    | ~ r1_wellord1(X1,k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( r1_wellord1(esk5_0,k3_relat_1(esk5_0)) ),
    inference(sr,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_26,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_19])]),c_0_23]),
    [proof]).

%------------------------------------------------------------------------------
