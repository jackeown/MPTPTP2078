%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0023+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:54 EST 2020

% Result     : Theorem 1.56s
% Output     : CNFRefutation 1.56s
% Verified   : 
% Statistics : Number of formulae       :   43 (1604 expanded)
%              Number of clauses        :   38 ( 915 expanded)
%              Number of leaves         :    2 ( 344 expanded)
%              Depth                    :   15
%              Number of atoms          :  107 (10550 expanded)
%              Number of equality atoms :   44 (3192 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(t16_xboole_1,conjecture,(
    ! [X1,X2,X3] : k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(c_0_2,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11,X12] :
      ( ( r2_hidden(X8,X5)
        | ~ r2_hidden(X8,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( r2_hidden(X8,X6)
        | ~ r2_hidden(X8,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X5)
        | ~ r2_hidden(X9,X6)
        | r2_hidden(X9,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X10)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X11)
        | X12 = k3_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k3_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X11)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k3_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_3,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_2])).

cnf(c_0_4,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_2])).

cnf(c_0_5,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_2])).

cnf(c_0_6,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_3])).

cnf(c_0_7,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_2])).

cnf(c_0_8,plain,
    ( X3 = k3_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_2])).

cnf(c_0_9,plain,
    ( k3_xboole_0(X1,X2) = X1
    | r2_hidden(esk1_3(X1,X2,X1),X1) ),
    inference(ef,[status(thm)],[c_0_4])).

cnf(c_0_10,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_5])).

cnf(c_0_11,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X4 != k3_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_2])).

cnf(c_0_12,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X3,X4)
    | r2_hidden(esk1_3(X3,X4,k3_xboole_0(X1,X2)),X4)
    | r2_hidden(esk1_3(X3,X4,k3_xboole_0(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_6,c_0_7])).

cnf(c_0_13,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r2_hidden(esk1_3(X1,X2,X1),X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_9]),c_0_9])).

cnf(c_0_14,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,X2)
    | r2_hidden(esk1_3(k3_xboole_0(X1,X2),X3,k3_xboole_0(X1,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_10,c_0_9])).

cnf(c_0_15,plain,
    ( k3_xboole_0(X1,X2) = X2
    | r2_hidden(esk1_3(X1,X2,X2),X2) ),
    inference(ef,[status(thm)],[c_0_7])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X3,X2)
    | r2_hidden(esk1_3(X3,X2,k3_xboole_0(X1,X2)),X2) ),
    inference(ef,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X1) = k3_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_19,plain,
    ( k3_xboole_0(X1,X2) = X2
    | ~ r2_hidden(esk1_3(X1,X2,X2),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_15]),c_0_15])).

cnf(c_0_20,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(X2,X3)
    | r2_hidden(esk1_3(X1,k3_xboole_0(X2,X3),k3_xboole_0(X2,X3)),X2) ),
    inference(spm,[status(thm)],[c_0_10,c_0_15])).

cnf(c_0_21,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X3,X4)
    | ~ r2_hidden(esk1_3(X3,X4,k3_xboole_0(X1,X2)),X4)
    | ~ r2_hidden(esk1_3(X3,X4,k3_xboole_0(X1,X2)),X3)
    | ~ r2_hidden(esk1_3(X3,X4,k3_xboole_0(X1,X2)),X2)
    | ~ r2_hidden(esk1_3(X3,X4,k3_xboole_0(X1,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_8,c_0_16])).

cnf(c_0_22,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X3,X1)
    | r2_hidden(esk1_3(X3,X1,k3_xboole_0(X1,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_23,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X3,X4)
    | r2_hidden(esk1_3(X3,X4,k3_xboole_0(X1,X2)),X3)
    | r2_hidden(esk1_3(X3,X4,k3_xboole_0(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_6,c_0_4])).

cnf(c_0_24,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = X3
    | ~ r2_hidden(esk1_3(k3_xboole_0(X1,X2),X3,X3),X2)
    | ~ r2_hidden(esk1_3(k3_xboole_0(X1,X2),X3,X3),X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_16])).

cnf(c_0_25,plain,
    ( k3_xboole_0(X1,k3_xboole_0(k3_xboole_0(X2,X3),X4)) = k3_xboole_0(k3_xboole_0(X2,X3),X4)
    | r2_hidden(esk1_3(X1,k3_xboole_0(k3_xboole_0(X2,X3),X4),k3_xboole_0(k3_xboole_0(X2,X3),X4)),X3) ),
    inference(spm,[status(thm)],[c_0_6,c_0_20])).

cnf(c_0_26,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X3,X1)
    | ~ r2_hidden(esk1_3(X3,X1,k3_xboole_0(X1,X2)),X3)
    | ~ r2_hidden(esk1_3(X3,X1,k3_xboole_0(X1,X2)),X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_22])).

cnf(c_0_27,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X3)
    | r2_hidden(esk1_3(X2,X3,k3_xboole_0(X1,X2)),X2) ),
    inference(ef,[status(thm)],[c_0_23])).

cnf(c_0_28,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X3,X2),X4)) = k3_xboole_0(k3_xboole_0(X3,X2),X4)
    | ~ r2_hidden(esk1_3(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X3,X2),X4),k3_xboole_0(k3_xboole_0(X3,X2),X4)),X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_29,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(X2,X3)
    | r2_hidden(esk1_3(X1,k3_xboole_0(X2,X3),k3_xboole_0(X2,X3)),X3) ),
    inference(spm,[status(thm)],[c_0_6,c_0_15])).

cnf(c_0_30,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_27])).

cnf(c_0_31,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X3,X2),X1)) = k3_xboole_0(k3_xboole_0(X3,X2),X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_32,plain,
    ( k3_xboole_0(k3_xboole_0(k3_xboole_0(X1,X2),X3),k3_xboole_0(X3,X2)) = k3_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_33,plain,
    ( k3_xboole_0(k3_xboole_0(k3_xboole_0(X1,X2),X3),k3_xboole_0(X3,X1)) = k3_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_32,c_0_30])).

cnf(c_0_34,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X2,X3),X1)) = k3_xboole_0(k3_xboole_0(X2,X3),X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_30])).

cnf(c_0_35,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X2,X3)) = k3_xboole_0(k3_xboole_0(X2,X3),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_33]),c_0_34])).

fof(c_0_36,negated_conjecture,(
    ~ ! [X1,X2,X3] : k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(assume_negation,[status(cth)],[t16_xboole_1])).

cnf(c_0_37,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X2,X3)) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_35])).

fof(c_0_38,negated_conjecture,(
    k3_xboole_0(k3_xboole_0(esk2_0,esk3_0),esk4_0) != k3_xboole_0(esk2_0,k3_xboole_0(esk3_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_36])])])).

cnf(c_0_39,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2)) = k3_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[c_0_32,c_0_37])).

cnf(c_0_40,negated_conjecture,
    ( k3_xboole_0(k3_xboole_0(esk2_0,esk3_0),esk4_0) != k3_xboole_0(esk2_0,k3_xboole_0(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_41,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_30]),c_0_37])).

cnf(c_0_42,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_41])]),
    [proof]).

%------------------------------------------------------------------------------
