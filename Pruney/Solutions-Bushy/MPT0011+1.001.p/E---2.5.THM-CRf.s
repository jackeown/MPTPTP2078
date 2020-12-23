%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0011+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:52 EST 2020

% Result     : Theorem 0.40s
% Output     : CNFRefutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 960 expanded)
%              Number of clauses        :   41 ( 515 expanded)
%              Number of leaves         :    3 ( 222 expanded)
%              Depth                    :   16
%              Number of atoms          :  108 (5860 expanded)
%              Number of equality atoms :   50 (1840 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t4_xboole_1,conjecture,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(c_0_3,plain,(
    ! [X7,X8,X9,X10,X11,X12,X13,X14] :
      ( ( ~ r2_hidden(X10,X9)
        | r2_hidden(X10,X7)
        | r2_hidden(X10,X8)
        | X9 != k2_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X11,X7)
        | r2_hidden(X11,X9)
        | X9 != k2_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X11,X8)
        | r2_hidden(X11,X9)
        | X9 != k2_xboole_0(X7,X8) )
      & ( ~ r2_hidden(esk1_3(X12,X13,X14),X12)
        | ~ r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k2_xboole_0(X12,X13) )
      & ( ~ r2_hidden(esk1_3(X12,X13,X14),X13)
        | ~ r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k2_xboole_0(X12,X13) )
      & ( r2_hidden(esk1_3(X12,X13,X14),X14)
        | r2_hidden(esk1_3(X12,X13,X14),X12)
        | r2_hidden(esk1_3(X12,X13,X14),X13)
        | X14 = k2_xboole_0(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

cnf(c_0_4,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_5,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X2)
    | X3 = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_6,plain,
    ( X3 = k2_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_7,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_4])).

cnf(c_0_8,plain,
    ( X3 = k2_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_9,plain,
    ( k2_xboole_0(X1,X2) = X2
    | r2_hidden(esk1_3(X1,X2,X2),X1)
    | r2_hidden(esk1_3(X1,X2,X2),X2) ),
    inference(ef,[status(thm)],[c_0_5])).

cnf(c_0_10,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X3,X4)
    | ~ r2_hidden(esk1_3(X3,X4,k2_xboole_0(X1,X2)),X3)
    | ~ r2_hidden(esk1_3(X3,X4,k2_xboole_0(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_6,c_0_7])).

cnf(c_0_11,plain,
    ( k2_xboole_0(X1,X2) = X2
    | r2_hidden(esk1_3(X1,X2,X2),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_9]),c_0_9])).

fof(c_0_12,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_13,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_xboole_0(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_14,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(X2,X3)
    | ~ r2_hidden(esk1_3(X1,k2_xboole_0(X2,X3),k2_xboole_0(X2,X3)),X3) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_15,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k2_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(X2,X3)
    | ~ r2_hidden(esk1_3(X1,k2_xboole_0(X2,X3),k2_xboole_0(X2,X3)),X2) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_18,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = X3
    | r2_hidden(esk1_3(k2_xboole_0(X1,X2),X3,X3),X2)
    | r2_hidden(esk1_3(k2_xboole_0(X1,X2),X3,X3),X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_11])).

cnf(c_0_19,plain,
    ( k2_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4)) = k2_xboole_0(k2_xboole_0(X2,X3),X4)
    | ~ r2_hidden(esk1_3(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4),k2_xboole_0(k2_xboole_0(X2,X3),X4)),X3) ),
    inference(spm,[status(thm)],[c_0_17,c_0_7])).

cnf(c_0_20,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X3,X1)) = k2_xboole_0(X3,X1)
    | r2_hidden(esk1_3(k2_xboole_0(X1,X2),k2_xboole_0(X3,X1),k2_xboole_0(X3,X1)),X2) ),
    inference(spm,[status(thm)],[c_0_14,c_0_18])).

cnf(c_0_21,plain,
    ( k2_xboole_0(X1,X2) = X1
    | r2_hidden(esk1_3(X1,X2,X1),X1)
    | r2_hidden(esk1_3(X1,X2,X1),X2) ),
    inference(ef,[status(thm)],[c_0_5])).

cnf(c_0_22,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(k2_xboole_0(X3,X2),X1)) = k2_xboole_0(k2_xboole_0(X3,X2),X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_23,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X3,X4)
    | ~ r2_hidden(esk1_3(X3,X4,k2_xboole_0(X1,X2)),X4)
    | ~ r2_hidden(esk1_3(X3,X4,k2_xboole_0(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_8,c_0_7])).

cnf(c_0_24,plain,
    ( k2_xboole_0(X1,X2) = X1
    | r2_hidden(esk1_3(X1,X2,X1),X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_6,c_0_21]),c_0_21])).

cnf(c_0_25,plain,
    ( k2_xboole_0(k2_xboole_0(k2_xboole_0(X1,X2),X3),k2_xboole_0(X3,X2)) = k2_xboole_0(k2_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_15,c_0_22])).

cnf(c_0_26,plain,
    ( k2_xboole_0(X1,X1) = X1
    | r2_hidden(esk1_3(X1,X1,X1),X1) ),
    inference(ef,[status(thm)],[c_0_9])).

cnf(c_0_27,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(k2_xboole_0(X1,X2),X3,k2_xboole_0(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_28,plain,
    ( k2_xboole_0(k2_xboole_0(k2_xboole_0(X1,X2),X3),k2_xboole_0(X3,X1)) = k2_xboole_0(k2_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_25,c_0_15])).

cnf(c_0_29,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(k2_xboole_0(X2,X3),X1)) = k2_xboole_0(k2_xboole_0(X2,X3),X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_15])).

cnf(c_0_30,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_26]),c_0_26])).

cnf(c_0_31,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X1)) = k2_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_24]),c_0_15])).

cnf(c_0_32,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X2,X3)) = k2_xboole_0(k2_xboole_0(X2,X3),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_28]),c_0_29])).

cnf(c_0_33,plain,
    ( k2_xboole_0(X1,X2) = X1
    | ~ r2_hidden(esk1_3(X1,X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_30])).

cnf(c_0_34,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X3)) = X1
    | r2_hidden(esk1_3(X1,k2_xboole_0(X2,X3),X1),X3)
    | r2_hidden(esk1_3(X1,k2_xboole_0(X2,X3),X1),X2) ),
    inference(spm,[status(thm)],[c_0_16,c_0_24])).

cnf(c_0_35,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_31,c_0_15])).

cnf(c_0_36,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X2,X3)) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_32])).

cnf(c_0_37,plain,
    ( k2_xboole_0(k2_xboole_0(X1,k2_xboole_0(X2,X3)),X4) = k2_xboole_0(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(esk1_3(k2_xboole_0(X1,k2_xboole_0(X2,X3)),X4,k2_xboole_0(X1,k2_xboole_0(X2,X3))),X3) ),
    inference(spm,[status(thm)],[c_0_27,c_0_7])).

cnf(c_0_38,plain,
    ( k2_xboole_0(X1,X2) = X1
    | r2_hidden(esk1_3(X1,k2_xboole_0(X1,X2),X1),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])).

fof(c_0_39,negated_conjecture,(
    ~ ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(assume_negation,[status(cth)],[t4_xboole_1])).

cnf(c_0_40,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X3,X2)) = k2_xboole_0(X1,k2_xboole_0(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_31])).

cnf(c_0_41,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X1))) = k2_xboole_0(X2,k2_xboole_0(X3,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_15]),c_0_31]),c_0_15])])).

fof(c_0_42,negated_conjecture,(
    k2_xboole_0(k2_xboole_0(esk2_0,esk3_0),esk4_0) != k2_xboole_0(esk2_0,k2_xboole_0(esk3_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_39])])])).

cnf(c_0_43,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(X2,k2_xboole_0(X1,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_40]),c_0_40])).

cnf(c_0_44,plain,
    ( k2_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X1),X3)) = k2_xboole_0(k2_xboole_0(X2,X1),X3) ),
    inference(spm,[status(thm)],[c_0_41,c_0_15])).

cnf(c_0_45,negated_conjecture,
    ( k2_xboole_0(k2_xboole_0(esk2_0,esk3_0),esk4_0) != k2_xboole_0(esk2_0,k2_xboole_0(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_46,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_43]),c_0_44])).

cnf(c_0_47,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_46])]),
    [proof]).

%------------------------------------------------------------------------------
