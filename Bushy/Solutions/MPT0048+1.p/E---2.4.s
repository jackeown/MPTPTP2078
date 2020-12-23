%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : xboole_1__t41_xboole_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:26 EDT 2019

% Result     : Theorem 3.81s
% Output     : CNFRefutation 3.81s
% Verified   : 
% Statistics : Number of formulae       :   34 ( 220 expanded)
%              Number of clauses        :   27 ( 109 expanded)
%              Number of leaves         :    3 (  50 expanded)
%              Depth                    :   13
%              Number of atoms          :  111 (1218 expanded)
%              Number of equality atoms :   27 ( 356 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t41_xboole_1,conjecture,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t41_xboole_1.p',t41_xboole_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t41_xboole_1.p',d5_xboole_0)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t41_xboole_1.p',d3_xboole_0)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(assume_negation,[status(cth)],[t41_xboole_1])).

fof(c_0_4,plain,(
    ! [X29,X30,X31,X32,X33,X34,X35,X36] :
      ( ( r2_hidden(X32,X29)
        | ~ r2_hidden(X32,X31)
        | X31 != k4_xboole_0(X29,X30) )
      & ( ~ r2_hidden(X32,X30)
        | ~ r2_hidden(X32,X31)
        | X31 != k4_xboole_0(X29,X30) )
      & ( ~ r2_hidden(X33,X29)
        | r2_hidden(X33,X30)
        | r2_hidden(X33,X31)
        | X31 != k4_xboole_0(X29,X30) )
      & ( ~ r2_hidden(esk6_3(X34,X35,X36),X36)
        | ~ r2_hidden(esk6_3(X34,X35,X36),X34)
        | r2_hidden(esk6_3(X34,X35,X36),X35)
        | X36 = k4_xboole_0(X34,X35) )
      & ( r2_hidden(esk6_3(X34,X35,X36),X34)
        | r2_hidden(esk6_3(X34,X35,X36),X36)
        | X36 = k4_xboole_0(X34,X35) )
      & ( ~ r2_hidden(esk6_3(X34,X35,X36),X35)
        | r2_hidden(esk6_3(X34,X35,X36),X36)
        | X36 = k4_xboole_0(X34,X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_5,negated_conjecture,(
    k4_xboole_0(k4_xboole_0(esk1_0,esk2_0),esk3_0) != k4_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

cnf(c_0_6,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(esk1_0,esk2_0),esk3_0) != k4_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,plain,
    ( r2_hidden(esk6_3(X1,X2,X3),X1)
    | r2_hidden(esk6_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_9,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X4 != k4_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_10,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( r2_hidden(esk6_3(k4_xboole_0(esk1_0,esk2_0),esk3_0,k4_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))),k4_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0)))
    | r2_hidden(esk6_3(k4_xboole_0(esk1_0,esk2_0),esk3_0,k4_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))),k4_xboole_0(esk1_0,esk2_0)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_8])])).

fof(c_0_12,plain,(
    ! [X20,X21,X22,X23,X24,X25,X26,X27] :
      ( ( ~ r2_hidden(X23,X22)
        | r2_hidden(X23,X20)
        | r2_hidden(X23,X21)
        | X22 != k2_xboole_0(X20,X21) )
      & ( ~ r2_hidden(X24,X20)
        | r2_hidden(X24,X22)
        | X22 != k2_xboole_0(X20,X21) )
      & ( ~ r2_hidden(X24,X21)
        | r2_hidden(X24,X22)
        | X22 != k2_xboole_0(X20,X21) )
      & ( ~ r2_hidden(esk5_3(X25,X26,X27),X25)
        | ~ r2_hidden(esk5_3(X25,X26,X27),X27)
        | X27 = k2_xboole_0(X25,X26) )
      & ( ~ r2_hidden(esk5_3(X25,X26,X27),X26)
        | ~ r2_hidden(esk5_3(X25,X26,X27),X27)
        | X27 = k2_xboole_0(X25,X26) )
      & ( r2_hidden(esk5_3(X25,X26,X27),X27)
        | r2_hidden(esk5_3(X25,X26,X27),X25)
        | r2_hidden(esk5_3(X25,X26,X27),X26)
        | X27 = k2_xboole_0(X25,X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

cnf(c_0_13,plain,
    ( r2_hidden(X1,k4_xboole_0(X2,X3))
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( r2_hidden(esk6_3(k4_xboole_0(esk1_0,esk2_0),esk3_0,k4_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))),esk1_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_10])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_17,plain,
    ( r2_hidden(esk6_3(X1,X2,X3),X2)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk6_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk6_3(X1,X2,X3),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(esk6_3(k4_xboole_0(esk1_0,esk2_0),esk3_0,k4_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))),k4_xboole_0(esk1_0,X1))
    | r2_hidden(esk6_3(k4_xboole_0(esk1_0,esk2_0),esk3_0,k4_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))),X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk6_3(k4_xboole_0(esk1_0,esk2_0),esk3_0,k4_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))),k2_xboole_0(esk2_0,esk3_0))
    | ~ r2_hidden(esk6_3(k4_xboole_0(esk1_0,esk2_0),esk3_0,k4_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))),k4_xboole_0(esk1_0,esk2_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_7]),c_0_19])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk6_3(k4_xboole_0(esk1_0,esk2_0),esk3_0,k4_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))),k4_xboole_0(esk1_0,esk2_0))
    | ~ r2_hidden(esk6_3(k4_xboole_0(esk1_0,esk2_0),esk3_0,k4_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))),k2_xboole_0(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_11])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk6_3(k4_xboole_0(esk1_0,esk2_0),esk3_0,k4_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))),k2_xboole_0(esk2_0,esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_18]),c_0_23])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_xboole_0(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk6_3(k4_xboole_0(esk1_0,esk2_0),esk3_0,k4_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))),k4_xboole_0(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_25])])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k2_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_26])).

cnf(c_0_29,negated_conjecture,
    ( ~ r2_hidden(esk6_3(k4_xboole_0(esk1_0,esk2_0),esk3_0,k4_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))),esk2_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_27])).

cnf(c_0_30,plain,
    ( r2_hidden(esk6_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk6_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk6_3(k4_xboole_0(esk1_0,esk2_0),esk3_0,k4_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))),esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_25]),c_0_29])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk6_3(k4_xboole_0(esk1_0,esk2_0),esk3_0,k4_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))),k4_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_7])).

cnf(c_0_33,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_32]),c_0_25])]),
    [proof]).
%------------------------------------------------------------------------------
