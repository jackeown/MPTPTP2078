%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : xboole_0__t7_xboole_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:19 EDT 2019

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   18 (  30 expanded)
%              Number of clauses        :   10 (  14 expanded)
%              Number of leaves         :    4 (   8 expanded)
%              Depth                    :    5
%              Number of atoms          :   30 (  51 expanded)
%              Number of equality atoms :   10 (  20 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/xboole_0__t7_xboole_0.p',l13_xboole_0)).

fof(t7_xboole_0,conjecture,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/xboole_0__t7_xboole_0.p',t7_xboole_0)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/xboole_0__t7_xboole_0.p',dt_o_0_0_xboole_0)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/xboole_0__t7_xboole_0.p',d1_xboole_0)).

fof(c_0_4,plain,(
    ! [X11] :
      ( ~ v1_xboole_0(X11)
      | X11 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] :
        ~ ( X1 != k1_xboole_0
          & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    inference(assume_negation,[status(cth)],[t7_xboole_0])).

cnf(c_0_6,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

fof(c_0_8,negated_conjecture,(
    ! [X4] :
      ( esk1_0 != k1_xboole_0
      & ~ r2_hidden(X4,esk1_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])])).

fof(c_0_9,plain,(
    ! [X7,X8,X9] :
      ( ( ~ v1_xboole_0(X7)
        | ~ r2_hidden(X8,X7) )
      & ( r2_hidden(esk2_1(X9),X9)
        | v1_xboole_0(X9) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_10,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(spm,[status(thm)],[c_0_6,c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( ~ r2_hidden(X1,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( r2_hidden(esk2_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( esk1_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( X1 = o_0_0_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(rw,[status(thm)],[c_0_6,c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( v1_xboole_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( esk1_0 != o_0_0_xboole_0 ),
    inference(rw,[status(thm)],[c_0_13,c_0_10])).

cnf(c_0_17,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16]),
    [proof]).
%------------------------------------------------------------------------------
