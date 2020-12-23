%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0213+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:14 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   21 (  35 expanded)
%              Number of clauses        :   11 (  18 expanded)
%              Number of leaves         :    5 (  10 expanded)
%              Depth                    :    6
%              Number of atoms          :   56 (  76 expanded)
%              Number of equality atoms :   19 (  23 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(d4_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k3_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r2_hidden(X3,X4)
              & r2_hidden(X4,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(t2_zfmisc_1,conjecture,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

fof(c_0_5,plain,(
    ! [X17,X18] :
      ( ~ r2_hidden(X17,X18)
      | ~ v1_xboole_0(X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

fof(c_0_6,plain,(
    ! [X5,X6,X7,X9,X10,X11,X12,X14] :
      ( ( r2_hidden(X7,esk1_3(X5,X6,X7))
        | ~ r2_hidden(X7,X6)
        | X6 != k3_tarski(X5) )
      & ( r2_hidden(esk1_3(X5,X6,X7),X5)
        | ~ r2_hidden(X7,X6)
        | X6 != k3_tarski(X5) )
      & ( ~ r2_hidden(X9,X10)
        | ~ r2_hidden(X10,X5)
        | r2_hidden(X9,X6)
        | X6 != k3_tarski(X5) )
      & ( ~ r2_hidden(esk2_2(X11,X12),X12)
        | ~ r2_hidden(esk2_2(X11,X12),X14)
        | ~ r2_hidden(X14,X11)
        | X12 = k3_tarski(X11) )
      & ( r2_hidden(esk2_2(X11,X12),esk3_2(X11,X12))
        | r2_hidden(esk2_2(X11,X12),X12)
        | X12 = k3_tarski(X11) )
      & ( r2_hidden(esk3_2(X11,X12),X11)
        | r2_hidden(esk2_2(X11,X12),X12)
        | X12 = k3_tarski(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).

fof(c_0_7,plain,(
    ! [X16] :
      ( ~ v1_xboole_0(X16)
      | X16 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_8,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( r2_hidden(esk3_2(X1,X2),X1)
    | r2_hidden(esk2_2(X1,X2),X2)
    | X2 = k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

cnf(c_0_12,plain,
    ( X1 = k3_tarski(X2)
    | r2_hidden(esk3_2(X2,X1),X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_13,plain,
    ( o_0_0_xboole_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

fof(c_0_14,negated_conjecture,(
    k3_tarski(k1_xboole_0) != k1_xboole_0 ),
    inference(assume_negation,[status(cth)],[t2_zfmisc_1])).

cnf(c_0_15,plain,
    ( X1 = k3_tarski(X2)
    | ~ v1_xboole_0(X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_8,c_0_12])).

cnf(c_0_16,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_11,c_0_13])).

fof(c_0_17,negated_conjecture,(
    k3_tarski(k1_xboole_0) != k1_xboole_0 ),
    inference(fof_simplification,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( k3_tarski(X1) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_19,negated_conjecture,
    ( k3_tarski(k1_xboole_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_20,plain,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_16]),c_0_19]),
    [proof]).

%------------------------------------------------------------------------------
