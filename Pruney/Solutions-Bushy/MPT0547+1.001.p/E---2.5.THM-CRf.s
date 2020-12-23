%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0547+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:47 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   23 (  40 expanded)
%              Number of clauses        :   13 (  20 expanded)
%              Number of leaves         :    5 (  11 expanded)
%              Depth                    :    7
%              Number of atoms          :   73 (  99 expanded)
%              Number of equality atoms :   20 (  27 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(d13_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( X3 = k9_relat_1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r2_hidden(k4_tarski(X5,X4),X1)
                  & r2_hidden(X5,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_relat_1)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(t149_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_relat_1)).

fof(c_0_5,plain,(
    ! [X19,X20] :
      ( ~ r2_hidden(X19,X20)
      | ~ v1_xboole_0(X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

fof(c_0_6,plain,(
    ! [X6,X7,X8,X9,X11,X12,X13,X14,X16] :
      ( ( r2_hidden(k4_tarski(esk1_4(X6,X7,X8,X9),X9),X6)
        | ~ r2_hidden(X9,X8)
        | X8 != k9_relat_1(X6,X7)
        | ~ v1_relat_1(X6) )
      & ( r2_hidden(esk1_4(X6,X7,X8,X9),X7)
        | ~ r2_hidden(X9,X8)
        | X8 != k9_relat_1(X6,X7)
        | ~ v1_relat_1(X6) )
      & ( ~ r2_hidden(k4_tarski(X12,X11),X6)
        | ~ r2_hidden(X12,X7)
        | r2_hidden(X11,X8)
        | X8 != k9_relat_1(X6,X7)
        | ~ v1_relat_1(X6) )
      & ( ~ r2_hidden(esk2_3(X6,X13,X14),X14)
        | ~ r2_hidden(k4_tarski(X16,esk2_3(X6,X13,X14)),X6)
        | ~ r2_hidden(X16,X13)
        | X14 = k9_relat_1(X6,X13)
        | ~ v1_relat_1(X6) )
      & ( r2_hidden(k4_tarski(esk3_3(X6,X13,X14),esk2_3(X6,X13,X14)),X6)
        | r2_hidden(esk2_3(X6,X13,X14),X14)
        | X14 = k9_relat_1(X6,X13)
        | ~ v1_relat_1(X6) )
      & ( r2_hidden(esk3_3(X6,X13,X14),X13)
        | r2_hidden(esk2_3(X6,X13,X14),X14)
        | X14 = k9_relat_1(X6,X13)
        | ~ v1_relat_1(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_relat_1])])])])])])).

fof(c_0_7,plain,(
    ! [X18] :
      ( ~ v1_xboole_0(X18)
      | X18 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_8,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),X2)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

cnf(c_0_12,plain,
    ( X1 = k9_relat_1(X2,X3)
    | r2_hidden(esk3_3(X2,X3,X1),X3)
    | ~ v1_xboole_0(X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_13,plain,
    ( o_0_0_xboole_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => k9_relat_1(X1,k1_xboole_0) = k1_xboole_0 ) ),
    inference(assume_negation,[status(cth)],[t149_relat_1])).

cnf(c_0_15,plain,
    ( X1 = k9_relat_1(X2,X3)
    | ~ v1_xboole_0(X3)
    | ~ v1_xboole_0(X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_8,c_0_12])).

cnf(c_0_16,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_11,c_0_13])).

fof(c_0_17,negated_conjecture,
    ( v1_relat_1(esk4_0)
    & k9_relat_1(esk4_0,k1_xboole_0) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

cnf(c_0_18,plain,
    ( k9_relat_1(X1,X2) = k1_xboole_0
    | ~ v1_xboole_0(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_19,negated_conjecture,
    ( k9_relat_1(esk4_0,k1_xboole_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_20,plain,
    ( k9_relat_1(X1,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])]),
    [proof]).

%------------------------------------------------------------------------------
