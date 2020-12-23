%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : zfmisc_1__t2_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:42:05 EDT 2019

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
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
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t2_zfmisc_1.p',t7_boole)).

fof(d4_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k3_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r2_hidden(X3,X4)
              & r2_hidden(X4,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t2_zfmisc_1.p',d4_tarski)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t2_zfmisc_1.p',t6_boole)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t2_zfmisc_1.p',dt_o_0_0_xboole_0)).

fof(t2_zfmisc_1,conjecture,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t2_zfmisc_1.p',t2_zfmisc_1)).

fof(c_0_5,plain,(
    ! [X19,X20] :
      ( ~ r2_hidden(X19,X20)
      | ~ v1_xboole_0(X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

fof(c_0_6,plain,(
    ! [X7,X8,X9,X11,X12,X13,X14,X16] :
      ( ( r2_hidden(X9,esk1_3(X7,X8,X9))
        | ~ r2_hidden(X9,X8)
        | X8 != k3_tarski(X7) )
      & ( r2_hidden(esk1_3(X7,X8,X9),X7)
        | ~ r2_hidden(X9,X8)
        | X8 != k3_tarski(X7) )
      & ( ~ r2_hidden(X11,X12)
        | ~ r2_hidden(X12,X7)
        | r2_hidden(X11,X8)
        | X8 != k3_tarski(X7) )
      & ( ~ r2_hidden(esk2_2(X13,X14),X14)
        | ~ r2_hidden(esk2_2(X13,X14),X16)
        | ~ r2_hidden(X16,X13)
        | X14 = k3_tarski(X13) )
      & ( r2_hidden(esk2_2(X13,X14),esk3_2(X13,X14))
        | r2_hidden(esk2_2(X13,X14),X14)
        | X14 = k3_tarski(X13) )
      & ( r2_hidden(esk3_2(X13,X14),X13)
        | r2_hidden(esk2_2(X13,X14),X14)
        | X14 = k3_tarski(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).

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
    ( X1 = k3_tarski(k1_xboole_0)
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
