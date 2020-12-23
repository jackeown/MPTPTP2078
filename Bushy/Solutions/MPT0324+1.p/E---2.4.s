%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : zfmisc_1__t137_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:42:00 EDT 2019

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   15 (  21 expanded)
%              Number of clauses        :    8 (   8 expanded)
%              Number of leaves         :    3 (   5 expanded)
%              Depth                    :    5
%              Number of atoms          :   49 (  67 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t137_zfmisc_1.p',d4_xboole_0)).

fof(t137_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4,X5] :
      ( ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
        & r2_hidden(X1,k2_zfmisc_1(X4,X5)) )
     => r2_hidden(X1,k2_zfmisc_1(k3_xboole_0(X2,X4),k3_xboole_0(X3,X5))) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t137_zfmisc_1.p',t137_zfmisc_1)).

fof(t123_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t137_zfmisc_1.p',t123_zfmisc_1)).

fof(c_0_3,plain,(
    ! [X15,X16,X17,X18,X19,X20,X21,X22] :
      ( ( r2_hidden(X18,X15)
        | ~ r2_hidden(X18,X17)
        | X17 != k3_xboole_0(X15,X16) )
      & ( r2_hidden(X18,X16)
        | ~ r2_hidden(X18,X17)
        | X17 != k3_xboole_0(X15,X16) )
      & ( ~ r2_hidden(X19,X15)
        | ~ r2_hidden(X19,X16)
        | r2_hidden(X19,X17)
        | X17 != k3_xboole_0(X15,X16) )
      & ( ~ r2_hidden(esk6_3(X20,X21,X22),X22)
        | ~ r2_hidden(esk6_3(X20,X21,X22),X20)
        | ~ r2_hidden(esk6_3(X20,X21,X22),X21)
        | X22 = k3_xboole_0(X20,X21) )
      & ( r2_hidden(esk6_3(X20,X21,X22),X20)
        | r2_hidden(esk6_3(X20,X21,X22),X22)
        | X22 = k3_xboole_0(X20,X21) )
      & ( r2_hidden(esk6_3(X20,X21,X22),X21)
        | r2_hidden(esk6_3(X20,X21,X22),X22)
        | X22 = k3_xboole_0(X20,X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5] :
        ( ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
          & r2_hidden(X1,k2_zfmisc_1(X4,X5)) )
       => r2_hidden(X1,k2_zfmisc_1(k3_xboole_0(X2,X4),k3_xboole_0(X3,X5))) ) ),
    inference(assume_negation,[status(cth)],[t137_zfmisc_1])).

cnf(c_0_5,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X4 != k3_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

fof(c_0_6,negated_conjecture,
    ( r2_hidden(esk1_0,k2_zfmisc_1(esk2_0,esk3_0))
    & r2_hidden(esk1_0,k2_zfmisc_1(esk4_0,esk5_0))
    & ~ r2_hidden(esk1_0,k2_zfmisc_1(k3_xboole_0(esk2_0,esk4_0),k3_xboole_0(esk3_0,esk5_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

cnf(c_0_7,plain,
    ( r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_5])).

cnf(c_0_8,negated_conjecture,
    ( r2_hidden(esk1_0,k2_zfmisc_1(esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_9,plain,(
    ! [X25,X26,X27,X28] : k2_zfmisc_1(k3_xboole_0(X25,X26),k3_xboole_0(X27,X28)) = k3_xboole_0(k2_zfmisc_1(X25,X27),k2_zfmisc_1(X26,X28)) ),
    inference(variable_rename,[status(thm)],[t123_zfmisc_1])).

cnf(c_0_10,negated_conjecture,
    ( r2_hidden(esk1_0,k3_xboole_0(X1,k2_zfmisc_1(esk4_0,esk5_0)))
    | ~ r2_hidden(esk1_0,X1) ),
    inference(spm,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( r2_hidden(esk1_0,k2_zfmisc_1(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,plain,
    ( k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( ~ r2_hidden(esk1_0,k2_zfmisc_1(k3_xboole_0(esk2_0,esk4_0),k3_xboole_0(esk3_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_14,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12]),c_0_13]),
    [proof]).
%------------------------------------------------------------------------------
