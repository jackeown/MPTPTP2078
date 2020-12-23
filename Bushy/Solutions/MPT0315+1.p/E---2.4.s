%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : zfmisc_1__t127_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:59 EDT 2019

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   20 (  37 expanded)
%              Number of clauses        :   13 (  16 expanded)
%              Number of leaves         :    3 (   9 expanded)
%              Depth                    :    7
%              Number of atoms          :   49 ( 106 expanded)
%              Number of equality atoms :    2 (   4 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t127_zfmisc_1.p',t4_xboole_0)).

fof(t104_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4,X5] :
      ~ ( r2_hidden(X1,k3_xboole_0(k2_zfmisc_1(X2,X3),k2_zfmisc_1(X4,X5)))
        & ! [X6,X7] :
            ~ ( X1 = k4_tarski(X6,X7)
              & r2_hidden(X6,k3_xboole_0(X2,X4))
              & r2_hidden(X7,k3_xboole_0(X3,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t127_zfmisc_1.p',t104_zfmisc_1)).

fof(t127_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( r1_xboole_0(X1,X2)
        | r1_xboole_0(X3,X4) )
     => r1_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t127_zfmisc_1.p',t127_zfmisc_1)).

fof(c_0_3,plain,(
    ! [X27,X28,X30,X31,X32] :
      ( ( r1_xboole_0(X27,X28)
        | r2_hidden(esk7_2(X27,X28),k3_xboole_0(X27,X28)) )
      & ( ~ r2_hidden(X32,k3_xboole_0(X30,X31))
        | ~ r1_xboole_0(X30,X31) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_4,plain,(
    ! [X19,X20,X21,X22,X23] :
      ( ( X19 = k4_tarski(esk5_5(X19,X20,X21,X22,X23),esk6_5(X19,X20,X21,X22,X23))
        | ~ r2_hidden(X19,k3_xboole_0(k2_zfmisc_1(X20,X21),k2_zfmisc_1(X22,X23))) )
      & ( r2_hidden(esk5_5(X19,X20,X21,X22,X23),k3_xboole_0(X20,X22))
        | ~ r2_hidden(X19,k3_xboole_0(k2_zfmisc_1(X20,X21),k2_zfmisc_1(X22,X23))) )
      & ( r2_hidden(esk6_5(X19,X20,X21,X22,X23),k3_xboole_0(X21,X23))
        | ~ r2_hidden(X19,k3_xboole_0(k2_zfmisc_1(X20,X21),k2_zfmisc_1(X22,X23))) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t104_zfmisc_1])])])])).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( r1_xboole_0(X1,X2)
          | r1_xboole_0(X3,X4) )
       => r1_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ) ),
    inference(assume_negation,[status(cth)],[t127_zfmisc_1])).

cnf(c_0_6,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_7,plain,
    ( r2_hidden(esk5_5(X1,X2,X3,X4,X5),k3_xboole_0(X2,X4))
    | ~ r2_hidden(X1,k3_xboole_0(k2_zfmisc_1(X2,X3),k2_zfmisc_1(X4,X5))) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

fof(c_0_8,negated_conjecture,
    ( ( r1_xboole_0(esk1_0,esk2_0)
      | r1_xboole_0(esk3_0,esk4_0) )
    & ~ r1_xboole_0(k2_zfmisc_1(esk1_0,esk3_0),k2_zfmisc_1(esk2_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

cnf(c_0_9,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(k2_zfmisc_1(X2,X3),k2_zfmisc_1(X4,X5)))
    | ~ r1_xboole_0(X2,X4) ),
    inference(spm,[status(thm)],[c_0_6,c_0_7])).

cnf(c_0_10,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk7_2(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_11,plain,
    ( r2_hidden(esk6_5(X1,X2,X3,X4,X5),k3_xboole_0(X3,X5))
    | ~ r2_hidden(X1,k3_xboole_0(k2_zfmisc_1(X2,X3),k2_zfmisc_1(X4,X5))) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_12,negated_conjecture,
    ( ~ r1_xboole_0(k2_zfmisc_1(esk1_0,esk3_0),k2_zfmisc_1(esk2_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( r1_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))
    | ~ r1_xboole_0(X1,X3) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_14,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(k2_zfmisc_1(X2,X3),k2_zfmisc_1(X4,X5)))
    | ~ r1_xboole_0(X3,X5) ),
    inference(spm,[status(thm)],[c_0_6,c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( r1_xboole_0(esk1_0,esk2_0)
    | r1_xboole_0(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_16,negated_conjecture,
    ( ~ r1_xboole_0(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_17,plain,
    ( r1_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))
    | ~ r1_xboole_0(X2,X4) ),
    inference(spm,[status(thm)],[c_0_14,c_0_10])).

cnf(c_0_18,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_19,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_17]),c_0_18])]),
    [proof]).
%------------------------------------------------------------------------------
