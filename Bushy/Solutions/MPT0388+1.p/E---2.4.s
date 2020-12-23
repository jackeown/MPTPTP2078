%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : setfam_1__t6_setfam_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:20 EDT 2019

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   22 (  38 expanded)
%              Number of clauses        :   15 (  16 expanded)
%              Number of leaves         :    3 (   9 expanded)
%              Depth                    :    8
%              Number of atoms          :   99 ( 196 expanded)
%              Number of equality atoms :   33 (  66 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t6_setfam_1,conjecture,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
         => r1_tarski(X2,X3) )
     => ( X1 = k1_xboole_0
        | r1_tarski(X2,k1_setfam_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t6_setfam_1.p',t6_setfam_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t6_setfam_1.p',d3_tarski)).

fof(d1_setfam_1,axiom,(
    ! [X1,X2] :
      ( ( X1 != k1_xboole_0
       => ( X2 = k1_setfam_1(X1)
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ! [X4] :
                  ( r2_hidden(X4,X1)
                 => r2_hidden(X3,X4) ) ) ) )
      & ( X1 = k1_xboole_0
       => ( X2 = k1_setfam_1(X1)
        <=> X2 = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t6_setfam_1.p',d1_setfam_1)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ! [X3] :
            ( r2_hidden(X3,X1)
           => r1_tarski(X2,X3) )
       => ( X1 = k1_xboole_0
          | r1_tarski(X2,k1_setfam_1(X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t6_setfam_1])).

fof(c_0_4,plain,(
    ! [X23,X24,X25,X26,X27] :
      ( ( ~ r1_tarski(X23,X24)
        | ~ r2_hidden(X25,X23)
        | r2_hidden(X25,X24) )
      & ( r2_hidden(esk6_2(X26,X27),X26)
        | r1_tarski(X26,X27) )
      & ( ~ r2_hidden(esk6_2(X26,X27),X27)
        | r1_tarski(X26,X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_5,negated_conjecture,(
    ! [X7] :
      ( ( ~ r2_hidden(X7,esk1_0)
        | r1_tarski(esk2_0,X7) )
      & esk1_0 != k1_xboole_0
      & ~ r1_tarski(esk2_0,k1_setfam_1(esk1_0)) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])])).

cnf(c_0_6,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,negated_conjecture,
    ( r1_tarski(esk2_0,X1)
    | ~ r2_hidden(X1,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_8,plain,(
    ! [X10,X11,X12,X13,X14,X16,X19,X20,X21,X22] :
      ( ( ~ r2_hidden(X12,X11)
        | ~ r2_hidden(X13,X10)
        | r2_hidden(X12,X13)
        | X11 != k1_setfam_1(X10)
        | X10 = k1_xboole_0 )
      & ( r2_hidden(esk3_3(X10,X11,X14),X10)
        | r2_hidden(X14,X11)
        | X11 != k1_setfam_1(X10)
        | X10 = k1_xboole_0 )
      & ( ~ r2_hidden(X14,esk3_3(X10,X11,X14))
        | r2_hidden(X14,X11)
        | X11 != k1_setfam_1(X10)
        | X10 = k1_xboole_0 )
      & ( r2_hidden(esk5_2(X10,X16),X10)
        | ~ r2_hidden(esk4_2(X10,X16),X16)
        | X16 = k1_setfam_1(X10)
        | X10 = k1_xboole_0 )
      & ( ~ r2_hidden(esk4_2(X10,X16),esk5_2(X10,X16))
        | ~ r2_hidden(esk4_2(X10,X16),X16)
        | X16 = k1_setfam_1(X10)
        | X10 = k1_xboole_0 )
      & ( r2_hidden(esk4_2(X10,X16),X16)
        | ~ r2_hidden(X19,X10)
        | r2_hidden(esk4_2(X10,X16),X19)
        | X16 = k1_setfam_1(X10)
        | X10 = k1_xboole_0 )
      & ( X21 != k1_setfam_1(X20)
        | X21 = k1_xboole_0
        | X20 != k1_xboole_0 )
      & ( X22 != k1_xboole_0
        | X22 = k1_setfam_1(X20)
        | X20 != k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_setfam_1])])])])])])).

cnf(c_0_9,negated_conjecture,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,esk2_0)
    | ~ r2_hidden(X2,esk1_0) ),
    inference(spm,[status(thm)],[c_0_6,c_0_7])).

cnf(c_0_10,plain,
    ( r2_hidden(esk6_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_11,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),X1)
    | r2_hidden(X3,X2)
    | X1 = k1_xboole_0
    | X2 != k1_setfam_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( r2_hidden(X1,X3)
    | X2 = k1_xboole_0
    | ~ r2_hidden(X1,esk3_3(X2,X3,X1))
    | X3 != k1_setfam_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( r1_tarski(esk2_0,X1)
    | r2_hidden(esk6_2(esk2_0,X1),X2)
    | ~ r2_hidden(X2,esk1_0) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_14,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk3_3(X1,k1_setfam_1(X1),X2),X1)
    | r2_hidden(X2,k1_setfam_1(X1)) ),
    inference(er,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( esk1_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_16,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(X2,k1_setfam_1(X1))
    | ~ r2_hidden(X2,esk3_3(X1,k1_setfam_1(X1),X2)) ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( r1_tarski(esk2_0,X1)
    | r2_hidden(esk6_2(esk2_0,X1),esk3_3(esk1_0,k1_setfam_1(esk1_0),X2))
    | r2_hidden(X2,k1_setfam_1(esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15])).

cnf(c_0_18,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk6_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_19,negated_conjecture,
    ( r1_tarski(esk2_0,X1)
    | r2_hidden(esk6_2(esk2_0,X1),k1_setfam_1(esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( ~ r1_tarski(esk2_0,k1_setfam_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_21,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20]),
    [proof]).
%------------------------------------------------------------------------------
