%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : zfmisc_1__t35_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:42:05 EDT 2019

% Result     : Theorem 151.25s
% Output     : CNFRefutation 151.25s
% Verified   : 
% Statistics : Number of formulae       :   33 ( 115 expanded)
%              Number of clauses        :   26 (  57 expanded)
%              Number of leaves         :    3 (  26 expanded)
%              Depth                    :   14
%              Number of atoms          :  110 ( 552 expanded)
%              Number of equality atoms :   51 ( 303 expanded)
%              Maximal formula depth    :   23 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t35_zfmisc_1,conjecture,(
    ! [X1,X2] : k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(k4_tarski(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t35_zfmisc_1.p',t35_zfmisc_1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t35_zfmisc_1.p',d1_tarski)).

fof(d2_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_zfmisc_1(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ? [X5,X6] :
              ( r2_hidden(X5,X1)
              & r2_hidden(X6,X2)
              & X4 = k4_tarski(X5,X6) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t35_zfmisc_1.p',d2_zfmisc_1)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2] : k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(k4_tarski(X1,X2)) ),
    inference(assume_negation,[status(cth)],[t35_zfmisc_1])).

fof(c_0_4,plain,(
    ! [X11,X12,X13,X14,X15,X16] :
      ( ( ~ r2_hidden(X13,X12)
        | X13 = X11
        | X12 != k1_tarski(X11) )
      & ( X14 != X11
        | r2_hidden(X14,X12)
        | X12 != k1_tarski(X11) )
      & ( ~ r2_hidden(esk3_2(X15,X16),X16)
        | esk3_2(X15,X16) != X15
        | X16 = k1_tarski(X15) )
      & ( r2_hidden(esk3_2(X15,X16),X16)
        | esk3_2(X15,X16) = X15
        | X16 = k1_tarski(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_5,negated_conjecture,(
    k2_zfmisc_1(k1_tarski(esk1_0),k1_tarski(esk2_0)) != k1_tarski(k4_tarski(esk1_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

fof(c_0_6,plain,(
    ! [X18,X19,X20,X21,X24,X25,X26,X27,X28,X29,X31,X32] :
      ( ( r2_hidden(esk4_4(X18,X19,X20,X21),X18)
        | ~ r2_hidden(X21,X20)
        | X20 != k2_zfmisc_1(X18,X19) )
      & ( r2_hidden(esk5_4(X18,X19,X20,X21),X19)
        | ~ r2_hidden(X21,X20)
        | X20 != k2_zfmisc_1(X18,X19) )
      & ( X21 = k4_tarski(esk4_4(X18,X19,X20,X21),esk5_4(X18,X19,X20,X21))
        | ~ r2_hidden(X21,X20)
        | X20 != k2_zfmisc_1(X18,X19) )
      & ( ~ r2_hidden(X25,X18)
        | ~ r2_hidden(X26,X19)
        | X24 != k4_tarski(X25,X26)
        | r2_hidden(X24,X20)
        | X20 != k2_zfmisc_1(X18,X19) )
      & ( ~ r2_hidden(esk6_3(X27,X28,X29),X29)
        | ~ r2_hidden(X31,X27)
        | ~ r2_hidden(X32,X28)
        | esk6_3(X27,X28,X29) != k4_tarski(X31,X32)
        | X29 = k2_zfmisc_1(X27,X28) )
      & ( r2_hidden(esk7_3(X27,X28,X29),X27)
        | r2_hidden(esk6_3(X27,X28,X29),X29)
        | X29 = k2_zfmisc_1(X27,X28) )
      & ( r2_hidden(esk8_3(X27,X28,X29),X28)
        | r2_hidden(esk6_3(X27,X28,X29),X29)
        | X29 = k2_zfmisc_1(X27,X28) )
      & ( esk6_3(X27,X28,X29) = k4_tarski(esk7_3(X27,X28,X29),esk8_3(X27,X28,X29))
        | r2_hidden(esk6_3(X27,X28,X29),X29)
        | X29 = k2_zfmisc_1(X27,X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).

cnf(c_0_7,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,negated_conjecture,
    ( k2_zfmisc_1(k1_tarski(esk1_0),k1_tarski(esk2_0)) != k1_tarski(k4_tarski(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( r2_hidden(esk7_3(X1,X2,X3),X1)
    | r2_hidden(esk6_3(X1,X2,X3),X3)
    | X3 = k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k1_tarski(X2)) ),
    inference(er,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( r2_hidden(esk6_3(k1_tarski(esk1_0),k1_tarski(esk2_0),k1_tarski(k4_tarski(esk1_0,esk2_0))),k1_tarski(k4_tarski(esk1_0,esk2_0)))
    | r2_hidden(esk7_3(k1_tarski(esk1_0),k1_tarski(esk2_0),k1_tarski(k4_tarski(esk1_0,esk2_0))),k1_tarski(esk1_0)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_9])])).

cnf(c_0_12,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_13,plain,
    ( r2_hidden(esk8_3(X1,X2,X3),X2)
    | r2_hidden(esk6_3(X1,X2,X3),X3)
    | X3 = k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_14,plain,
    ( X3 = k2_zfmisc_1(X1,X2)
    | ~ r2_hidden(esk6_3(X1,X2,X3),X3)
    | ~ r2_hidden(X4,X1)
    | ~ r2_hidden(X5,X2)
    | esk6_3(X1,X2,X3) != k4_tarski(X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_15,negated_conjecture,
    ( esk6_3(k1_tarski(esk1_0),k1_tarski(esk2_0),k1_tarski(k4_tarski(esk1_0,esk2_0))) = k4_tarski(esk1_0,esk2_0)
    | r2_hidden(esk7_3(k1_tarski(esk1_0),k1_tarski(esk2_0),k1_tarski(k4_tarski(esk1_0,esk2_0))),k1_tarski(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,k1_tarski(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_12])])).

cnf(c_0_17,negated_conjecture,
    ( r2_hidden(esk6_3(k1_tarski(esk1_0),k1_tarski(esk2_0),k1_tarski(k4_tarski(esk1_0,esk2_0))),k1_tarski(k4_tarski(esk1_0,esk2_0)))
    | r2_hidden(esk8_3(k1_tarski(esk1_0),k1_tarski(esk2_0),k1_tarski(k4_tarski(esk1_0,esk2_0))),k1_tarski(esk2_0)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_13])])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(esk7_3(k1_tarski(esk1_0),k1_tarski(esk2_0),k1_tarski(k4_tarski(esk1_0,esk2_0))),k1_tarski(esk1_0))
    | k4_tarski(esk1_0,esk2_0) != k4_tarski(X1,X2)
    | ~ r2_hidden(X2,k1_tarski(esk2_0))
    | ~ r2_hidden(X1,k1_tarski(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16])]),c_0_8])).

cnf(c_0_19,negated_conjecture,
    ( esk6_3(k1_tarski(esk1_0),k1_tarski(esk2_0),k1_tarski(k4_tarski(esk1_0,esk2_0))) = k4_tarski(esk1_0,esk2_0)
    | r2_hidden(esk8_3(k1_tarski(esk1_0),k1_tarski(esk2_0),k1_tarski(k4_tarski(esk1_0,esk2_0))),k1_tarski(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_10,c_0_17])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(esk7_3(k1_tarski(esk1_0),k1_tarski(esk2_0),k1_tarski(k4_tarski(esk1_0,esk2_0))),k1_tarski(esk1_0))
    | k4_tarski(esk1_0,esk2_0) != k4_tarski(X1,esk2_0)
    | ~ r2_hidden(X1,k1_tarski(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(esk8_3(k1_tarski(esk1_0),k1_tarski(esk2_0),k1_tarski(k4_tarski(esk1_0,esk2_0))),k1_tarski(esk2_0))
    | k4_tarski(esk1_0,esk2_0) != k4_tarski(X1,X2)
    | ~ r2_hidden(X2,k1_tarski(esk2_0))
    | ~ r2_hidden(X1,k1_tarski(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_19]),c_0_16])]),c_0_8])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk7_3(k1_tarski(esk1_0),k1_tarski(esk2_0),k1_tarski(k4_tarski(esk1_0,esk2_0))),k1_tarski(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(esk8_3(k1_tarski(esk1_0),k1_tarski(esk2_0),k1_tarski(k4_tarski(esk1_0,esk2_0))),k1_tarski(esk2_0))
    | k4_tarski(esk1_0,esk2_0) != k4_tarski(X1,esk2_0)
    | ~ r2_hidden(X1,k1_tarski(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_16])).

cnf(c_0_24,plain,
    ( esk6_3(X1,X2,X3) = k4_tarski(esk7_3(X1,X2,X3),esk8_3(X1,X2,X3))
    | r2_hidden(esk6_3(X1,X2,X3),X3)
    | X3 = k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_25,negated_conjecture,
    ( esk7_3(k1_tarski(esk1_0),k1_tarski(esk2_0),k1_tarski(k4_tarski(esk1_0,esk2_0))) = esk1_0 ),
    inference(spm,[status(thm)],[c_0_10,c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk8_3(k1_tarski(esk1_0),k1_tarski(esk2_0),k1_tarski(k4_tarski(esk1_0,esk2_0))),k1_tarski(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_16])).

cnf(c_0_27,negated_conjecture,
    ( k4_tarski(esk1_0,esk8_3(k1_tarski(esk1_0),k1_tarski(esk2_0),k1_tarski(k4_tarski(esk1_0,esk2_0)))) = esk6_3(k1_tarski(esk1_0),k1_tarski(esk2_0),k1_tarski(k4_tarski(esk1_0,esk2_0)))
    | r2_hidden(esk6_3(k1_tarski(esk1_0),k1_tarski(esk2_0),k1_tarski(k4_tarski(esk1_0,esk2_0))),k1_tarski(k4_tarski(esk1_0,esk2_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_8])).

cnf(c_0_28,negated_conjecture,
    ( esk8_3(k1_tarski(esk1_0),k1_tarski(esk2_0),k1_tarski(k4_tarski(esk1_0,esk2_0))) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_10,c_0_26])).

cnf(c_0_29,negated_conjecture,
    ( esk6_3(k1_tarski(esk1_0),k1_tarski(esk2_0),k1_tarski(k4_tarski(esk1_0,esk2_0))) = k4_tarski(esk1_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_28]),c_0_10])).

cnf(c_0_30,negated_conjecture,
    ( k4_tarski(esk1_0,esk2_0) != k4_tarski(X1,X2)
    | ~ r2_hidden(X2,k1_tarski(esk2_0))
    | ~ r2_hidden(X1,k1_tarski(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_29]),c_0_16])]),c_0_8])).

cnf(c_0_31,negated_conjecture,
    ( k4_tarski(esk1_0,esk2_0) != k4_tarski(X1,esk2_0)
    | ~ r2_hidden(X1,k1_tarski(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_16])).

cnf(c_0_32,negated_conjecture,
    ( $false ),
    inference(spm,[status(thm)],[c_0_31,c_0_16]),
    [proof]).
%------------------------------------------------------------------------------
