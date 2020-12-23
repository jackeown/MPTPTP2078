%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : relset_1__t28_relset_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:08 EDT 2019

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   26 (  54 expanded)
%              Number of clauses        :   15 (  23 expanded)
%              Number of leaves         :    5 (  14 expanded)
%              Depth                    :    7
%              Number of atoms          :   89 ( 172 expanded)
%              Number of equality atoms :   17 (  29 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t28_relset_1,conjecture,(
    ! [X1] : r1_tarski(k6_relat_1(X1),k2_zfmisc_1(X1,X1)) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t28_relset_1.p',t28_relset_1)).

fof(d10_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( X2 = k6_relat_1(X1)
      <=> ! [X3,X4] :
            ( r2_hidden(k4_tarski(X3,X4),X2)
          <=> ( r2_hidden(X3,X1)
              & X3 = X4 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t28_relset_1.p',d10_relat_1)).

fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t28_relset_1.p',dt_k6_relat_1)).

fof(d3_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r1_tarski(X1,X2)
        <=> ! [X3,X4] :
              ( r2_hidden(k4_tarski(X3,X4),X1)
             => r2_hidden(k4_tarski(X3,X4),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t28_relset_1.p',d3_relat_1)).

fof(t106_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t28_relset_1.p',t106_zfmisc_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] : r1_tarski(k6_relat_1(X1),k2_zfmisc_1(X1,X1)) ),
    inference(assume_negation,[status(cth)],[t28_relset_1])).

fof(c_0_6,plain,(
    ! [X8,X9,X10,X11,X12,X13] :
      ( ( r2_hidden(X10,X8)
        | ~ r2_hidden(k4_tarski(X10,X11),X9)
        | X9 != k6_relat_1(X8)
        | ~ v1_relat_1(X9) )
      & ( X10 = X11
        | ~ r2_hidden(k4_tarski(X10,X11),X9)
        | X9 != k6_relat_1(X8)
        | ~ v1_relat_1(X9) )
      & ( ~ r2_hidden(X12,X8)
        | X12 != X13
        | r2_hidden(k4_tarski(X12,X13),X9)
        | X9 != k6_relat_1(X8)
        | ~ v1_relat_1(X9) )
      & ( ~ r2_hidden(k4_tarski(esk2_2(X8,X9),esk3_2(X8,X9)),X9)
        | ~ r2_hidden(esk2_2(X8,X9),X8)
        | esk2_2(X8,X9) != esk3_2(X8,X9)
        | X9 = k6_relat_1(X8)
        | ~ v1_relat_1(X9) )
      & ( r2_hidden(esk2_2(X8,X9),X8)
        | r2_hidden(k4_tarski(esk2_2(X8,X9),esk3_2(X8,X9)),X9)
        | X9 = k6_relat_1(X8)
        | ~ v1_relat_1(X9) )
      & ( esk2_2(X8,X9) = esk3_2(X8,X9)
        | r2_hidden(k4_tarski(esk2_2(X8,X9),esk3_2(X8,X9)),X9)
        | X9 = k6_relat_1(X8)
        | ~ v1_relat_1(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_relat_1])])])])])])).

fof(c_0_7,plain,(
    ! [X23] : v1_relat_1(k6_relat_1(X23)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

fof(c_0_8,negated_conjecture,(
    ~ r1_tarski(k6_relat_1(esk1_0),k2_zfmisc_1(esk1_0,esk1_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

fof(c_0_9,plain,(
    ! [X16,X17,X18,X19,X20] :
      ( ( ~ r1_tarski(X16,X17)
        | ~ r2_hidden(k4_tarski(X18,X19),X16)
        | r2_hidden(k4_tarski(X18,X19),X17)
        | ~ v1_relat_1(X16) )
      & ( r2_hidden(k4_tarski(esk4_2(X16,X20),esk5_2(X16,X20)),X16)
        | r1_tarski(X16,X20)
        | ~ v1_relat_1(X16) )
      & ( ~ r2_hidden(k4_tarski(esk4_2(X16,X20),esk5_2(X16,X20)),X20)
        | r1_tarski(X16,X20)
        | ~ v1_relat_1(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_relat_1])])])])])])).

cnf(c_0_10,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X3 != k6_relat_1(X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( ~ r1_tarski(k6_relat_1(esk1_0),k2_zfmisc_1(esk1_0,esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( r2_hidden(k4_tarski(esk4_2(X1,X2),esk5_2(X1,X2)),X1)
    | r1_tarski(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(k4_tarski(esk4_2(X1,X2),esk5_2(X1,X2)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X1,X2),k6_relat_1(X3)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_10]),c_0_11])])).

cnf(c_0_16,negated_conjecture,
    ( r2_hidden(k4_tarski(esk4_2(k6_relat_1(esk1_0),k2_zfmisc_1(esk1_0,esk1_0)),esk5_2(k6_relat_1(esk1_0),k2_zfmisc_1(esk1_0,esk1_0))),k6_relat_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_11])])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),X4)
    | X4 != k6_relat_1(X2)
    | ~ v1_relat_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_18,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk4_2(k6_relat_1(esk1_0),k2_zfmisc_1(esk1_0,esk1_0)),esk5_2(k6_relat_1(esk1_0),k2_zfmisc_1(esk1_0,esk1_0))),k2_zfmisc_1(esk1_0,esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_14]),c_0_11])])).

cnf(c_0_19,negated_conjecture,
    ( esk5_2(k6_relat_1(esk1_0),k2_zfmisc_1(esk1_0,esk1_0)) = esk4_2(k6_relat_1(esk1_0),k2_zfmisc_1(esk1_0,esk1_0)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

fof(c_0_20,plain,(
    ! [X26,X27,X28,X29] :
      ( ( r2_hidden(X26,X28)
        | ~ r2_hidden(k4_tarski(X26,X27),k2_zfmisc_1(X28,X29)) )
      & ( r2_hidden(X27,X29)
        | ~ r2_hidden(k4_tarski(X26,X27),k2_zfmisc_1(X28,X29)) )
      & ( ~ r2_hidden(X26,X28)
        | ~ r2_hidden(X27,X29)
        | r2_hidden(k4_tarski(X26,X27),k2_zfmisc_1(X28,X29)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_zfmisc_1])])])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k6_relat_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_17]),c_0_11])])).

cnf(c_0_22,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk4_2(k6_relat_1(esk1_0),k2_zfmisc_1(esk1_0,esk1_0)),esk4_2(k6_relat_1(esk1_0),k2_zfmisc_1(esk1_0,esk1_0))),k2_zfmisc_1(esk1_0,esk1_0)) ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_23,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk4_2(k6_relat_1(esk1_0),k2_zfmisc_1(esk1_0,esk1_0)),esk1_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_16])).

cnf(c_0_25,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])]),
    [proof]).
%------------------------------------------------------------------------------
