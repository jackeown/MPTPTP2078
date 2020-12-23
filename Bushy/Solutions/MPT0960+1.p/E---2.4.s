%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : wellord2__t33_wellord2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:17 EDT 2019

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   29 (  68 expanded)
%              Number of clauses        :   16 (  29 expanded)
%              Number of leaves         :    6 (  18 expanded)
%              Depth                    :    8
%              Number of atoms          :  109 ( 223 expanded)
%              Number of equality atoms :   17 (  34 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   33 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t33_wellord2,conjecture,(
    ! [X1] : r1_tarski(k1_wellord2(X1),k2_zfmisc_1(X1,X1)) ),
    file('/export/starexec/sandbox/benchmark/wellord2__t33_wellord2.p',t33_wellord2)).

fof(d3_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r1_tarski(X1,X2)
        <=> ! [X3,X4] :
              ( r2_hidden(k4_tarski(X3,X4),X1)
             => r2_hidden(k4_tarski(X3,X4),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord2__t33_wellord2.p',d3_relat_1)).

fof(dt_k1_wellord2,axiom,(
    ! [X1] : v1_relat_1(k1_wellord2(X1)) ),
    file('/export/starexec/sandbox/benchmark/wellord2__t33_wellord2.p',dt_k1_wellord2)).

fof(d1_wellord2,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( X2 = k1_wellord2(X1)
      <=> ( k3_relat_1(X2) = X1
          & ! [X3,X4] :
              ( ( r2_hidden(X3,X1)
                & r2_hidden(X4,X1) )
             => ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> r1_tarski(X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord2__t33_wellord2.p',d1_wellord2)).

fof(t30_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X1,X2),X3)
       => ( r2_hidden(X1,k3_relat_1(X3))
          & r2_hidden(X2,k3_relat_1(X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord2__t33_wellord2.p',t30_relat_1)).

fof(t106_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord2__t33_wellord2.p',t106_zfmisc_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] : r1_tarski(k1_wellord2(X1),k2_zfmisc_1(X1,X1)) ),
    inference(assume_negation,[status(cth)],[t33_wellord2])).

fof(c_0_7,plain,(
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

fof(c_0_8,plain,(
    ! [X23] : v1_relat_1(k1_wellord2(X23)) ),
    inference(variable_rename,[status(thm)],[dt_k1_wellord2])).

fof(c_0_9,negated_conjecture,(
    ~ r1_tarski(k1_wellord2(esk1_0),k2_zfmisc_1(esk1_0,esk1_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

cnf(c_0_10,plain,
    ( r2_hidden(k4_tarski(esk4_2(X1,X2),esk5_2(X1,X2)),X1)
    | r1_tarski(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( v1_relat_1(k1_wellord2(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_12,plain,(
    ! [X10,X11,X12,X13] :
      ( ( k3_relat_1(X11) = X10
        | X11 != k1_wellord2(X10)
        | ~ v1_relat_1(X11) )
      & ( ~ r2_hidden(k4_tarski(X12,X13),X11)
        | r1_tarski(X12,X13)
        | ~ r2_hidden(X12,X10)
        | ~ r2_hidden(X13,X10)
        | X11 != k1_wellord2(X10)
        | ~ v1_relat_1(X11) )
      & ( ~ r1_tarski(X12,X13)
        | r2_hidden(k4_tarski(X12,X13),X11)
        | ~ r2_hidden(X12,X10)
        | ~ r2_hidden(X13,X10)
        | X11 != k1_wellord2(X10)
        | ~ v1_relat_1(X11) )
      & ( r2_hidden(esk2_2(X10,X11),X10)
        | k3_relat_1(X11) != X10
        | X11 = k1_wellord2(X10)
        | ~ v1_relat_1(X11) )
      & ( r2_hidden(esk3_2(X10,X11),X10)
        | k3_relat_1(X11) != X10
        | X11 = k1_wellord2(X10)
        | ~ v1_relat_1(X11) )
      & ( ~ r2_hidden(k4_tarski(esk2_2(X10,X11),esk3_2(X10,X11)),X11)
        | ~ r1_tarski(esk2_2(X10,X11),esk3_2(X10,X11))
        | k3_relat_1(X11) != X10
        | X11 = k1_wellord2(X10)
        | ~ v1_relat_1(X11) )
      & ( r2_hidden(k4_tarski(esk2_2(X10,X11),esk3_2(X10,X11)),X11)
        | r1_tarski(esk2_2(X10,X11),esk3_2(X10,X11))
        | k3_relat_1(X11) != X10
        | X11 = k1_wellord2(X10)
        | ~ v1_relat_1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord2])])])])])).

fof(c_0_13,plain,(
    ! [X36,X37,X38] :
      ( ( r2_hidden(X36,k3_relat_1(X38))
        | ~ r2_hidden(k4_tarski(X36,X37),X38)
        | ~ v1_relat_1(X38) )
      & ( r2_hidden(X37,k3_relat_1(X38))
        | ~ r2_hidden(k4_tarski(X36,X37),X38)
        | ~ v1_relat_1(X38) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_relat_1])])])).

cnf(c_0_14,negated_conjecture,
    ( ~ r1_tarski(k1_wellord2(esk1_0),k2_zfmisc_1(esk1_0,esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( r2_hidden(k4_tarski(esk4_2(k1_wellord2(X1),X2),esk5_2(k1_wellord2(X1),X2)),k1_wellord2(X1))
    | r1_tarski(k1_wellord2(X1),X2) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_16,plain,
    ( k3_relat_1(X1) = X2
    | X1 != k1_wellord2(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_17,plain,(
    ! [X27,X28,X29,X30] :
      ( ( r2_hidden(X27,X29)
        | ~ r2_hidden(k4_tarski(X27,X28),k2_zfmisc_1(X29,X30)) )
      & ( r2_hidden(X28,X30)
        | ~ r2_hidden(k4_tarski(X27,X28),k2_zfmisc_1(X29,X30)) )
      & ( ~ r2_hidden(X27,X29)
        | ~ r2_hidden(X28,X30)
        | r2_hidden(k4_tarski(X27,X28),k2_zfmisc_1(X29,X30)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_zfmisc_1])])])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,k3_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(k4_tarski(esk4_2(k1_wellord2(esk1_0),k2_zfmisc_1(esk1_0,esk1_0)),esk5_2(k1_wellord2(esk1_0),k2_zfmisc_1(esk1_0,esk1_0))),k1_wellord2(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_20,plain,
    ( k3_relat_1(k1_wellord2(X1)) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_16]),c_0_11])])).

cnf(c_0_21,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk5_2(k1_wellord2(esk1_0),k2_zfmisc_1(esk1_0,esk1_0)),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20]),c_0_11])])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,k3_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk5_2(k1_wellord2(esk1_0),k2_zfmisc_1(esk1_0,esk1_0))),k2_zfmisc_1(X2,esk1_0))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk4_2(k1_wellord2(esk1_0),k2_zfmisc_1(esk1_0,esk1_0)),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_19]),c_0_20]),c_0_11])])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(k4_tarski(esk4_2(X1,X2),esk5_2(X1,X2)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(k4_tarski(esk4_2(k1_wellord2(esk1_0),k2_zfmisc_1(esk1_0,esk1_0)),esk5_2(k1_wellord2(esk1_0),k2_zfmisc_1(esk1_0,esk1_0))),k2_zfmisc_1(esk1_0,esk1_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_28,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_11])]),c_0_14]),
    [proof]).
%------------------------------------------------------------------------------
