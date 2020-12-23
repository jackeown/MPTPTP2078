%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : wellord2__t5_wellord2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:18 EDT 2019

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 250 expanded)
%              Number of clauses        :   37 ( 111 expanded)
%              Number of leaves         :    6 (  66 expanded)
%              Depth                    :   12
%              Number of atoms          :  171 (1159 expanded)
%              Number of equality atoms :   30 ( 281 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   33 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d4_relat_2,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r4_relat_2(X1,X2)
        <=> ! [X3,X4] :
              ( ( r2_hidden(X3,X2)
                & r2_hidden(X4,X2)
                & r2_hidden(k4_tarski(X3,X4),X1)
                & r2_hidden(k4_tarski(X4,X3),X1) )
             => X3 = X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord2__t5_wellord2.p',d4_relat_2)).

fof(dt_k1_wellord2,axiom,(
    ! [X1] : v1_relat_1(k1_wellord2(X1)) ),
    file('/export/starexec/sandbox2/benchmark/wellord2__t5_wellord2.p',dt_k1_wellord2)).

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
    file('/export/starexec/sandbox2/benchmark/wellord2__t5_wellord2.p',d1_wellord2)).

fof(t5_wellord2,conjecture,(
    ! [X1] : v4_relat_2(k1_wellord2(X1)) ),
    file('/export/starexec/sandbox2/benchmark/wellord2__t5_wellord2.p',t5_wellord2)).

fof(d12_relat_2,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_2(X1)
      <=> r4_relat_2(X1,k3_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord2__t5_wellord2.p',d12_relat_2)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord2__t5_wellord2.p',d10_xboole_0)).

fof(c_0_6,plain,(
    ! [X19,X20,X21,X22,X23] :
      ( ( ~ r4_relat_2(X19,X20)
        | ~ r2_hidden(X21,X20)
        | ~ r2_hidden(X22,X20)
        | ~ r2_hidden(k4_tarski(X21,X22),X19)
        | ~ r2_hidden(k4_tarski(X22,X21),X19)
        | X21 = X22
        | ~ v1_relat_1(X19) )
      & ( r2_hidden(esk4_2(X19,X23),X23)
        | r4_relat_2(X19,X23)
        | ~ v1_relat_1(X19) )
      & ( r2_hidden(esk5_2(X19,X23),X23)
        | r4_relat_2(X19,X23)
        | ~ v1_relat_1(X19) )
      & ( r2_hidden(k4_tarski(esk4_2(X19,X23),esk5_2(X19,X23)),X19)
        | r4_relat_2(X19,X23)
        | ~ v1_relat_1(X19) )
      & ( r2_hidden(k4_tarski(esk5_2(X19,X23),esk4_2(X19,X23)),X19)
        | r4_relat_2(X19,X23)
        | ~ v1_relat_1(X19) )
      & ( esk4_2(X19,X23) != esk5_2(X19,X23)
        | r4_relat_2(X19,X23)
        | ~ v1_relat_1(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_2])])])])])])).

fof(c_0_7,plain,(
    ! [X26] : v1_relat_1(k1_wellord2(X26)) ),
    inference(variable_rename,[status(thm)],[dt_k1_wellord2])).

fof(c_0_8,plain,(
    ! [X13,X14,X15,X16] :
      ( ( k3_relat_1(X14) = X13
        | X14 != k1_wellord2(X13)
        | ~ v1_relat_1(X14) )
      & ( ~ r2_hidden(k4_tarski(X15,X16),X14)
        | r1_tarski(X15,X16)
        | ~ r2_hidden(X15,X13)
        | ~ r2_hidden(X16,X13)
        | X14 != k1_wellord2(X13)
        | ~ v1_relat_1(X14) )
      & ( ~ r1_tarski(X15,X16)
        | r2_hidden(k4_tarski(X15,X16),X14)
        | ~ r2_hidden(X15,X13)
        | ~ r2_hidden(X16,X13)
        | X14 != k1_wellord2(X13)
        | ~ v1_relat_1(X14) )
      & ( r2_hidden(esk2_2(X13,X14),X13)
        | k3_relat_1(X14) != X13
        | X14 = k1_wellord2(X13)
        | ~ v1_relat_1(X14) )
      & ( r2_hidden(esk3_2(X13,X14),X13)
        | k3_relat_1(X14) != X13
        | X14 = k1_wellord2(X13)
        | ~ v1_relat_1(X14) )
      & ( ~ r2_hidden(k4_tarski(esk2_2(X13,X14),esk3_2(X13,X14)),X14)
        | ~ r1_tarski(esk2_2(X13,X14),esk3_2(X13,X14))
        | k3_relat_1(X14) != X13
        | X14 = k1_wellord2(X13)
        | ~ v1_relat_1(X14) )
      & ( r2_hidden(k4_tarski(esk2_2(X13,X14),esk3_2(X13,X14)),X14)
        | r1_tarski(esk2_2(X13,X14),esk3_2(X13,X14))
        | k3_relat_1(X14) != X13
        | X14 = k1_wellord2(X13)
        | ~ v1_relat_1(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord2])])])])])).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] : v4_relat_2(k1_wellord2(X1)) ),
    inference(assume_negation,[status(cth)],[t5_wellord2])).

fof(c_0_10,plain,(
    ! [X12] :
      ( ( ~ v4_relat_2(X12)
        | r4_relat_2(X12,k3_relat_1(X12))
        | ~ v1_relat_1(X12) )
      & ( ~ r4_relat_2(X12,k3_relat_1(X12))
        | v4_relat_2(X12)
        | ~ v1_relat_1(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_relat_2])])])).

cnf(c_0_11,plain,
    ( r2_hidden(esk5_2(X1,X2),X2)
    | r4_relat_2(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,plain,
    ( v1_relat_1(k1_wellord2(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( k3_relat_1(X1) = X2
    | X1 != k1_wellord2(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_14,negated_conjecture,(
    ~ v4_relat_2(k1_wellord2(esk1_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

cnf(c_0_15,plain,
    ( v4_relat_2(X1)
    | ~ r4_relat_2(X1,k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( r4_relat_2(k1_wellord2(X1),X2)
    | r2_hidden(esk5_2(k1_wellord2(X1),X2),X2) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_17,plain,
    ( k3_relat_1(k1_wellord2(X1)) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_13]),c_0_12])])).

cnf(c_0_18,plain,
    ( r2_hidden(esk4_2(X1,X2),X2)
    | r4_relat_2(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_19,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,X4)
    | ~ r2_hidden(X2,X4)
    | X3 != k1_wellord2(X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_20,negated_conjecture,
    ( ~ v4_relat_2(k1_wellord2(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( r2_hidden(esk5_2(k1_wellord2(X1),X1),X1)
    | v4_relat_2(k1_wellord2(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_17]),c_0_12])])).

cnf(c_0_22,plain,
    ( r4_relat_2(k1_wellord2(X1),X2)
    | r2_hidden(esk4_2(k1_wellord2(X1),X2),X2) ),
    inference(spm,[status(thm)],[c_0_18,c_0_12])).

cnf(c_0_23,plain,
    ( r2_hidden(k4_tarski(esk4_2(X1,X2),esk5_2(X1,X2)),X1)
    | r4_relat_2(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X2),k1_wellord2(X3))
    | ~ r2_hidden(X2,X3)
    | ~ r2_hidden(X1,X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_19]),c_0_12])])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk5_2(k1_wellord2(esk1_0),esk1_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_26,plain,
    ( r2_hidden(esk4_2(k1_wellord2(X1),X1),X1)
    | v4_relat_2(k1_wellord2(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_22]),c_0_17]),c_0_17]),c_0_12])])).

cnf(c_0_27,plain,
    ( r4_relat_2(k1_wellord2(X1),X2)
    | r2_hidden(k4_tarski(esk4_2(k1_wellord2(X1),X2),esk5_2(k1_wellord2(X1),X2)),k1_wellord2(X1)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_12])).

cnf(c_0_28,plain,
    ( r2_hidden(k4_tarski(esk5_2(X1,X2),esk4_2(X1,X2)),X1)
    | r4_relat_2(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_29,negated_conjecture,
    ( r1_tarski(X1,esk5_2(k1_wellord2(esk1_0),esk1_0))
    | ~ r2_hidden(k4_tarski(X1,esk5_2(k1_wellord2(esk1_0),esk1_0)),k1_wellord2(esk1_0))
    | ~ r2_hidden(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk4_2(k1_wellord2(esk1_0),esk1_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_26])).

cnf(c_0_31,plain,
    ( r2_hidden(k4_tarski(esk4_2(k1_wellord2(X1),X1),esk5_2(k1_wellord2(X1),X1)),k1_wellord2(X1))
    | v4_relat_2(k1_wellord2(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_27]),c_0_17]),c_0_17]),c_0_12])])).

cnf(c_0_32,plain,
    ( r4_relat_2(k1_wellord2(X1),X2)
    | r2_hidden(k4_tarski(esk5_2(k1_wellord2(X1),X2),esk4_2(k1_wellord2(X1),X2)),k1_wellord2(X1)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_12])).

fof(c_0_33,plain,(
    ! [X10,X11] :
      ( ( r1_tarski(X10,X11)
        | X10 != X11 )
      & ( r1_tarski(X11,X10)
        | X10 != X11 )
      & ( ~ r1_tarski(X10,X11)
        | ~ r1_tarski(X11,X10)
        | X10 = X11 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(esk4_2(k1_wellord2(esk1_0),esk1_0),esk5_2(k1_wellord2(esk1_0),esk1_0))
    | ~ r2_hidden(k4_tarski(esk4_2(k1_wellord2(esk1_0),esk1_0),esk5_2(k1_wellord2(esk1_0),esk1_0)),k1_wellord2(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(k4_tarski(esk4_2(k1_wellord2(esk1_0),esk1_0),esk5_2(k1_wellord2(esk1_0),esk1_0)),k1_wellord2(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_31])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(X1,esk4_2(k1_wellord2(esk1_0),esk1_0))
    | ~ r2_hidden(k4_tarski(X1,esk4_2(k1_wellord2(esk1_0),esk1_0)),k1_wellord2(esk1_0))
    | ~ r2_hidden(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_30])).

cnf(c_0_37,plain,
    ( r2_hidden(k4_tarski(esk5_2(k1_wellord2(X1),X1),esk4_2(k1_wellord2(X1),X1)),k1_wellord2(X1))
    | v4_relat_2(k1_wellord2(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_32]),c_0_17]),c_0_17]),c_0_12])])).

cnf(c_0_38,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_39,negated_conjecture,
    ( r1_tarski(esk4_2(k1_wellord2(esk1_0),esk1_0),esk5_2(k1_wellord2(esk1_0),esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_35])])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(esk5_2(k1_wellord2(esk1_0),esk1_0),esk4_2(k1_wellord2(esk1_0),esk1_0))
    | ~ r2_hidden(k4_tarski(esk5_2(k1_wellord2(esk1_0),esk1_0),esk4_2(k1_wellord2(esk1_0),esk1_0)),k1_wellord2(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_25])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(k4_tarski(esk5_2(k1_wellord2(esk1_0),esk1_0),esk4_2(k1_wellord2(esk1_0),esk1_0)),k1_wellord2(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_37])).

cnf(c_0_42,plain,
    ( r4_relat_2(X1,X2)
    | esk4_2(X1,X2) != esk5_2(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_43,negated_conjecture,
    ( esk5_2(k1_wellord2(esk1_0),esk1_0) = esk4_2(k1_wellord2(esk1_0),esk1_0)
    | ~ r1_tarski(esk5_2(k1_wellord2(esk1_0),esk1_0),esk4_2(k1_wellord2(esk1_0),esk1_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(esk5_2(k1_wellord2(esk1_0),esk1_0),esk4_2(k1_wellord2(esk1_0),esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_41])])).

cnf(c_0_45,plain,
    ( r4_relat_2(k1_wellord2(X1),X2)
    | esk5_2(k1_wellord2(X1),X2) != esk4_2(k1_wellord2(X1),X2) ),
    inference(spm,[status(thm)],[c_0_42,c_0_12])).

cnf(c_0_46,negated_conjecture,
    ( esk5_2(k1_wellord2(esk1_0),esk1_0) = esk4_2(k1_wellord2(esk1_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_44])])).

cnf(c_0_47,plain,
    ( v4_relat_2(k1_wellord2(X1))
    | ~ r4_relat_2(k1_wellord2(X1),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_17]),c_0_12])])).

cnf(c_0_48,negated_conjecture,
    ( r4_relat_2(k1_wellord2(esk1_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_49,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_20]),
    [proof]).
%------------------------------------------------------------------------------
