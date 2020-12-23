%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : wellord1__t21_wellord1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:11 EDT 2019

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   37 (  74 expanded)
%              Number of clauses        :   24 (  33 expanded)
%              Number of leaves         :    6 (  17 expanded)
%              Depth                    :   10
%              Number of atoms          :  129 ( 262 expanded)
%              Number of equality atoms :   31 (  55 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t21_wellord1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => r1_tarski(k1_wellord1(k2_wellord1(X3,X1),X2),k1_wellord1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t21_wellord1.p',t21_wellord1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t21_wellord1.p',d4_xboole_0)).

fof(d6_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] : k2_wellord1(X1,X2) = k3_xboole_0(X1,k2_zfmisc_1(X2,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t21_wellord1.p',d6_wellord1)).

fof(d1_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( X3 = k1_wellord1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ( X4 != X2
                & r2_hidden(k4_tarski(X4,X2),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t21_wellord1.p',d1_wellord1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t21_wellord1.p',d3_tarski)).

fof(dt_k2_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k2_wellord1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t21_wellord1.p',dt_k2_wellord1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => r1_tarski(k1_wellord1(k2_wellord1(X3,X1),X2),k1_wellord1(X3,X2)) ) ),
    inference(assume_negation,[status(cth)],[t21_wellord1])).

fof(c_0_7,plain,(
    ! [X26,X27,X28,X29,X30,X31,X32,X33] :
      ( ( r2_hidden(X29,X26)
        | ~ r2_hidden(X29,X28)
        | X28 != k3_xboole_0(X26,X27) )
      & ( r2_hidden(X29,X27)
        | ~ r2_hidden(X29,X28)
        | X28 != k3_xboole_0(X26,X27) )
      & ( ~ r2_hidden(X30,X26)
        | ~ r2_hidden(X30,X27)
        | r2_hidden(X30,X28)
        | X28 != k3_xboole_0(X26,X27) )
      & ( ~ r2_hidden(esk6_3(X31,X32,X33),X33)
        | ~ r2_hidden(esk6_3(X31,X32,X33),X31)
        | ~ r2_hidden(esk6_3(X31,X32,X33),X32)
        | X33 = k3_xboole_0(X31,X32) )
      & ( r2_hidden(esk6_3(X31,X32,X33),X31)
        | r2_hidden(esk6_3(X31,X32,X33),X33)
        | X33 = k3_xboole_0(X31,X32) )
      & ( r2_hidden(esk6_3(X31,X32,X33),X32)
        | r2_hidden(esk6_3(X31,X32,X33),X33)
        | X33 = k3_xboole_0(X31,X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

fof(c_0_8,plain,(
    ! [X35,X36] :
      ( ~ v1_relat_1(X35)
      | k2_wellord1(X35,X36) = k3_xboole_0(X35,k2_zfmisc_1(X36,X36)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_wellord1])])])).

fof(c_0_9,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & ~ r1_tarski(k1_wellord1(k2_wellord1(esk3_0,esk1_0),esk2_0),k1_wellord1(esk3_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

fof(c_0_10,plain,(
    ! [X12,X13,X14,X15,X16,X17,X18] :
      ( ( X15 != X13
        | ~ r2_hidden(X15,X14)
        | X14 != k1_wellord1(X12,X13)
        | ~ v1_relat_1(X12) )
      & ( r2_hidden(k4_tarski(X15,X13),X12)
        | ~ r2_hidden(X15,X14)
        | X14 != k1_wellord1(X12,X13)
        | ~ v1_relat_1(X12) )
      & ( X16 = X13
        | ~ r2_hidden(k4_tarski(X16,X13),X12)
        | r2_hidden(X16,X14)
        | X14 != k1_wellord1(X12,X13)
        | ~ v1_relat_1(X12) )
      & ( ~ r2_hidden(esk4_3(X12,X17,X18),X18)
        | esk4_3(X12,X17,X18) = X17
        | ~ r2_hidden(k4_tarski(esk4_3(X12,X17,X18),X17),X12)
        | X18 = k1_wellord1(X12,X17)
        | ~ v1_relat_1(X12) )
      & ( esk4_3(X12,X17,X18) != X17
        | r2_hidden(esk4_3(X12,X17,X18),X18)
        | X18 = k1_wellord1(X12,X17)
        | ~ v1_relat_1(X12) )
      & ( r2_hidden(k4_tarski(esk4_3(X12,X17,X18),X17),X12)
        | r2_hidden(esk4_3(X12,X17,X18),X18)
        | X18 = k1_wellord1(X12,X17)
        | ~ v1_relat_1(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord1])])])])])])).

fof(c_0_11,plain,(
    ! [X20,X21,X22,X23,X24] :
      ( ( ~ r1_tarski(X20,X21)
        | ~ r2_hidden(X22,X20)
        | r2_hidden(X22,X21) )
      & ( r2_hidden(esk5_2(X23,X24),X23)
        | r1_tarski(X23,X24) )
      & ( ~ r2_hidden(esk5_2(X23,X24),X24)
        | r1_tarski(X23,X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_12,plain,(
    ! [X37,X38] :
      ( ~ v1_relat_1(X37)
      | v1_relat_1(k2_wellord1(X37,X38)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_wellord1])])).

cnf(c_0_13,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,plain,
    ( k2_wellord1(X1,X2) = k3_xboole_0(X1,k2_zfmisc_1(X2,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,X4)
    | X4 != k1_wellord1(X3,X2)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,negated_conjecture,
    ( ~ r1_tarski(k1_wellord1(k2_wellord1(esk3_0,esk1_0),esk2_0),k1_wellord1(esk3_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_18,plain,
    ( r2_hidden(esk5_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( v1_relat_1(k2_wellord1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_13])).

cnf(c_0_21,negated_conjecture,
    ( k3_xboole_0(esk3_0,k2_zfmisc_1(X1,X1)) = k2_wellord1(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_22,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,k1_wellord1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(er,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(esk5_2(k1_wellord1(k2_wellord1(esk3_0,esk1_0),esk2_0),k1_wellord1(esk3_0,esk2_0)),k1_wellord1(k2_wellord1(esk3_0,esk1_0),esk2_0)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( v1_relat_1(k2_wellord1(esk3_0,X1)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_15])).

cnf(c_0_25,plain,
    ( X1 = X2
    | r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_wellord1(X3,X2)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X1,k2_wellord1(esk3_0,X2)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(k4_tarski(esk5_2(k1_wellord1(k2_wellord1(esk3_0,esk1_0),esk2_0),k1_wellord1(esk3_0,esk2_0)),esk2_0),k2_wellord1(esk3_0,esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])])).

cnf(c_0_28,plain,
    ( X1 = X2
    | r2_hidden(X1,k1_wellord1(X3,X2))
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ v1_relat_1(X3) ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(k4_tarski(esk5_2(k1_wellord1(k2_wellord1(esk3_0,esk1_0),esk2_0),k1_wellord1(esk3_0,esk2_0)),esk2_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_30,negated_conjecture,
    ( esk5_2(k1_wellord1(k2_wellord1(esk3_0,esk1_0),esk2_0),k1_wellord1(esk3_0,esk2_0)) = esk2_0
    | r2_hidden(esk5_2(k1_wellord1(k2_wellord1(esk3_0,esk1_0),esk2_0),k1_wellord1(esk3_0,esk2_0)),k1_wellord1(esk3_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_15])])).

cnf(c_0_31,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,X3)
    | X3 != k1_wellord1(X4,X2)
    | ~ v1_relat_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk5_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk5_2(k1_wellord1(k2_wellord1(esk3_0,esk1_0),esk2_0),k1_wellord1(esk3_0,esk2_0)),k1_wellord1(esk3_0,esk2_0))
    | r2_hidden(esk2_0,k1_wellord1(k2_wellord1(esk3_0,esk1_0),esk2_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_30])).

cnf(c_0_34,plain,
    ( ~ r2_hidden(X1,k1_wellord1(X2,X1))
    | ~ v1_relat_1(X2) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_31])])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk2_0,k1_wellord1(k2_wellord1(esk3_0,esk1_0),esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_17])).

cnf(c_0_36,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_24])]),
    [proof]).
%------------------------------------------------------------------------------
