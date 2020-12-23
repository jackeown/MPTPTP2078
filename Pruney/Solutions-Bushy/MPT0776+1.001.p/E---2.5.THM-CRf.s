%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0776+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:10 EST 2020

% Result     : Theorem 0.10s
% Output     : CNFRefutation 0.10s
% Verified   : 
% Statistics : Number of formulae       :   34 (  91 expanded)
%              Number of clauses        :   23 (  39 expanded)
%              Number of leaves         :    5 (  21 expanded)
%              Depth                    :   10
%              Number of atoms          :  102 ( 299 expanded)
%              Number of equality atoms :   19 (  40 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t25_wellord1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_2(X2)
       => v4_relat_2(k2_wellord1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_wellord1)).

fof(dt_k2_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k2_wellord1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_wellord1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(d6_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] : k2_wellord1(X1,X2) = k3_xboole_0(X1,k2_zfmisc_1(X2,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_wellord1)).

fof(l3_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_2(X1)
      <=> ! [X2,X3] :
            ( ( r2_hidden(k4_tarski(X2,X3),X1)
              & r2_hidden(k4_tarski(X3,X2),X1) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_wellord1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( v4_relat_2(X2)
         => v4_relat_2(k2_wellord1(X2,X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t25_wellord1])).

fof(c_0_6,plain,(
    ! [X16,X17] :
      ( ~ v1_relat_1(X16)
      | v1_relat_1(k2_wellord1(X16,X17)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_wellord1])])).

fof(c_0_7,negated_conjecture,
    ( v1_relat_1(esk5_0)
    & v4_relat_2(esk5_0)
    & ~ v4_relat_2(k2_wellord1(esk5_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

fof(c_0_8,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11,X12] :
      ( ( r2_hidden(X8,X5)
        | ~ r2_hidden(X8,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( r2_hidden(X8,X6)
        | ~ r2_hidden(X8,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X5)
        | ~ r2_hidden(X9,X6)
        | r2_hidden(X9,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X10)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X11)
        | X12 = k3_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k3_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X11)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k3_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

fof(c_0_9,plain,(
    ! [X14,X15] :
      ( ~ v1_relat_1(X14)
      | k2_wellord1(X14,X15) = k3_xboole_0(X14,k2_zfmisc_1(X15,X15)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_wellord1])])])).

fof(c_0_10,plain,(
    ! [X18,X19,X20] :
      ( ( ~ v4_relat_2(X18)
        | ~ r2_hidden(k4_tarski(X19,X20),X18)
        | ~ r2_hidden(k4_tarski(X20,X19),X18)
        | X19 = X20
        | ~ v1_relat_1(X18) )
      & ( r2_hidden(k4_tarski(esk2_1(X18),esk3_1(X18)),X18)
        | v4_relat_2(X18)
        | ~ v1_relat_1(X18) )
      & ( r2_hidden(k4_tarski(esk3_1(X18),esk2_1(X18)),X18)
        | v4_relat_2(X18)
        | ~ v1_relat_1(X18) )
      & ( esk2_1(X18) != esk3_1(X18)
        | v4_relat_2(X18)
        | ~ v1_relat_1(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_wellord1])])])])])).

cnf(c_0_11,plain,
    ( v1_relat_1(k2_wellord1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( k2_wellord1(X1,X2) = k3_xboole_0(X1,k2_zfmisc_1(X2,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( r2_hidden(k4_tarski(esk2_1(X1),esk3_1(X1)),X1)
    | v4_relat_2(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( v1_relat_1(k2_wellord1(esk5_0,X1)) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( k3_xboole_0(esk5_0,k2_zfmisc_1(X1,X1)) = k2_wellord1(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( ~ v4_relat_2(k2_wellord1(esk5_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_20,negated_conjecture,
    ( v4_relat_2(k2_wellord1(esk5_0,X1))
    | r2_hidden(k4_tarski(esk2_1(k2_wellord1(esk5_0,X1)),esk3_1(k2_wellord1(esk5_0,X1))),k2_wellord1(esk5_0,X1)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_21,plain,
    ( r2_hidden(k4_tarski(esk3_1(X1),esk2_1(X1)),X1)
    | v4_relat_2(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,k2_wellord1(esk5_0,X2)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(k4_tarski(esk2_1(k2_wellord1(esk5_0,esk4_0)),esk3_1(k2_wellord1(esk5_0,esk4_0))),k2_wellord1(esk5_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( v4_relat_2(k2_wellord1(esk5_0,X1))
    | r2_hidden(k4_tarski(esk3_1(k2_wellord1(esk5_0,X1)),esk2_1(k2_wellord1(esk5_0,X1))),k2_wellord1(esk5_0,X1)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_16])).

cnf(c_0_25,plain,
    ( X2 = X3
    | ~ v4_relat_2(X1)
    | ~ r2_hidden(k4_tarski(X2,X3),X1)
    | ~ r2_hidden(k4_tarski(X3,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(k4_tarski(esk2_1(k2_wellord1(esk5_0,esk4_0)),esk3_1(k2_wellord1(esk5_0,esk4_0))),esk5_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_27,negated_conjecture,
    ( v4_relat_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_1(k2_wellord1(esk5_0,esk4_0)),esk2_1(k2_wellord1(esk5_0,esk4_0))),k2_wellord1(esk5_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( esk3_1(k2_wellord1(esk5_0,esk4_0)) = esk2_1(k2_wellord1(esk5_0,esk4_0))
    | ~ r2_hidden(k4_tarski(esk3_1(k2_wellord1(esk5_0,esk4_0)),esk2_1(k2_wellord1(esk5_0,esk4_0))),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_12])])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_1(k2_wellord1(esk5_0,esk4_0)),esk2_1(k2_wellord1(esk5_0,esk4_0))),esk5_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_28])).

cnf(c_0_31,plain,
    ( v4_relat_2(X1)
    | esk2_1(X1) != esk3_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_32,negated_conjecture,
    ( esk3_1(k2_wellord1(esk5_0,esk4_0)) = esk2_1(k2_wellord1(esk5_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_30])])).

cnf(c_0_33,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_16])]),c_0_19]),
    [proof]).

%------------------------------------------------------------------------------
