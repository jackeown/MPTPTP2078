%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : wellord1__t25_wellord1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:12 EDT 2019

% Result     : Theorem 3.49s
% Output     : CNFRefutation 3.49s
% Verified   : 
% Statistics : Number of formulae       :   30 (  56 expanded)
%              Number of clauses        :   19 (  25 expanded)
%              Number of leaves         :    5 (  14 expanded)
%              Depth                    :    7
%              Number of atoms          :  108 ( 233 expanded)
%              Number of equality atoms :   17 (  37 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t25_wellord1.p',d4_xboole_0)).

fof(d6_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] : k2_wellord1(X1,X2) = k3_xboole_0(X1,k2_zfmisc_1(X2,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t25_wellord1.p',d6_wellord1)).

fof(l3_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_2(X1)
      <=> ! [X2,X3] :
            ( ( r2_hidden(k4_tarski(X2,X3),X1)
              & r2_hidden(k4_tarski(X3,X2),X1) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t25_wellord1.p',l3_wellord1)).

fof(dt_k2_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k2_wellord1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t25_wellord1.p',dt_k2_wellord1)).

fof(t25_wellord1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_2(X2)
       => v4_relat_2(k2_wellord1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t25_wellord1.p',t25_wellord1)).

fof(c_0_5,plain,(
    ! [X11,X12,X13,X14,X15,X16,X17,X18] :
      ( ( r2_hidden(X14,X11)
        | ~ r2_hidden(X14,X13)
        | X13 != k3_xboole_0(X11,X12) )
      & ( r2_hidden(X14,X12)
        | ~ r2_hidden(X14,X13)
        | X13 != k3_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X15,X11)
        | ~ r2_hidden(X15,X12)
        | r2_hidden(X15,X13)
        | X13 != k3_xboole_0(X11,X12) )
      & ( ~ r2_hidden(esk3_3(X16,X17,X18),X18)
        | ~ r2_hidden(esk3_3(X16,X17,X18),X16)
        | ~ r2_hidden(esk3_3(X16,X17,X18),X17)
        | X18 = k3_xboole_0(X16,X17) )
      & ( r2_hidden(esk3_3(X16,X17,X18),X16)
        | r2_hidden(esk3_3(X16,X17,X18),X18)
        | X18 = k3_xboole_0(X16,X17) )
      & ( r2_hidden(esk3_3(X16,X17,X18),X17)
        | r2_hidden(esk3_3(X16,X17,X18),X18)
        | X18 = k3_xboole_0(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_6,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_7,plain,(
    ! [X20,X21] :
      ( ~ v1_relat_1(X20)
      | k2_wellord1(X20,X21) = k3_xboole_0(X20,k2_zfmisc_1(X21,X21)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_wellord1])])])).

fof(c_0_8,plain,(
    ! [X27,X28,X29] :
      ( ( ~ v4_relat_2(X27)
        | ~ r2_hidden(k4_tarski(X28,X29),X27)
        | ~ r2_hidden(k4_tarski(X29,X28),X27)
        | X28 = X29
        | ~ v1_relat_1(X27) )
      & ( r2_hidden(k4_tarski(esk5_1(X27),esk6_1(X27)),X27)
        | v4_relat_2(X27)
        | ~ v1_relat_1(X27) )
      & ( r2_hidden(k4_tarski(esk6_1(X27),esk5_1(X27)),X27)
        | v4_relat_2(X27)
        | ~ v1_relat_1(X27) )
      & ( esk5_1(X27) != esk6_1(X27)
        | v4_relat_2(X27)
        | ~ v1_relat_1(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_wellord1])])])])])).

fof(c_0_9,plain,(
    ! [X22,X23] :
      ( ~ v1_relat_1(X22)
      | v1_relat_1(k2_wellord1(X22,X23)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_wellord1])])).

cnf(c_0_10,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( k2_wellord1(X1,X2) = k3_xboole_0(X1,k2_zfmisc_1(X2,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( r2_hidden(k4_tarski(esk5_1(X1),esk6_1(X1)),X1)
    | v4_relat_2(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( v1_relat_1(k2_wellord1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( r2_hidden(k4_tarski(esk6_1(X1),esk5_1(X1)),X1)
    | v4_relat_2(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( v4_relat_2(X2)
         => v4_relat_2(k2_wellord1(X2,X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t25_wellord1])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k2_wellord1(X2,X3))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_17,plain,
    ( r2_hidden(k4_tarski(esk5_1(k2_wellord1(X1,X2)),esk6_1(k2_wellord1(X1,X2))),k2_wellord1(X1,X2))
    | v4_relat_2(k2_wellord1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_18,plain,
    ( r2_hidden(k4_tarski(esk6_1(k2_wellord1(X1,X2)),esk5_1(k2_wellord1(X1,X2))),k2_wellord1(X1,X2))
    | v4_relat_2(k2_wellord1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_13])).

cnf(c_0_19,plain,
    ( v4_relat_2(X1)
    | esk5_1(X1) != esk6_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_20,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & v4_relat_2(esk2_0)
    & ~ v4_relat_2(k2_wellord1(esk2_0,esk1_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

cnf(c_0_21,plain,
    ( X2 = X3
    | ~ v4_relat_2(X1)
    | ~ r2_hidden(k4_tarski(X2,X3),X1)
    | ~ r2_hidden(k4_tarski(X3,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_22,plain,
    ( r2_hidden(k4_tarski(esk5_1(k2_wellord1(X1,X2)),esk6_1(k2_wellord1(X1,X2))),X1)
    | v4_relat_2(k2_wellord1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_23,plain,
    ( r2_hidden(k4_tarski(esk6_1(k2_wellord1(X1,X2)),esk5_1(k2_wellord1(X1,X2))),X1)
    | v4_relat_2(k2_wellord1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_18])).

cnf(c_0_24,plain,
    ( v4_relat_2(k2_wellord1(X1,X2))
    | esk6_1(k2_wellord1(X1,X2)) != esk5_1(k2_wellord1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_13])).

cnf(c_0_25,negated_conjecture,
    ( ~ v4_relat_2(k2_wellord1(esk2_0,esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( v4_relat_2(k2_wellord1(X1,X2))
    | ~ v4_relat_2(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23]),c_0_24])).

cnf(c_0_27,negated_conjecture,
    ( v4_relat_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_28])]),
    [proof]).
%------------------------------------------------------------------------------
