%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0314+1.003 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:24 EST 2020

% Result     : Theorem 1.51s
% Output     : CNFRefutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :   48 (  82 expanded)
%              Number of clauses        :   27 (  39 expanded)
%              Number of leaves         :   10 (  21 expanded)
%              Depth                    :   10
%              Number of atoms          :  106 ( 237 expanded)
%              Number of equality atoms :   55 ( 107 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal clause size      :   20 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(t4_boole,axiom,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t54_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k3_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_xboole_1)).

fof(t125_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k4_xboole_0(X1,X2),X3) = k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))
      & k2_zfmisc_1(X3,k4_xboole_0(X1,X2)) = k4_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_zfmisc_1)).

fof(t126_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] : k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)) = k2_xboole_0(k2_zfmisc_1(k4_xboole_0(X1,X3),X2),k2_zfmisc_1(X1,k4_xboole_0(X2,X4))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_zfmisc_1)).

fof(t123_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(c_0_10,plain,(
    ! [X18,X19,X20,X21,X22,X23,X24,X25] :
      ( ( r2_hidden(X21,X18)
        | ~ r2_hidden(X21,X20)
        | X20 != k4_xboole_0(X18,X19) )
      & ( ~ r2_hidden(X21,X19)
        | ~ r2_hidden(X21,X20)
        | X20 != k4_xboole_0(X18,X19) )
      & ( ~ r2_hidden(X22,X18)
        | r2_hidden(X22,X19)
        | r2_hidden(X22,X20)
        | X20 != k4_xboole_0(X18,X19) )
      & ( ~ r2_hidden(esk2_3(X23,X24,X25),X25)
        | ~ r2_hidden(esk2_3(X23,X24,X25),X23)
        | r2_hidden(esk2_3(X23,X24,X25),X24)
        | X25 = k4_xboole_0(X23,X24) )
      & ( r2_hidden(esk2_3(X23,X24,X25),X23)
        | r2_hidden(esk2_3(X23,X24,X25),X25)
        | X25 = k4_xboole_0(X23,X24) )
      & ( ~ r2_hidden(esk2_3(X23,X24,X25),X24)
        | r2_hidden(esk2_3(X23,X24,X25),X25)
        | X25 = k4_xboole_0(X23,X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_11,plain,(
    ! [X9,X10,X11,X12,X13,X14,X15,X16] :
      ( ( ~ r2_hidden(X12,X11)
        | r2_hidden(X12,X9)
        | r2_hidden(X12,X10)
        | X11 != k2_xboole_0(X9,X10) )
      & ( ~ r2_hidden(X13,X9)
        | r2_hidden(X13,X11)
        | X11 != k2_xboole_0(X9,X10) )
      & ( ~ r2_hidden(X13,X10)
        | r2_hidden(X13,X11)
        | X11 != k2_xboole_0(X9,X10) )
      & ( ~ r2_hidden(esk1_3(X14,X15,X16),X14)
        | ~ r2_hidden(esk1_3(X14,X15,X16),X16)
        | X16 = k2_xboole_0(X14,X15) )
      & ( ~ r2_hidden(esk1_3(X14,X15,X16),X15)
        | ~ r2_hidden(esk1_3(X14,X15,X16),X16)
        | X16 = k2_xboole_0(X14,X15) )
      & ( r2_hidden(esk1_3(X14,X15,X16),X16)
        | r2_hidden(esk1_3(X14,X15,X16),X14)
        | r2_hidden(esk1_3(X14,X15,X16),X15)
        | X16 = k2_xboole_0(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

cnf(c_0_12,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_13,plain,(
    ! [X35] : k4_xboole_0(k1_xboole_0,X35) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

cnf(c_0_14,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,plain,(
    ! [X34] : k2_xboole_0(X34,k1_xboole_0) = X34 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

cnf(c_0_16,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_21,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])).

cnf(c_0_22,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X1)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_23,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_24,plain,(
    ! [X36,X37,X38] : k4_xboole_0(X36,k3_xboole_0(X37,X38)) = k2_xboole_0(k4_xboole_0(X36,X37),k4_xboole_0(X36,X38)) ),
    inference(variable_rename,[status(thm)],[t54_xboole_1])).

fof(c_0_25,plain,(
    ! [X31,X32,X33] :
      ( k2_zfmisc_1(k4_xboole_0(X31,X32),X33) = k4_xboole_0(k2_zfmisc_1(X31,X33),k2_zfmisc_1(X32,X33))
      & k2_zfmisc_1(X33,k4_xboole_0(X31,X32)) = k4_xboole_0(k2_zfmisc_1(X33,X31),k2_zfmisc_1(X33,X32)) ) ),
    inference(variable_rename,[status(thm)],[t125_zfmisc_1])).

fof(c_0_26,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] : k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)) = k2_xboole_0(k2_zfmisc_1(k4_xboole_0(X1,X3),X2),k2_zfmisc_1(X1,k4_xboole_0(X2,X4))) ),
    inference(assume_negation,[status(cth)],[t126_zfmisc_1])).

cnf(c_0_27,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_28,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | r2_hidden(esk2_3(X1,X2,k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_29,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_30,plain,(
    ! [X27,X28,X29,X30] : k2_zfmisc_1(k3_xboole_0(X27,X28),k3_xboole_0(X29,X30)) = k3_xboole_0(k2_zfmisc_1(X27,X29),k2_zfmisc_1(X28,X30)) ),
    inference(variable_rename,[status(thm)],[t123_zfmisc_1])).

fof(c_0_31,plain,(
    ! [X7,X8] : k3_xboole_0(X7,X8) = k3_xboole_0(X8,X7) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_32,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,plain,
    ( k2_zfmisc_1(k4_xboole_0(X1,X2),X3) = k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_34,negated_conjecture,(
    k4_xboole_0(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk6_0)) != k2_xboole_0(k2_zfmisc_1(k4_xboole_0(esk3_0,esk5_0),esk4_0),k2_zfmisc_1(esk3_0,k4_xboole_0(esk4_0,esk6_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_26])])])).

cnf(c_0_35,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_21])).

cnf(c_0_36,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_19,c_0_29])).

cnf(c_0_37,plain,
    ( k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,plain,
    ( k2_xboole_0(k4_xboole_0(k2_zfmisc_1(X1,X2),X3),k2_zfmisc_1(k4_xboole_0(X1,X4),X2)) = k4_xboole_0(k2_zfmisc_1(X1,X2),k3_xboole_0(X3,k2_zfmisc_1(X4,X2))) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_40,plain,
    ( k2_zfmisc_1(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_41,negated_conjecture,
    ( k4_xboole_0(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk6_0)) != k2_xboole_0(k2_zfmisc_1(k4_xboole_0(esk3_0,esk5_0),esk4_0),k2_zfmisc_1(esk3_0,k4_xboole_0(esk4_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_35]),c_0_36])).

cnf(c_0_43,plain,
    ( k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X4),k2_zfmisc_1(X3,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_37])).

cnf(c_0_44,plain,
    ( k4_xboole_0(k2_zfmisc_1(X1,X2),k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X4,X2))) = k2_xboole_0(k2_zfmisc_1(X1,k4_xboole_0(X2,X3)),k2_zfmisc_1(k4_xboole_0(X1,X4),X2)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_45,negated_conjecture,
    ( k2_xboole_0(k2_zfmisc_1(esk3_0,k4_xboole_0(esk4_0,esk6_0)),k2_zfmisc_1(k4_xboole_0(esk3_0,esk5_0),esk4_0)) != k4_xboole_0(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(rw,[status(thm)],[c_0_41,c_0_29])).

cnf(c_0_46,plain,
    ( k2_xboole_0(k2_zfmisc_1(X1,k4_xboole_0(X2,X3)),k2_zfmisc_1(k4_xboole_0(X1,X4),X2)) = k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X4,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44])).

cnf(c_0_47,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_46])]),
    [proof]).

%------------------------------------------------------------------------------
