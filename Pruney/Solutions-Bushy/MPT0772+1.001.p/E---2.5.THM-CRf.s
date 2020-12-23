%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0772+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:10 EST 2020

% Result     : Theorem 1.92s
% Output     : CNFRefutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :   42 (  77 expanded)
%              Number of clauses        :   29 (  36 expanded)
%              Number of leaves         :    6 (  18 expanded)
%              Depth                    :   17
%              Number of atoms          :  148 ( 299 expanded)
%              Number of equality atoms :   31 (  55 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t21_wellord1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => r1_tarski(k1_wellord1(k2_wellord1(X3,X1),X2),k1_wellord1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_wellord1)).

fof(d1_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( X3 = k1_wellord1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ( X4 != X2
                & r2_hidden(k4_tarski(X4,X2),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord1)).

fof(dt_k2_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k2_wellord1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_wellord1)).

fof(c_0_6,plain,(
    ! [X19,X20,X21,X22,X23,X24,X25,X26] :
      ( ( r2_hidden(X22,X19)
        | ~ r2_hidden(X22,X21)
        | X21 != k3_xboole_0(X19,X20) )
      & ( r2_hidden(X22,X20)
        | ~ r2_hidden(X22,X21)
        | X21 != k3_xboole_0(X19,X20) )
      & ( ~ r2_hidden(X23,X19)
        | ~ r2_hidden(X23,X20)
        | r2_hidden(X23,X21)
        | X21 != k3_xboole_0(X19,X20) )
      & ( ~ r2_hidden(esk3_3(X24,X25,X26),X26)
        | ~ r2_hidden(esk3_3(X24,X25,X26),X24)
        | ~ r2_hidden(esk3_3(X24,X25,X26),X25)
        | X26 = k3_xboole_0(X24,X25) )
      & ( r2_hidden(esk3_3(X24,X25,X26),X24)
        | r2_hidden(esk3_3(X24,X25,X26),X26)
        | X26 = k3_xboole_0(X24,X25) )
      & ( r2_hidden(esk3_3(X24,X25,X26),X25)
        | r2_hidden(esk3_3(X24,X25,X26),X26)
        | X26 = k3_xboole_0(X24,X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_7,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_8,plain,(
    ! [X28,X29] :
      ( ~ v1_relat_1(X28)
      | k2_wellord1(X28,X29) = k3_xboole_0(X28,k2_zfmisc_1(X29,X29)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_wellord1])])])).

cnf(c_0_9,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_7])).

cnf(c_0_10,plain,
    ( k2_wellord1(X1,X2) = k3_xboole_0(X1,k2_zfmisc_1(X2,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_11,plain,(
    ! [X13,X14,X15,X16,X17] :
      ( ( ~ r1_tarski(X13,X14)
        | ~ r2_hidden(X15,X13)
        | r2_hidden(X15,X14) )
      & ( r2_hidden(esk2_2(X16,X17),X16)
        | r1_tarski(X16,X17) )
      & ( ~ r2_hidden(esk2_2(X16,X17),X17)
        | r1_tarski(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => r1_tarski(k1_wellord1(k2_wellord1(X3,X1),X2),k1_wellord1(X3,X2)) ) ),
    inference(assume_negation,[status(cth)],[t21_wellord1])).

cnf(c_0_13,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k2_wellord1(X2,X3))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_14,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,negated_conjecture,
    ( v1_relat_1(esk6_0)
    & ~ r1_tarski(k1_wellord1(k2_wellord1(esk6_0,esk4_0),esk5_0),k1_wellord1(esk6_0,esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

cnf(c_0_16,plain,
    ( r1_tarski(k2_wellord1(X1,X2),X3)
    | r2_hidden(esk2_2(k2_wellord1(X1,X2),X3),X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_17,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_18,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk2_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,negated_conjecture,
    ( r1_tarski(k2_wellord1(esk6_0,X1),X2)
    | r2_hidden(esk2_2(k2_wellord1(esk6_0,X1),X2),esk6_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

fof(c_0_20,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11] :
      ( ( X8 != X6
        | ~ r2_hidden(X8,X7)
        | X7 != k1_wellord1(X5,X6)
        | ~ v1_relat_1(X5) )
      & ( r2_hidden(k4_tarski(X8,X6),X5)
        | ~ r2_hidden(X8,X7)
        | X7 != k1_wellord1(X5,X6)
        | ~ v1_relat_1(X5) )
      & ( X9 = X6
        | ~ r2_hidden(k4_tarski(X9,X6),X5)
        | r2_hidden(X9,X7)
        | X7 != k1_wellord1(X5,X6)
        | ~ v1_relat_1(X5) )
      & ( ~ r2_hidden(esk1_3(X5,X10,X11),X11)
        | esk1_3(X5,X10,X11) = X10
        | ~ r2_hidden(k4_tarski(esk1_3(X5,X10,X11),X10),X5)
        | X11 = k1_wellord1(X5,X10)
        | ~ v1_relat_1(X5) )
      & ( esk1_3(X5,X10,X11) != X10
        | r2_hidden(esk1_3(X5,X10,X11),X11)
        | X11 = k1_wellord1(X5,X10)
        | ~ v1_relat_1(X5) )
      & ( r2_hidden(k4_tarski(esk1_3(X5,X10,X11),X10),X5)
        | r2_hidden(esk1_3(X5,X10,X11),X11)
        | X11 = k1_wellord1(X5,X10)
        | ~ v1_relat_1(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord1])])])])])])).

cnf(c_0_21,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_22,negated_conjecture,
    ( r1_tarski(k2_wellord1(esk6_0,X1),esk6_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_23,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,X4)
    | X4 != k1_wellord1(X3,X2)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X1,k2_wellord1(esk6_0,X2)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_25,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,k1_wellord1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(er,[status(thm)],[c_0_23])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,X2),esk6_0)
    | ~ r2_hidden(X1,k1_wellord1(k2_wellord1(esk6_0,X3),X2))
    | ~ v1_relat_1(k2_wellord1(esk6_0,X3)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

fof(c_0_27,plain,(
    ! [X30,X31] :
      ( ~ v1_relat_1(X30)
      | v1_relat_1(k2_wellord1(X30,X31)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_wellord1])])).

cnf(c_0_28,plain,
    ( X1 = X2
    | r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_wellord1(X3,X2)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,negated_conjecture,
    ( r1_tarski(k1_wellord1(k2_wellord1(esk6_0,X1),X2),X3)
    | r2_hidden(k4_tarski(esk2_2(k1_wellord1(k2_wellord1(esk6_0,X1),X2),X3),X2),esk6_0)
    | ~ v1_relat_1(k2_wellord1(esk6_0,X1)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_14])).

cnf(c_0_30,plain,
    ( v1_relat_1(k2_wellord1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_31,plain,
    ( X1 = X2
    | r2_hidden(X1,k1_wellord1(X3,X2))
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ v1_relat_1(X3) ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(k1_wellord1(k2_wellord1(esk6_0,X1),X2),X3)
    | r2_hidden(k4_tarski(esk2_2(k1_wellord1(k2_wellord1(esk6_0,X1),X2),X3),X2),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_17])])).

cnf(c_0_33,negated_conjecture,
    ( esk2_2(k1_wellord1(k2_wellord1(esk6_0,X1),X2),X3) = X2
    | r1_tarski(k1_wellord1(k2_wellord1(esk6_0,X1),X2),X3)
    | r2_hidden(esk2_2(k1_wellord1(k2_wellord1(esk6_0,X1),X2),X3),k1_wellord1(esk6_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_17])])).

cnf(c_0_34,negated_conjecture,
    ( esk2_2(k1_wellord1(k2_wellord1(esk6_0,X1),X2),k1_wellord1(esk6_0,X2)) = X2
    | r1_tarski(k1_wellord1(k2_wellord1(esk6_0,X1),X2),k1_wellord1(esk6_0,X2)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_33])).

cnf(c_0_35,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,X3)
    | X3 != k1_wellord1(X4,X2)
    | ~ v1_relat_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_36,negated_conjecture,
    ( ~ r1_tarski(k1_wellord1(k2_wellord1(esk6_0,esk4_0),esk5_0),k1_wellord1(esk6_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(k1_wellord1(k2_wellord1(esk6_0,X1),X2),k1_wellord1(esk6_0,X2))
    | r2_hidden(X2,k1_wellord1(k2_wellord1(esk6_0,X1),X2)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_34])).

cnf(c_0_38,plain,
    ( ~ r2_hidden(X1,k1_wellord1(X2,X1))
    | ~ v1_relat_1(X2) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_35])])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk5_0,k1_wellord1(k2_wellord1(esk6_0,esk4_0),esk5_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_40,negated_conjecture,
    ( ~ v1_relat_1(k2_wellord1(esk6_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_41,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_30]),c_0_17])]),
    [proof]).

%------------------------------------------------------------------------------
