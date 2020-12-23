%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:48:24 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 190 expanded)
%              Number of clauses        :   43 (  84 expanded)
%              Number of leaves         :   11 (  45 expanded)
%              Depth                    :   12
%              Number of atoms          :  187 ( 537 expanded)
%              Number of equality atoms :   30 (  68 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d6_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t31_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k3_relat_1(X1),k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).

fof(t10_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(X1,k2_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(t25_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
              & r1_tarski(k2_relat_1(X1),k2_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(t8_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2) )
     => r1_tarski(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t30_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X1,X2),X3)
       => ( r2_hidden(X1,k3_relat_1(X3))
          & r2_hidden(X2,k3_relat_1(X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relat_1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(c_0_11,plain,(
    ! [X45] :
      ( ~ v1_relat_1(X45)
      | k3_relat_1(X45) = k2_xboole_0(k1_relat_1(X45),k2_relat_1(X45)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_relat_1])])).

fof(c_0_12,plain,(
    ! [X28,X29] : k3_tarski(k2_tarski(X28,X29)) = k2_xboole_0(X28,X29) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ( r1_tarski(X1,X2)
             => r1_tarski(k3_relat_1(X1),k3_relat_1(X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t31_relat_1])).

fof(c_0_14,plain,(
    ! [X20,X21,X22] :
      ( ~ r1_tarski(X20,X21)
      | r1_tarski(X20,k2_xboole_0(X22,X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).

cnf(c_0_15,plain,
    ( k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_17,negated_conjecture,
    ( v1_relat_1(esk6_0)
    & v1_relat_1(esk7_0)
    & r1_tarski(esk6_0,esk7_0)
    & ~ r1_tarski(k3_relat_1(esk6_0),k3_relat_1(esk7_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

fof(c_0_18,plain,(
    ! [X46,X47] :
      ( ( r1_tarski(k1_relat_1(X46),k1_relat_1(X47))
        | ~ r1_tarski(X46,X47)
        | ~ v1_relat_1(X47)
        | ~ v1_relat_1(X46) )
      & ( r1_tarski(k2_relat_1(X46),k2_relat_1(X47))
        | ~ r1_tarski(X46,X47)
        | ~ v1_relat_1(X47)
        | ~ v1_relat_1(X46) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).

fof(c_0_19,plain,(
    ! [X25,X26,X27] :
      ( ~ r1_tarski(X25,X26)
      | ~ r1_tarski(X27,X26)
      | r1_tarski(k2_xboole_0(X25,X27),X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).

cnf(c_0_20,plain,
    ( r1_tarski(X1,k2_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( k3_relat_1(X1) = k3_tarski(k2_tarski(k1_relat_1(X1),k2_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( r1_tarski(k2_relat_1(X1),k2_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_24,plain,(
    ! [X34,X35,X36,X38,X39,X40,X41,X43] :
      ( ( ~ r2_hidden(X36,X35)
        | r2_hidden(k4_tarski(X36,esk3_3(X34,X35,X36)),X34)
        | X35 != k1_relat_1(X34) )
      & ( ~ r2_hidden(k4_tarski(X38,X39),X34)
        | r2_hidden(X38,X35)
        | X35 != k1_relat_1(X34) )
      & ( ~ r2_hidden(esk4_2(X40,X41),X41)
        | ~ r2_hidden(k4_tarski(esk4_2(X40,X41),X43),X40)
        | X41 = k1_relat_1(X40) )
      & ( r2_hidden(esk4_2(X40,X41),X41)
        | r2_hidden(k4_tarski(esk4_2(X40,X41),esk5_2(X40,X41)),X40)
        | X41 = k1_relat_1(X40) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

fof(c_0_25,plain,(
    ! [X23,X24] :
      ( ~ r1_tarski(X23,X24)
      | k3_xboole_0(X23,X24) = X23 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_26,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_27,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X3,X2)))
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_20,c_0_16])).

cnf(c_0_30,negated_conjecture,
    ( k3_tarski(k2_tarski(k1_relat_1(esk7_0),k2_relat_1(esk7_0))) = k3_relat_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(k2_relat_1(X1),k2_relat_1(esk7_0))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_22])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_33,plain,(
    ! [X48,X49,X50] :
      ( ( r2_hidden(X48,k3_relat_1(X50))
        | ~ r2_hidden(k4_tarski(X48,X49),X50)
        | ~ v1_relat_1(X50) )
      & ( r2_hidden(X49,k3_relat_1(X50))
        | ~ r2_hidden(k4_tarski(X48,X49),X50)
        | ~ v1_relat_1(X50) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_relat_1])])])).

cnf(c_0_34,plain,
    ( r2_hidden(k4_tarski(X1,esk3_3(X3,X2,X1)),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_35,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_36,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_37,plain,
    ( r1_tarski(k3_tarski(k2_tarski(X1,X3)),X2)
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_27,c_0_16])).

cnf(c_0_38,negated_conjecture,
    ( k3_tarski(k2_tarski(k1_relat_1(esk6_0),k2_relat_1(esk6_0))) = k3_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_28])).

cnf(c_0_39,negated_conjecture,
    ( r1_tarski(X1,k3_relat_1(esk7_0))
    | ~ r1_tarski(X1,k2_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk6_0),k2_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_28]),c_0_32])])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,k3_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_42,plain,
    ( r2_hidden(k4_tarski(X1,esk3_3(X2,k1_relat_1(X2),X1)),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_34])).

cnf(c_0_43,plain,
    ( k3_xboole_0(X1,X2) = X1
    | r2_hidden(esk1_2(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(k3_relat_1(esk6_0),X1)
    | ~ r1_tarski(k2_relat_1(esk6_0),X1)
    | ~ r1_tarski(k1_relat_1(esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk6_0),k3_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_46,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(esk6_0),k3_relat_1(esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_47,plain,(
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
      & ( ~ r2_hidden(esk2_3(X16,X17,X18),X18)
        | ~ r2_hidden(esk2_3(X16,X17,X18),X16)
        | ~ r2_hidden(esk2_3(X16,X17,X18),X17)
        | X18 = k3_xboole_0(X16,X17) )
      & ( r2_hidden(esk2_3(X16,X17,X18),X16)
        | r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k3_xboole_0(X16,X17) )
      & ( r2_hidden(esk2_3(X16,X17,X18),X17)
        | r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k3_xboole_0(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(X1,k3_relat_1(esk7_0))
    | ~ r2_hidden(k4_tarski(X1,X2),esk7_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_22])).

cnf(c_0_49,plain,
    ( k3_xboole_0(k1_relat_1(X1),X2) = k1_relat_1(X1)
    | r2_hidden(k4_tarski(esk1_2(k1_relat_1(X1),X2),esk3_3(X1,k1_relat_1(X1),esk1_2(k1_relat_1(X1),X2))),X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_50,negated_conjecture,
    ( ~ r1_tarski(k1_relat_1(esk6_0),k3_relat_1(esk7_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46])).

cnf(c_0_51,plain,
    ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_52,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_53,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_54,negated_conjecture,
    ( k3_xboole_0(k1_relat_1(esk7_0),X1) = k1_relat_1(esk7_0)
    | r2_hidden(esk1_2(k1_relat_1(esk7_0),X1),k3_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_55,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk1_2(k1_relat_1(esk6_0),k3_relat_1(esk7_0)),k1_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_36])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(k1_relat_1(X1),k1_relat_1(esk7_0))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_22])).

cnf(c_0_58,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_52])).

cnf(c_0_59,negated_conjecture,
    ( k3_xboole_0(k1_relat_1(esk7_0),k3_relat_1(esk7_0)) = k1_relat_1(esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_35])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(esk1_2(k1_relat_1(esk6_0),k3_relat_1(esk7_0)),X1)
    | ~ r1_tarski(k1_relat_1(esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_61,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk6_0),k1_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_28]),c_0_32])])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(X1,k3_relat_1(esk7_0))
    | ~ r2_hidden(X1,k1_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(esk1_2(k1_relat_1(esk6_0),k3_relat_1(esk7_0)),k1_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(esk1_2(k1_relat_1(esk6_0),k3_relat_1(esk7_0)),k3_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_65,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_64]),c_0_50]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.15  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.15/0.35  % Computer   : n022.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 13:32:26 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  # Version: 2.5pre002
% 0.21/0.36  # No SInE strategy applied
% 0.21/0.36  # Trying AutoSched0 for 299 seconds
% 0.21/0.52  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S053I
% 0.21/0.52  # and selection function HSelectMinInfpos.
% 0.21/0.52  #
% 0.21/0.52  # Preprocessing time       : 0.028 s
% 0.21/0.52  # Presaturation interreduction done
% 0.21/0.52  
% 0.21/0.52  # Proof found!
% 0.21/0.52  # SZS status Theorem
% 0.21/0.52  # SZS output start CNFRefutation
% 0.21/0.52  fof(d6_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k3_relat_1(X1)=k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 0.21/0.52  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.21/0.52  fof(t31_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>r1_tarski(k3_relat_1(X1),k3_relat_1(X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_relat_1)).
% 0.21/0.52  fof(t10_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(X1,k2_xboole_0(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 0.21/0.52  fof(t25_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>(r1_tarski(k1_relat_1(X1),k1_relat_1(X2))&r1_tarski(k2_relat_1(X1),k2_relat_1(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 0.21/0.52  fof(t8_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X3,X2))=>r1_tarski(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 0.21/0.52  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 0.21/0.52  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.21/0.52  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.21/0.52  fof(t30_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)=>(r2_hidden(X1,k3_relat_1(X3))&r2_hidden(X2,k3_relat_1(X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_relat_1)).
% 0.21/0.52  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.21/0.52  fof(c_0_11, plain, ![X45]:(~v1_relat_1(X45)|k3_relat_1(X45)=k2_xboole_0(k1_relat_1(X45),k2_relat_1(X45))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_relat_1])])).
% 0.21/0.52  fof(c_0_12, plain, ![X28, X29]:k3_tarski(k2_tarski(X28,X29))=k2_xboole_0(X28,X29), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.21/0.52  fof(c_0_13, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>r1_tarski(k3_relat_1(X1),k3_relat_1(X2)))))), inference(assume_negation,[status(cth)],[t31_relat_1])).
% 0.21/0.52  fof(c_0_14, plain, ![X20, X21, X22]:(~r1_tarski(X20,X21)|r1_tarski(X20,k2_xboole_0(X22,X21))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).
% 0.21/0.52  cnf(c_0_15, plain, (k3_relat_1(X1)=k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.52  cnf(c_0_16, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.52  fof(c_0_17, negated_conjecture, (v1_relat_1(esk6_0)&(v1_relat_1(esk7_0)&(r1_tarski(esk6_0,esk7_0)&~r1_tarski(k3_relat_1(esk6_0),k3_relat_1(esk7_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 0.21/0.52  fof(c_0_18, plain, ![X46, X47]:((r1_tarski(k1_relat_1(X46),k1_relat_1(X47))|~r1_tarski(X46,X47)|~v1_relat_1(X47)|~v1_relat_1(X46))&(r1_tarski(k2_relat_1(X46),k2_relat_1(X47))|~r1_tarski(X46,X47)|~v1_relat_1(X47)|~v1_relat_1(X46))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).
% 0.21/0.52  fof(c_0_19, plain, ![X25, X26, X27]:(~r1_tarski(X25,X26)|~r1_tarski(X27,X26)|r1_tarski(k2_xboole_0(X25,X27),X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).
% 0.21/0.52  cnf(c_0_20, plain, (r1_tarski(X1,k2_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.52  cnf(c_0_21, plain, (k3_relat_1(X1)=k3_tarski(k2_tarski(k1_relat_1(X1),k2_relat_1(X1)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_15, c_0_16])).
% 0.21/0.52  cnf(c_0_22, negated_conjecture, (v1_relat_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.52  cnf(c_0_23, plain, (r1_tarski(k2_relat_1(X1),k2_relat_1(X2))|~r1_tarski(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.52  fof(c_0_24, plain, ![X34, X35, X36, X38, X39, X40, X41, X43]:(((~r2_hidden(X36,X35)|r2_hidden(k4_tarski(X36,esk3_3(X34,X35,X36)),X34)|X35!=k1_relat_1(X34))&(~r2_hidden(k4_tarski(X38,X39),X34)|r2_hidden(X38,X35)|X35!=k1_relat_1(X34)))&((~r2_hidden(esk4_2(X40,X41),X41)|~r2_hidden(k4_tarski(esk4_2(X40,X41),X43),X40)|X41=k1_relat_1(X40))&(r2_hidden(esk4_2(X40,X41),X41)|r2_hidden(k4_tarski(esk4_2(X40,X41),esk5_2(X40,X41)),X40)|X41=k1_relat_1(X40)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 0.21/0.52  fof(c_0_25, plain, ![X23, X24]:(~r1_tarski(X23,X24)|k3_xboole_0(X23,X24)=X23), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.21/0.52  fof(c_0_26, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.21/0.52  cnf(c_0_27, plain, (r1_tarski(k2_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.52  cnf(c_0_28, negated_conjecture, (v1_relat_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.52  cnf(c_0_29, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X3,X2)))|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_20, c_0_16])).
% 0.21/0.52  cnf(c_0_30, negated_conjecture, (k3_tarski(k2_tarski(k1_relat_1(esk7_0),k2_relat_1(esk7_0)))=k3_relat_1(esk7_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.21/0.52  cnf(c_0_31, negated_conjecture, (r1_tarski(k2_relat_1(X1),k2_relat_1(esk7_0))|~v1_relat_1(X1)|~r1_tarski(X1,esk7_0)), inference(spm,[status(thm)],[c_0_23, c_0_22])).
% 0.21/0.52  cnf(c_0_32, negated_conjecture, (r1_tarski(esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.52  fof(c_0_33, plain, ![X48, X49, X50]:((r2_hidden(X48,k3_relat_1(X50))|~r2_hidden(k4_tarski(X48,X49),X50)|~v1_relat_1(X50))&(r2_hidden(X49,k3_relat_1(X50))|~r2_hidden(k4_tarski(X48,X49),X50)|~v1_relat_1(X50))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_relat_1])])])).
% 0.21/0.52  cnf(c_0_34, plain, (r2_hidden(k4_tarski(X1,esk3_3(X3,X2,X1)),X3)|~r2_hidden(X1,X2)|X2!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.21/0.52  cnf(c_0_35, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.52  cnf(c_0_36, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.21/0.52  cnf(c_0_37, plain, (r1_tarski(k3_tarski(k2_tarski(X1,X3)),X2)|~r1_tarski(X3,X2)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_27, c_0_16])).
% 0.21/0.52  cnf(c_0_38, negated_conjecture, (k3_tarski(k2_tarski(k1_relat_1(esk6_0),k2_relat_1(esk6_0)))=k3_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_21, c_0_28])).
% 0.21/0.52  cnf(c_0_39, negated_conjecture, (r1_tarski(X1,k3_relat_1(esk7_0))|~r1_tarski(X1,k2_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.21/0.52  cnf(c_0_40, negated_conjecture, (r1_tarski(k2_relat_1(esk6_0),k2_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_28]), c_0_32])])).
% 0.21/0.52  cnf(c_0_41, plain, (r2_hidden(X1,k3_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.21/0.52  cnf(c_0_42, plain, (r2_hidden(k4_tarski(X1,esk3_3(X2,k1_relat_1(X2),X1)),X2)|~r2_hidden(X1,k1_relat_1(X2))), inference(er,[status(thm)],[c_0_34])).
% 0.21/0.52  cnf(c_0_43, plain, (k3_xboole_0(X1,X2)=X1|r2_hidden(esk1_2(X1,X2),X1)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.21/0.52  cnf(c_0_44, negated_conjecture, (r1_tarski(k3_relat_1(esk6_0),X1)|~r1_tarski(k2_relat_1(esk6_0),X1)|~r1_tarski(k1_relat_1(esk6_0),X1)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.21/0.52  cnf(c_0_45, negated_conjecture, (r1_tarski(k2_relat_1(esk6_0),k3_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.21/0.52  cnf(c_0_46, negated_conjecture, (~r1_tarski(k3_relat_1(esk6_0),k3_relat_1(esk7_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.52  fof(c_0_47, plain, ![X11, X12, X13, X14, X15, X16, X17, X18]:((((r2_hidden(X14,X11)|~r2_hidden(X14,X13)|X13!=k3_xboole_0(X11,X12))&(r2_hidden(X14,X12)|~r2_hidden(X14,X13)|X13!=k3_xboole_0(X11,X12)))&(~r2_hidden(X15,X11)|~r2_hidden(X15,X12)|r2_hidden(X15,X13)|X13!=k3_xboole_0(X11,X12)))&((~r2_hidden(esk2_3(X16,X17,X18),X18)|(~r2_hidden(esk2_3(X16,X17,X18),X16)|~r2_hidden(esk2_3(X16,X17,X18),X17))|X18=k3_xboole_0(X16,X17))&((r2_hidden(esk2_3(X16,X17,X18),X16)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k3_xboole_0(X16,X17))&(r2_hidden(esk2_3(X16,X17,X18),X17)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k3_xboole_0(X16,X17))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.21/0.52  cnf(c_0_48, negated_conjecture, (r2_hidden(X1,k3_relat_1(esk7_0))|~r2_hidden(k4_tarski(X1,X2),esk7_0)), inference(spm,[status(thm)],[c_0_41, c_0_22])).
% 0.21/0.52  cnf(c_0_49, plain, (k3_xboole_0(k1_relat_1(X1),X2)=k1_relat_1(X1)|r2_hidden(k4_tarski(esk1_2(k1_relat_1(X1),X2),esk3_3(X1,k1_relat_1(X1),esk1_2(k1_relat_1(X1),X2))),X1)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.21/0.52  cnf(c_0_50, negated_conjecture, (~r1_tarski(k1_relat_1(esk6_0),k3_relat_1(esk7_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46])).
% 0.21/0.52  cnf(c_0_51, plain, (r1_tarski(k1_relat_1(X1),k1_relat_1(X2))|~r1_tarski(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.52  cnf(c_0_52, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.21/0.52  cnf(c_0_53, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.21/0.52  cnf(c_0_54, negated_conjecture, (k3_xboole_0(k1_relat_1(esk7_0),X1)=k1_relat_1(esk7_0)|r2_hidden(esk1_2(k1_relat_1(esk7_0),X1),k3_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.21/0.52  cnf(c_0_55, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.21/0.52  cnf(c_0_56, negated_conjecture, (r2_hidden(esk1_2(k1_relat_1(esk6_0),k3_relat_1(esk7_0)),k1_relat_1(esk6_0))), inference(spm,[status(thm)],[c_0_50, c_0_36])).
% 0.21/0.52  cnf(c_0_57, negated_conjecture, (r1_tarski(k1_relat_1(X1),k1_relat_1(esk7_0))|~v1_relat_1(X1)|~r1_tarski(X1,esk7_0)), inference(spm,[status(thm)],[c_0_51, c_0_22])).
% 0.21/0.52  cnf(c_0_58, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X3,X2))), inference(er,[status(thm)],[c_0_52])).
% 0.21/0.52  cnf(c_0_59, negated_conjecture, (k3_xboole_0(k1_relat_1(esk7_0),k3_relat_1(esk7_0))=k1_relat_1(esk7_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_35])).
% 0.21/0.52  cnf(c_0_60, negated_conjecture, (r2_hidden(esk1_2(k1_relat_1(esk6_0),k3_relat_1(esk7_0)),X1)|~r1_tarski(k1_relat_1(esk6_0),X1)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.21/0.52  cnf(c_0_61, negated_conjecture, (r1_tarski(k1_relat_1(esk6_0),k1_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_28]), c_0_32])])).
% 0.21/0.52  cnf(c_0_62, negated_conjecture, (r2_hidden(X1,k3_relat_1(esk7_0))|~r2_hidden(X1,k1_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.21/0.52  cnf(c_0_63, negated_conjecture, (r2_hidden(esk1_2(k1_relat_1(esk6_0),k3_relat_1(esk7_0)),k1_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.21/0.52  cnf(c_0_64, negated_conjecture, (r2_hidden(esk1_2(k1_relat_1(esk6_0),k3_relat_1(esk7_0)),k3_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.21/0.52  cnf(c_0_65, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_64]), c_0_50]), ['proof']).
% 0.21/0.52  # SZS output end CNFRefutation
% 0.21/0.52  # Proof object total steps             : 66
% 0.21/0.52  # Proof object clause steps            : 43
% 0.21/0.52  # Proof object formula steps           : 23
% 0.21/0.52  # Proof object conjectures             : 26
% 0.21/0.52  # Proof object clause conjectures      : 23
% 0.21/0.52  # Proof object formula conjectures     : 3
% 0.21/0.52  # Proof object initial clauses used    : 17
% 0.21/0.52  # Proof object initial formulas used   : 11
% 0.21/0.52  # Proof object generating inferences   : 21
% 0.21/0.52  # Proof object simplifying inferences  : 12
% 0.21/0.52  # Training examples: 0 positive, 0 negative
% 0.21/0.52  # Parsed axioms                        : 13
% 0.21/0.52  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.52  # Initial clauses                      : 29
% 0.21/0.52  # Removed in clause preprocessing      : 1
% 0.21/0.52  # Initial clauses in saturation        : 28
% 0.21/0.52  # Processed clauses                    : 1050
% 0.21/0.52  # ...of these trivial                  : 78
% 0.21/0.52  # ...subsumed                          : 295
% 0.21/0.52  # ...remaining for further processing  : 677
% 0.21/0.52  # Other redundant clauses eliminated   : 5
% 0.21/0.52  # Clauses deleted for lack of memory   : 0
% 0.21/0.52  # Backward-subsumed                    : 19
% 0.21/0.52  # Backward-rewritten                   : 49
% 0.21/0.52  # Generated clauses                    : 6111
% 0.21/0.52  # ...of the previous two non-trivial   : 5348
% 0.21/0.52  # Contextual simplify-reflections      : 8
% 0.21/0.52  # Paramodulations                      : 6054
% 0.21/0.52  # Factorizations                       : 52
% 0.21/0.52  # Equation resolutions                 : 5
% 0.21/0.52  # Propositional unsat checks           : 0
% 0.21/0.52  #    Propositional check models        : 0
% 0.21/0.52  #    Propositional check unsatisfiable : 0
% 0.21/0.52  #    Propositional clauses             : 0
% 0.21/0.52  #    Propositional clauses after purity: 0
% 0.21/0.52  #    Propositional unsat core size     : 0
% 0.21/0.52  #    Propositional preprocessing time  : 0.000
% 0.21/0.52  #    Propositional encoding time       : 0.000
% 0.21/0.52  #    Propositional solver time         : 0.000
% 0.21/0.52  #    Success case prop preproc time    : 0.000
% 0.21/0.52  #    Success case prop encoding time   : 0.000
% 0.21/0.52  #    Success case prop solver time     : 0.000
% 0.21/0.52  # Current number of processed clauses  : 576
% 0.21/0.52  #    Positive orientable unit clauses  : 91
% 0.21/0.52  #    Positive unorientable unit clauses: 0
% 0.21/0.52  #    Negative unit clauses             : 2
% 0.21/0.52  #    Non-unit-clauses                  : 483
% 0.21/0.52  # Current number of unprocessed clauses: 4303
% 0.21/0.52  # ...number of literals in the above   : 12582
% 0.21/0.52  # Current number of archived formulas  : 0
% 0.21/0.52  # Current number of archived clauses   : 97
% 0.21/0.52  # Clause-clause subsumption calls (NU) : 29915
% 0.21/0.52  # Rec. Clause-clause subsumption calls : 23034
% 0.21/0.52  # Non-unit clause-clause subsumptions  : 305
% 0.21/0.52  # Unit Clause-clause subsumption calls : 2635
% 0.21/0.52  # Rewrite failures with RHS unbound    : 0
% 0.21/0.52  # BW rewrite match attempts            : 87
% 0.21/0.52  # BW rewrite match successes           : 10
% 0.21/0.52  # Condensation attempts                : 0
% 0.21/0.52  # Condensation successes               : 0
% 0.21/0.52  # Termbank termtop insertions          : 108782
% 0.21/0.52  
% 0.21/0.52  # -------------------------------------------------
% 0.21/0.52  # User time                : 0.159 s
% 0.21/0.52  # System time              : 0.005 s
% 0.21/0.52  # Total time               : 0.164 s
% 0.21/0.52  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
