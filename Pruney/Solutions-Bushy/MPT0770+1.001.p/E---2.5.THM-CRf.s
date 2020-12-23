%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0770+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:10 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 882 expanded)
%              Number of clauses        :   68 ( 389 expanded)
%              Number of leaves         :   17 ( 217 expanded)
%              Depth                    :   14
%              Number of atoms          :  279 (2890 expanded)
%              Number of equality atoms :   34 ( 407 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(d6_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

fof(t19_wellord1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k3_relat_1(k2_wellord1(X3,X2)))
       => ( r2_hidden(X1,k3_relat_1(X3))
          & r2_hidden(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_wellord1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(t99_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k2_relat_1(k7_relat_1(X2,X1)),k2_relat_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_relat_1)).

fof(t119_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k8_relat_1(X1,X2)) = k3_xboole_0(k2_relat_1(X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_relat_1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(l29_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k1_relat_1(k8_relat_1(X1,X2)),k1_relat_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l29_wellord1)).

fof(t18_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_wellord1(X2,X1) = k8_relat_1(X1,k7_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_wellord1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(t17_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_wellord1(X2,X1) = k7_relat_1(k8_relat_1(X1,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_wellord1)).

fof(dt_k8_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => v1_relat_1(k8_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(dt_k2_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k2_wellord1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_wellord1)).

fof(t90_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k1_relat_1(k7_relat_1(X2,X1)) = k3_xboole_0(k1_relat_1(X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(c_0_17,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11,X12] :
      ( ( ~ r2_hidden(X8,X7)
        | r2_hidden(X8,X5)
        | r2_hidden(X8,X6)
        | X7 != k2_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X5)
        | r2_hidden(X9,X7)
        | X7 != k2_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X6)
        | r2_hidden(X9,X7)
        | X7 != k2_xboole_0(X5,X6) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X10)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k2_xboole_0(X10,X11) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X11)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k2_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X12)
        | r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X11)
        | X12 = k2_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

fof(c_0_18,plain,(
    ! [X45,X46,X47] :
      ( ~ r2_hidden(X45,X46)
      | ~ m1_subset_1(X46,k1_zfmisc_1(X47))
      | ~ v1_xboole_0(X47) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_19,plain,(
    ! [X40,X41] :
      ( ( ~ m1_subset_1(X40,k1_zfmisc_1(X41))
        | r1_tarski(X40,X41) )
      & ( ~ r1_tarski(X40,X41)
        | m1_subset_1(X40,k1_zfmisc_1(X41)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_xboole_0(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_21,plain,(
    ! [X23] :
      ( ~ v1_relat_1(X23)
      | k3_relat_1(X23) = k2_xboole_0(k1_relat_1(X23),k2_relat_1(X23)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_relat_1])])).

fof(c_0_22,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ( r2_hidden(X1,k3_relat_1(k2_wellord1(X3,X2)))
         => ( r2_hidden(X1,k3_relat_1(X3))
            & r2_hidden(X1,X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t19_wellord1])).

fof(c_0_23,plain,(
    ! [X14,X15,X16,X17,X18,X19,X20,X21] :
      ( ( r2_hidden(X17,X14)
        | ~ r2_hidden(X17,X16)
        | X16 != k3_xboole_0(X14,X15) )
      & ( r2_hidden(X17,X15)
        | ~ r2_hidden(X17,X16)
        | X16 != k3_xboole_0(X14,X15) )
      & ( ~ r2_hidden(X18,X14)
        | ~ r2_hidden(X18,X15)
        | r2_hidden(X18,X16)
        | X16 != k3_xboole_0(X14,X15) )
      & ( ~ r2_hidden(esk2_3(X19,X20,X21),X21)
        | ~ r2_hidden(esk2_3(X19,X20,X21),X19)
        | ~ r2_hidden(esk2_3(X19,X20,X21),X20)
        | X21 = k3_xboole_0(X19,X20) )
      & ( r2_hidden(esk2_3(X19,X20,X21),X19)
        | r2_hidden(esk2_3(X19,X20,X21),X21)
        | X21 = k3_xboole_0(X19,X20) )
      & ( r2_hidden(esk2_3(X19,X20,X21),X20)
        | r2_hidden(esk2_3(X19,X20,X21),X21)
        | X21 = k3_xboole_0(X19,X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_24,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_26,plain,(
    ! [X50,X51] :
      ( ~ v1_relat_1(X51)
      | r1_tarski(k2_relat_1(k7_relat_1(X51,X50)),k2_relat_1(X51)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t99_relat_1])])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k2_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_29,negated_conjecture,
    ( v1_relat_1(esk5_0)
    & r2_hidden(esk3_0,k3_relat_1(k2_wellord1(esk5_0,esk4_0)))
    & ( ~ r2_hidden(esk3_0,k3_relat_1(esk5_0))
      | ~ r2_hidden(esk3_0,esk4_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_22])])])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_31,plain,(
    ! [X32,X33] :
      ( ~ v1_relat_1(X33)
      | k2_relat_1(k8_relat_1(X32,X33)) = k3_xboole_0(k2_relat_1(X33),X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t119_relat_1])])).

fof(c_0_32,plain,(
    ! [X42,X43,X44] :
      ( ~ r2_hidden(X42,X43)
      | ~ m1_subset_1(X43,k1_zfmisc_1(X44))
      | m1_subset_1(X42,X44) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_33,plain,(
    ! [X30,X31] :
      ( ~ v1_relat_1(X31)
      | r1_tarski(k1_relat_1(k8_relat_1(X30,X31)),k1_relat_1(X31)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l29_wellord1])])).

fof(c_0_34,plain,(
    ! [X36,X37] :
      ( ~ v1_relat_1(X37)
      | k2_wellord1(X37,X36) = k8_relat_1(X36,k7_relat_1(X37,X36)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_wellord1])])).

fof(c_0_35,plain,(
    ! [X26,X27] :
      ( ~ v1_relat_1(X26)
      | v1_relat_1(k7_relat_1(X26,X27)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

cnf(c_0_36,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r1_tarski(X2,X1)
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_37,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(X1,X2)),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_38,plain,(
    ! [X34,X35] :
      ( ~ v1_relat_1(X35)
      | k2_wellord1(X35,X34) = k7_relat_1(k8_relat_1(X34,X35),X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t17_wellord1])])).

fof(c_0_39,plain,(
    ! [X28,X29] :
      ( ~ v1_relat_1(X29)
      | v1_relat_1(k8_relat_1(X28,X29)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_relat_1])])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | r2_hidden(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k3_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk3_0,k3_relat_1(k2_wellord1(esk5_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_42,plain,(
    ! [X24,X25] :
      ( ~ v1_relat_1(X24)
      | v1_relat_1(k2_wellord1(X24,X25)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_wellord1])])).

fof(c_0_43,plain,(
    ! [X48,X49] :
      ( ~ v1_relat_1(X49)
      | k1_relat_1(k7_relat_1(X49,X48)) = k3_xboole_0(k1_relat_1(X49),X48) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).

cnf(c_0_44,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_30])).

cnf(c_0_45,plain,
    ( k2_relat_1(k8_relat_1(X2,X1)) = k3_xboole_0(k2_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_46,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_47,plain,
    ( r1_tarski(k1_relat_1(k8_relat_1(X2,X1)),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_48,plain,
    ( k2_wellord1(X1,X2) = k8_relat_1(X2,k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_49,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_50,plain,
    ( ~ v1_xboole_0(k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(k7_relat_1(X1,X3))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_51,plain,
    ( k2_wellord1(X1,X2) = k7_relat_1(k8_relat_1(X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_52,plain,
    ( v1_relat_1(k8_relat_1(X2,X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(esk3_0,k1_relat_1(k2_wellord1(esk5_0,esk4_0)))
    | r2_hidden(esk3_0,k2_relat_1(k2_wellord1(esk5_0,esk4_0)))
    | ~ v1_relat_1(k2_wellord1(esk5_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_54,plain,
    ( v1_relat_1(k2_wellord1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_55,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_56,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_57,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k3_xboole_0(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_58,plain,
    ( r2_hidden(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(X1,k2_relat_1(k8_relat_1(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_59,plain,
    ( m1_subset_1(X1,X2)
    | ~ r1_tarski(X3,X2)
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_46,c_0_25])).

cnf(c_0_60,plain,
    ( r1_tarski(k1_relat_1(k2_wellord1(X1,X2)),k1_relat_1(k7_relat_1(X1,X2)))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49])).

cnf(c_0_61,plain,
    ( ~ v1_xboole_0(k2_relat_1(k8_relat_1(X1,X2)))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X3,k2_relat_1(k2_wellord1(X2,X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(esk3_0,k2_relat_1(k2_wellord1(esk5_0,esk4_0)))
    | r2_hidden(esk3_0,k1_relat_1(k2_wellord1(esk5_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55])])).

cnf(c_0_63,plain,
    ( ~ v1_xboole_0(k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(k8_relat_1(X3,X1))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_47])).

cnf(c_0_64,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_56])).

cnf(c_0_65,plain,
    ( r2_hidden(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2))) ),
    inference(spm,[status(thm)],[c_0_44,c_0_57])).

cnf(c_0_66,plain,
    ( r2_hidden(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(X1,k2_relat_1(k2_wellord1(X3,X2))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_48]),c_0_49])).

cnf(c_0_67,plain,
    ( r1_tarski(k2_relat_1(k2_wellord1(X1,X2)),k2_relat_1(k8_relat_1(X2,X1)))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_51]),c_0_52])).

cnf(c_0_68,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_69,plain,(
    ! [X38,X39] :
      ( ~ m1_subset_1(X38,X39)
      | v1_xboole_0(X39)
      | r2_hidden(X38,X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_70,plain,
    ( m1_subset_1(X1,k1_relat_1(k7_relat_1(X2,X3)))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k1_relat_1(k2_wellord1(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_71,negated_conjecture,
    ( r2_hidden(esk3_0,k1_relat_1(k2_wellord1(esk5_0,esk4_0)))
    | ~ v1_xboole_0(k2_relat_1(k8_relat_1(esk4_0,esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_55])])).

cnf(c_0_72,plain,
    ( ~ v1_xboole_0(k1_relat_1(k7_relat_1(X1,X2)))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X3,k1_relat_1(k2_wellord1(X1,X2))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_48]),c_0_49])).

cnf(c_0_73,negated_conjecture,
    ( ~ r2_hidden(esk3_0,k3_relat_1(esk5_0))
    | ~ r2_hidden(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_74,plain,
    ( r2_hidden(X1,k3_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_28])).

cnf(c_0_75,plain,
    ( r2_hidden(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(X1,k1_relat_1(k2_wellord1(X3,X2))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_51]),c_0_52])).

cnf(c_0_76,negated_conjecture,
    ( r2_hidden(esk3_0,k1_relat_1(k2_wellord1(esk5_0,esk4_0)))
    | r2_hidden(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_62]),c_0_55])])).

cnf(c_0_77,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_78,plain,
    ( m1_subset_1(X1,k2_relat_1(k8_relat_1(X2,X3)))
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(X1,k2_relat_1(k2_wellord1(X3,X2))) ),
    inference(spm,[status(thm)],[c_0_59,c_0_67])).

cnf(c_0_79,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_68])).

cnf(c_0_80,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_81,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_relat_1(k7_relat_1(esk5_0,esk4_0)))
    | ~ v1_xboole_0(k2_relat_1(k8_relat_1(esk4_0,esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_55])])).

cnf(c_0_82,negated_conjecture,
    ( ~ v1_xboole_0(k1_relat_1(k7_relat_1(esk5_0,esk4_0)))
    | ~ v1_xboole_0(k2_relat_1(k8_relat_1(esk4_0,esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_71]),c_0_55])])).

cnf(c_0_83,negated_conjecture,
    ( ~ r2_hidden(esk3_0,k1_relat_1(esk5_0))
    | ~ r2_hidden(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_55])])).

cnf(c_0_84,negated_conjecture,
    ( r2_hidden(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_55])])).

cnf(c_0_85,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_77])).

cnf(c_0_86,negated_conjecture,
    ( m1_subset_1(esk3_0,k2_relat_1(k8_relat_1(esk4_0,esk5_0)))
    | r2_hidden(esk3_0,k1_relat_1(k2_wellord1(esk5_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_62]),c_0_55])])).

cnf(c_0_87,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k1_relat_1(k7_relat_1(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_79,c_0_57])).

cnf(c_0_88,negated_conjecture,
    ( r2_hidden(esk3_0,k1_relat_1(k7_relat_1(esk5_0,esk4_0)))
    | ~ v1_xboole_0(k2_relat_1(k8_relat_1(esk4_0,esk5_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_82])).

cnf(c_0_89,negated_conjecture,
    ( ~ r2_hidden(esk3_0,k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_83,c_0_84])])).

cnf(c_0_90,plain,
    ( r2_hidden(X1,k3_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k2_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_85,c_0_28])).

cnf(c_0_91,negated_conjecture,
    ( m1_subset_1(esk3_0,k2_relat_1(k8_relat_1(esk4_0,esk5_0)))
    | m1_subset_1(esk3_0,k1_relat_1(k7_relat_1(esk5_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_86]),c_0_55])])).

cnf(c_0_92,negated_conjecture,
    ( ~ v1_xboole_0(k2_relat_1(k8_relat_1(esk4_0,esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_55])]),c_0_89])).

cnf(c_0_93,negated_conjecture,
    ( ~ r2_hidden(esk3_0,k2_relat_1(esk5_0))
    | ~ r2_hidden(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_90]),c_0_55])])).

cnf(c_0_94,negated_conjecture,
    ( m1_subset_1(esk3_0,k2_relat_1(k8_relat_1(esk4_0,esk5_0)))
    | ~ v1_xboole_0(k1_relat_1(k7_relat_1(esk5_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_86]),c_0_55])])).

cnf(c_0_95,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k2_relat_1(k8_relat_1(X3,X2))) ),
    inference(spm,[status(thm)],[c_0_79,c_0_45])).

cnf(c_0_96,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_relat_1(k7_relat_1(esk5_0,esk4_0)))
    | r2_hidden(esk3_0,k2_relat_1(k8_relat_1(esk4_0,esk5_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_91]),c_0_92])).

cnf(c_0_97,negated_conjecture,
    ( ~ r2_hidden(esk3_0,k2_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_93,c_0_84])])).

cnf(c_0_98,negated_conjecture,
    ( r2_hidden(esk3_0,k2_relat_1(k8_relat_1(esk4_0,esk5_0)))
    | ~ v1_xboole_0(k1_relat_1(k7_relat_1(esk5_0,esk4_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_94]),c_0_92])).

cnf(c_0_99,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_relat_1(k7_relat_1(esk5_0,esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_96]),c_0_55])]),c_0_97])).

cnf(c_0_100,negated_conjecture,
    ( ~ v1_xboole_0(k1_relat_1(k7_relat_1(esk5_0,esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_98]),c_0_55])]),c_0_97])).

cnf(c_0_101,negated_conjecture,
    ( r2_hidden(esk3_0,k1_relat_1(k7_relat_1(esk5_0,esk4_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_99]),c_0_100])).

cnf(c_0_102,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_101]),c_0_55])]),c_0_89]),
    [proof]).

%------------------------------------------------------------------------------
