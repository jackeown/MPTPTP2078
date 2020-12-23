%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:52:18 EST 2020

% Result     : Theorem 18.17s
% Output     : CNFRefutation 18.17s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 357 expanded)
%              Number of clauses        :   43 ( 137 expanded)
%              Number of leaves         :   18 ( 107 expanded)
%              Depth                    :    9
%              Number of atoms          :  141 ( 509 expanded)
%              Number of equality atoms :   71 ( 348 expanded)
%              Maximal formula depth    :   15 (   3 average)
%              Maximal clause size      :   12 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t205_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X1,k1_relat_1(X2))
      <=> k11_relat_1(X2,X1) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

fof(t204_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> r2_hidden(X2,k11_relat_1(X3,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t46_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(t78_enumset1,axiom,(
    ! [X1,X2,X3] : k3_enumset1(X1,X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_enumset1)).

fof(t80_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k5_enumset1(X1,X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(t21_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

fof(l1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t20_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
    <=> X1 != X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(t19_zfmisc_1,axiom,(
    ! [X1,X2] : k3_xboole_0(k1_tarski(X1),k2_tarski(X1,X2)) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_zfmisc_1)).

fof(t3_xboole_1,axiom,(
    ! [X1] :
      ( r1_tarski(X1,k1_xboole_0)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( r2_hidden(X1,k1_relat_1(X2))
        <=> k11_relat_1(X2,X1) != k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t205_relat_1])).

fof(c_0_19,plain,(
    ! [X56,X57,X58] :
      ( ( ~ r2_hidden(k4_tarski(X56,X57),X58)
        | r2_hidden(X57,k11_relat_1(X58,X56))
        | ~ v1_relat_1(X58) )
      & ( ~ r2_hidden(X57,k11_relat_1(X58,X56))
        | r2_hidden(k4_tarski(X56,X57),X58)
        | ~ v1_relat_1(X58) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t204_relat_1])])])).

fof(c_0_20,negated_conjecture,
    ( v1_relat_1(esk6_0)
    & ( ~ r2_hidden(esk5_0,k1_relat_1(esk6_0))
      | k11_relat_1(esk6_0,esk5_0) = k1_xboole_0 )
    & ( r2_hidden(esk5_0,k1_relat_1(esk6_0))
      | k11_relat_1(esk6_0,esk5_0) != k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).

fof(c_0_21,plain,(
    ! [X8] :
      ( X8 = k1_xboole_0
      | r2_hidden(esk1_1(X8),X8) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

fof(c_0_22,plain,(
    ! [X45,X46,X47,X49,X50,X51,X52,X54] :
      ( ( ~ r2_hidden(X47,X46)
        | r2_hidden(k4_tarski(X47,esk2_3(X45,X46,X47)),X45)
        | X46 != k1_relat_1(X45) )
      & ( ~ r2_hidden(k4_tarski(X49,X50),X45)
        | r2_hidden(X49,X46)
        | X46 != k1_relat_1(X45) )
      & ( ~ r2_hidden(esk3_2(X51,X52),X52)
        | ~ r2_hidden(k4_tarski(esk3_2(X51,X52),X54),X51)
        | X52 = k1_relat_1(X51) )
      & ( r2_hidden(esk3_2(X51,X52),X52)
        | r2_hidden(k4_tarski(esk3_2(X51,X52),esk4_2(X51,X52)),X51)
        | X52 = k1_relat_1(X51) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

fof(c_0_23,plain,(
    ! [X43,X44] : k1_setfam_1(k2_tarski(X43,X44)) = k3_xboole_0(X43,X44) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_24,plain,(
    ! [X18,X19] : k1_enumset1(X18,X18,X19) = k2_tarski(X18,X19) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_25,plain,
    ( r2_hidden(k4_tarski(X3,X1),X2)
    | ~ r2_hidden(X1,k11_relat_1(X2,X3))
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk5_0,k1_relat_1(esk6_0))
    | k11_relat_1(esk6_0,esk5_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_30,plain,(
    ! [X37,X38] : k3_tarski(k2_tarski(X37,X38)) = k2_xboole_0(X37,X38) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_31,plain,(
    ! [X10,X11] : k4_xboole_0(X10,X11) = k5_xboole_0(X10,k3_xboole_0(X10,X11)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_32,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,plain,
    ( r2_hidden(k4_tarski(X1,esk2_3(X3,X2,X1)),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,X2),esk6_0)
    | ~ r2_hidden(X2,k11_relat_1(esk6_0,X1)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk1_1(k11_relat_1(esk6_0,esk5_0)),k11_relat_1(esk6_0,esk5_0))
    | r2_hidden(esk5_0,k1_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2) ),
    inference(er,[status(thm)],[c_0_29])).

fof(c_0_38,plain,(
    ! [X15,X16] : k4_xboole_0(X15,k2_xboole_0(X15,X16)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t46_xboole_1])).

cnf(c_0_39,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_41,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_32,c_0_33])).

fof(c_0_42,plain,(
    ! [X27,X28,X29] : k3_enumset1(X27,X27,X27,X28,X29) = k1_enumset1(X27,X28,X29) ),
    inference(variable_rename,[status(thm)],[t78_enumset1])).

fof(c_0_43,plain,(
    ! [X30,X31,X32,X33,X34] : k5_enumset1(X30,X30,X30,X31,X32,X33,X34) = k3_enumset1(X30,X31,X32,X33,X34) ),
    inference(variable_rename,[status(thm)],[t80_enumset1])).

fof(c_0_44,plain,(
    ! [X20,X21,X22,X23,X24,X25,X26] : k6_enumset1(X20,X20,X21,X22,X23,X24,X25,X26) = k5_enumset1(X20,X21,X22,X23,X24,X25,X26) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_45,plain,(
    ! [X12,X13] : k3_xboole_0(X12,k2_xboole_0(X12,X13)) = X12 ),
    inference(variable_rename,[status(thm)],[t21_xboole_1])).

fof(c_0_46,plain,(
    ! [X35,X36] :
      ( ( ~ r1_tarski(k1_tarski(X35),X36)
        | r2_hidden(X35,X36) )
      & ( ~ r2_hidden(X35,X36)
        | r1_tarski(k1_tarski(X35),X36) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).

fof(c_0_47,plain,(
    ! [X17] : k2_tarski(X17,X17) = k1_tarski(X17) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_48,plain,
    ( r2_hidden(X2,k11_relat_1(X3,X1))
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_49,plain,
    ( r2_hidden(k4_tarski(X1,esk2_3(X2,k1_relat_1(X2),X1)),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_34])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(esk5_0,k1_relat_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37])).

cnf(c_0_51,negated_conjecture,
    ( k11_relat_1(esk6_0,esk5_0) = k1_xboole_0
    | ~ r2_hidden(esk5_0,k1_relat_1(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_52,plain,(
    ! [X41,X42] :
      ( ( k4_xboole_0(k1_tarski(X41),k1_tarski(X42)) != k1_tarski(X41)
        | X41 != X42 )
      & ( X41 = X42
        | k4_xboole_0(k1_tarski(X41),k1_tarski(X42)) = k1_tarski(X41) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_zfmisc_1])])).

fof(c_0_53,plain,(
    ! [X39,X40] : k3_xboole_0(k1_tarski(X39),k2_tarski(X39,X40)) = k1_tarski(X39) ),
    inference(variable_rename,[status(thm)],[t19_zfmisc_1])).

cnf(c_0_54,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_55,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_39,c_0_33])).

cnf(c_0_56,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_57,plain,
    ( k3_enumset1(X1,X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_58,plain,
    ( k5_enumset1(X1,X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_59,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_60,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_61,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_62,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(X1,k11_relat_1(esk6_0,X2))
    | ~ r2_hidden(k4_tarski(X2,X1),esk6_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_26])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(k4_tarski(esk5_0,esk2_3(esk6_0,k1_relat_1(esk6_0),esk5_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_65,negated_conjecture,
    ( k11_relat_1(esk6_0,esk5_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_50])])).

cnf(c_0_66,plain,
    ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) != k1_tarski(X1)
    | X1 != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_67,plain,
    ( k3_xboole_0(k1_tarski(X1),k2_tarski(X1,X2)) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_68,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_55]),c_0_56]),c_0_57]),c_0_57]),c_0_58]),c_0_58]),c_0_59]),c_0_59])).

cnf(c_0_69,plain,
    ( k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_55]),c_0_41]),c_0_57]),c_0_57]),c_0_58]),c_0_58]),c_0_59]),c_0_59])).

fof(c_0_70,plain,(
    ! [X14] :
      ( ~ r1_tarski(X14,k1_xboole_0)
      | X14 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).

cnf(c_0_71,plain,
    ( r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_62]),c_0_33]),c_0_57]),c_0_58]),c_0_59])).

cnf(c_0_72,negated_conjecture,
    ( r2_hidden(esk2_3(esk6_0,k1_relat_1(esk6_0),esk5_0),k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65])).

cnf(c_0_73,plain,
    ( X1 != X2
    | k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)))) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_62]),c_0_62]),c_0_62]),c_0_33]),c_0_33]),c_0_33]),c_0_56]),c_0_57]),c_0_57]),c_0_57]),c_0_57]),c_0_57]),c_0_57]),c_0_58]),c_0_58]),c_0_58]),c_0_58]),c_0_58]),c_0_58]),c_0_58]),c_0_58]),c_0_59]),c_0_59]),c_0_59]),c_0_59]),c_0_59]),c_0_59]),c_0_59]),c_0_59]),c_0_59]),c_0_59])).

cnf(c_0_74,plain,
    ( k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_62]),c_0_62]),c_0_33]),c_0_33]),c_0_33]),c_0_41]),c_0_57]),c_0_57]),c_0_57]),c_0_57]),c_0_57]),c_0_58]),c_0_58]),c_0_58]),c_0_58]),c_0_58]),c_0_58]),c_0_58]),c_0_59]),c_0_59]),c_0_59]),c_0_59]),c_0_59]),c_0_59]),c_0_59]),c_0_59]),c_0_59])).

cnf(c_0_75,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_76,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_77,negated_conjecture,
    ( r1_tarski(k6_enumset1(esk2_3(esk6_0,k1_relat_1(esk6_0),esk5_0),esk2_3(esk6_0,k1_relat_1(esk6_0),esk5_0),esk2_3(esk6_0,k1_relat_1(esk6_0),esk5_0),esk2_3(esk6_0,k1_relat_1(esk6_0),esk5_0),esk2_3(esk6_0,k1_relat_1(esk6_0),esk5_0),esk2_3(esk6_0,k1_relat_1(esk6_0),esk5_0),esk2_3(esk6_0,k1_relat_1(esk6_0),esk5_0),esk2_3(esk6_0,k1_relat_1(esk6_0),esk5_0)),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_78,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_73]),c_0_74]),c_0_75])).

cnf(c_0_79,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_78]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n002.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:40:36 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 18.17/18.42  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 18.17/18.42  # and selection function SelectNegativeLiterals.
% 18.17/18.42  #
% 18.17/18.42  # Preprocessing time       : 0.027 s
% 18.17/18.42  # Presaturation interreduction done
% 18.17/18.42  
% 18.17/18.42  # Proof found!
% 18.17/18.42  # SZS status Theorem
% 18.17/18.42  # SZS output start CNFRefutation
% 18.17/18.42  fof(t205_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(r2_hidden(X1,k1_relat_1(X2))<=>k11_relat_1(X2,X1)!=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 18.17/18.42  fof(t204_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)<=>r2_hidden(X2,k11_relat_1(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t204_relat_1)).
% 18.17/18.42  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 18.17/18.42  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 18.17/18.42  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 18.17/18.42  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 18.17/18.42  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 18.17/18.42  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 18.17/18.42  fof(t46_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 18.17/18.42  fof(t78_enumset1, axiom, ![X1, X2, X3]:k3_enumset1(X1,X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_enumset1)).
% 18.17/18.42  fof(t80_enumset1, axiom, ![X1, X2, X3, X4, X5]:k5_enumset1(X1,X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_enumset1)).
% 18.17/18.42  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 18.17/18.42  fof(t21_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 18.17/18.42  fof(l1_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 18.17/18.42  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 18.17/18.42  fof(t20_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)<=>X1!=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 18.17/18.42  fof(t19_zfmisc_1, axiom, ![X1, X2]:k3_xboole_0(k1_tarski(X1),k2_tarski(X1,X2))=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_zfmisc_1)).
% 18.17/18.42  fof(t3_xboole_1, axiom, ![X1]:(r1_tarski(X1,k1_xboole_0)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 18.17/18.42  fof(c_0_18, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(r2_hidden(X1,k1_relat_1(X2))<=>k11_relat_1(X2,X1)!=k1_xboole_0))), inference(assume_negation,[status(cth)],[t205_relat_1])).
% 18.17/18.42  fof(c_0_19, plain, ![X56, X57, X58]:((~r2_hidden(k4_tarski(X56,X57),X58)|r2_hidden(X57,k11_relat_1(X58,X56))|~v1_relat_1(X58))&(~r2_hidden(X57,k11_relat_1(X58,X56))|r2_hidden(k4_tarski(X56,X57),X58)|~v1_relat_1(X58))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t204_relat_1])])])).
% 18.17/18.42  fof(c_0_20, negated_conjecture, (v1_relat_1(esk6_0)&((~r2_hidden(esk5_0,k1_relat_1(esk6_0))|k11_relat_1(esk6_0,esk5_0)=k1_xboole_0)&(r2_hidden(esk5_0,k1_relat_1(esk6_0))|k11_relat_1(esk6_0,esk5_0)!=k1_xboole_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).
% 18.17/18.42  fof(c_0_21, plain, ![X8]:(X8=k1_xboole_0|r2_hidden(esk1_1(X8),X8)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 18.17/18.42  fof(c_0_22, plain, ![X45, X46, X47, X49, X50, X51, X52, X54]:(((~r2_hidden(X47,X46)|r2_hidden(k4_tarski(X47,esk2_3(X45,X46,X47)),X45)|X46!=k1_relat_1(X45))&(~r2_hidden(k4_tarski(X49,X50),X45)|r2_hidden(X49,X46)|X46!=k1_relat_1(X45)))&((~r2_hidden(esk3_2(X51,X52),X52)|~r2_hidden(k4_tarski(esk3_2(X51,X52),X54),X51)|X52=k1_relat_1(X51))&(r2_hidden(esk3_2(X51,X52),X52)|r2_hidden(k4_tarski(esk3_2(X51,X52),esk4_2(X51,X52)),X51)|X52=k1_relat_1(X51)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 18.17/18.42  fof(c_0_23, plain, ![X43, X44]:k1_setfam_1(k2_tarski(X43,X44))=k3_xboole_0(X43,X44), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 18.17/18.42  fof(c_0_24, plain, ![X18, X19]:k1_enumset1(X18,X18,X19)=k2_tarski(X18,X19), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 18.17/18.42  cnf(c_0_25, plain, (r2_hidden(k4_tarski(X3,X1),X2)|~r2_hidden(X1,k11_relat_1(X2,X3))|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 18.17/18.42  cnf(c_0_26, negated_conjecture, (v1_relat_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 18.17/18.42  cnf(c_0_27, negated_conjecture, (r2_hidden(esk5_0,k1_relat_1(esk6_0))|k11_relat_1(esk6_0,esk5_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 18.17/18.42  cnf(c_0_28, plain, (X1=k1_xboole_0|r2_hidden(esk1_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 18.17/18.42  cnf(c_0_29, plain, (r2_hidden(X1,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 18.17/18.42  fof(c_0_30, plain, ![X37, X38]:k3_tarski(k2_tarski(X37,X38))=k2_xboole_0(X37,X38), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 18.17/18.42  fof(c_0_31, plain, ![X10, X11]:k4_xboole_0(X10,X11)=k5_xboole_0(X10,k3_xboole_0(X10,X11)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 18.17/18.42  cnf(c_0_32, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 18.17/18.42  cnf(c_0_33, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 18.17/18.42  cnf(c_0_34, plain, (r2_hidden(k4_tarski(X1,esk2_3(X3,X2,X1)),X3)|~r2_hidden(X1,X2)|X2!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 18.17/18.42  cnf(c_0_35, negated_conjecture, (r2_hidden(k4_tarski(X1,X2),esk6_0)|~r2_hidden(X2,k11_relat_1(esk6_0,X1))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 18.17/18.42  cnf(c_0_36, negated_conjecture, (r2_hidden(esk1_1(k11_relat_1(esk6_0,esk5_0)),k11_relat_1(esk6_0,esk5_0))|r2_hidden(esk5_0,k1_relat_1(esk6_0))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 18.17/18.42  cnf(c_0_37, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)), inference(er,[status(thm)],[c_0_29])).
% 18.17/18.42  fof(c_0_38, plain, ![X15, X16]:k4_xboole_0(X15,k2_xboole_0(X15,X16))=k1_xboole_0, inference(variable_rename,[status(thm)],[t46_xboole_1])).
% 18.17/18.42  cnf(c_0_39, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 18.17/18.42  cnf(c_0_40, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 18.17/18.42  cnf(c_0_41, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_32, c_0_33])).
% 18.17/18.42  fof(c_0_42, plain, ![X27, X28, X29]:k3_enumset1(X27,X27,X27,X28,X29)=k1_enumset1(X27,X28,X29), inference(variable_rename,[status(thm)],[t78_enumset1])).
% 18.17/18.42  fof(c_0_43, plain, ![X30, X31, X32, X33, X34]:k5_enumset1(X30,X30,X30,X31,X32,X33,X34)=k3_enumset1(X30,X31,X32,X33,X34), inference(variable_rename,[status(thm)],[t80_enumset1])).
% 18.17/18.42  fof(c_0_44, plain, ![X20, X21, X22, X23, X24, X25, X26]:k6_enumset1(X20,X20,X21,X22,X23,X24,X25,X26)=k5_enumset1(X20,X21,X22,X23,X24,X25,X26), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 18.17/18.42  fof(c_0_45, plain, ![X12, X13]:k3_xboole_0(X12,k2_xboole_0(X12,X13))=X12, inference(variable_rename,[status(thm)],[t21_xboole_1])).
% 18.17/18.42  fof(c_0_46, plain, ![X35, X36]:((~r1_tarski(k1_tarski(X35),X36)|r2_hidden(X35,X36))&(~r2_hidden(X35,X36)|r1_tarski(k1_tarski(X35),X36))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).
% 18.17/18.42  fof(c_0_47, plain, ![X17]:k2_tarski(X17,X17)=k1_tarski(X17), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 18.17/18.42  cnf(c_0_48, plain, (r2_hidden(X2,k11_relat_1(X3,X1))|~r2_hidden(k4_tarski(X1,X2),X3)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 18.17/18.42  cnf(c_0_49, plain, (r2_hidden(k4_tarski(X1,esk2_3(X2,k1_relat_1(X2),X1)),X2)|~r2_hidden(X1,k1_relat_1(X2))), inference(er,[status(thm)],[c_0_34])).
% 18.17/18.42  cnf(c_0_50, negated_conjecture, (r2_hidden(esk5_0,k1_relat_1(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37])).
% 18.17/18.42  cnf(c_0_51, negated_conjecture, (k11_relat_1(esk6_0,esk5_0)=k1_xboole_0|~r2_hidden(esk5_0,k1_relat_1(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 18.17/18.42  fof(c_0_52, plain, ![X41, X42]:((k4_xboole_0(k1_tarski(X41),k1_tarski(X42))!=k1_tarski(X41)|X41!=X42)&(X41=X42|k4_xboole_0(k1_tarski(X41),k1_tarski(X42))=k1_tarski(X41))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_zfmisc_1])])).
% 18.17/18.42  fof(c_0_53, plain, ![X39, X40]:k3_xboole_0(k1_tarski(X39),k2_tarski(X39,X40))=k1_tarski(X39), inference(variable_rename,[status(thm)],[t19_zfmisc_1])).
% 18.17/18.42  cnf(c_0_54, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_38])).
% 18.17/18.42  cnf(c_0_55, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_39, c_0_33])).
% 18.17/18.42  cnf(c_0_56, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))), inference(rw,[status(thm)],[c_0_40, c_0_41])).
% 18.17/18.42  cnf(c_0_57, plain, (k3_enumset1(X1,X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 18.17/18.42  cnf(c_0_58, plain, (k5_enumset1(X1,X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 18.17/18.42  cnf(c_0_59, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 18.17/18.42  cnf(c_0_60, plain, (k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_45])).
% 18.17/18.42  cnf(c_0_61, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 18.17/18.42  cnf(c_0_62, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 18.17/18.42  cnf(c_0_63, negated_conjecture, (r2_hidden(X1,k11_relat_1(esk6_0,X2))|~r2_hidden(k4_tarski(X2,X1),esk6_0)), inference(spm,[status(thm)],[c_0_48, c_0_26])).
% 18.17/18.42  cnf(c_0_64, negated_conjecture, (r2_hidden(k4_tarski(esk5_0,esk2_3(esk6_0,k1_relat_1(esk6_0),esk5_0)),esk6_0)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 18.17/18.42  cnf(c_0_65, negated_conjecture, (k11_relat_1(esk6_0,esk5_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_50])])).
% 18.17/18.42  cnf(c_0_66, plain, (k4_xboole_0(k1_tarski(X1),k1_tarski(X2))!=k1_tarski(X1)|X1!=X2), inference(split_conjunct,[status(thm)],[c_0_52])).
% 18.17/18.42  cnf(c_0_67, plain, (k3_xboole_0(k1_tarski(X1),k2_tarski(X1,X2))=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 18.17/18.42  cnf(c_0_68, plain, (k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_55]), c_0_56]), c_0_57]), c_0_57]), c_0_58]), c_0_58]), c_0_59]), c_0_59])).
% 18.17/18.42  cnf(c_0_69, plain, (k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_55]), c_0_41]), c_0_57]), c_0_57]), c_0_58]), c_0_58]), c_0_59]), c_0_59])).
% 18.17/18.42  fof(c_0_70, plain, ![X14]:(~r1_tarski(X14,k1_xboole_0)|X14=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).
% 18.17/18.42  cnf(c_0_71, plain, (r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_62]), c_0_33]), c_0_57]), c_0_58]), c_0_59])).
% 18.17/18.42  cnf(c_0_72, negated_conjecture, (r2_hidden(esk2_3(esk6_0,k1_relat_1(esk6_0),esk5_0),k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_65])).
% 18.17/18.42  cnf(c_0_73, plain, (X1!=X2|k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))))!=k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_62]), c_0_62]), c_0_62]), c_0_33]), c_0_33]), c_0_33]), c_0_56]), c_0_57]), c_0_57]), c_0_57]), c_0_57]), c_0_57]), c_0_57]), c_0_58]), c_0_58]), c_0_58]), c_0_58]), c_0_58]), c_0_58]), c_0_58]), c_0_58]), c_0_59]), c_0_59]), c_0_59]), c_0_59]), c_0_59]), c_0_59]), c_0_59]), c_0_59]), c_0_59]), c_0_59])).
% 18.17/18.42  cnf(c_0_74, plain, (k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))=k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67, c_0_62]), c_0_62]), c_0_33]), c_0_33]), c_0_33]), c_0_41]), c_0_57]), c_0_57]), c_0_57]), c_0_57]), c_0_57]), c_0_58]), c_0_58]), c_0_58]), c_0_58]), c_0_58]), c_0_58]), c_0_58]), c_0_59]), c_0_59]), c_0_59]), c_0_59]), c_0_59]), c_0_59]), c_0_59]), c_0_59]), c_0_59])).
% 18.17/18.42  cnf(c_0_75, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[c_0_68, c_0_69])).
% 18.17/18.42  cnf(c_0_76, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 18.17/18.42  cnf(c_0_77, negated_conjecture, (r1_tarski(k6_enumset1(esk2_3(esk6_0,k1_relat_1(esk6_0),esk5_0),esk2_3(esk6_0,k1_relat_1(esk6_0),esk5_0),esk2_3(esk6_0,k1_relat_1(esk6_0),esk5_0),esk2_3(esk6_0,k1_relat_1(esk6_0),esk5_0),esk2_3(esk6_0,k1_relat_1(esk6_0),esk5_0),esk2_3(esk6_0,k1_relat_1(esk6_0),esk5_0),esk2_3(esk6_0,k1_relat_1(esk6_0),esk5_0),esk2_3(esk6_0,k1_relat_1(esk6_0),esk5_0)),k1_xboole_0)), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 18.17/18.42  cnf(c_0_78, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_73]), c_0_74]), c_0_75])).
% 18.17/18.42  cnf(c_0_79, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_78]), ['proof']).
% 18.17/18.42  # SZS output end CNFRefutation
% 18.17/18.42  # Proof object total steps             : 80
% 18.17/18.42  # Proof object clause steps            : 43
% 18.17/18.42  # Proof object formula steps           : 37
% 18.17/18.42  # Proof object conjectures             : 15
% 18.17/18.42  # Proof object clause conjectures      : 12
% 18.17/18.42  # Proof object formula conjectures     : 3
% 18.17/18.42  # Proof object initial clauses used    : 22
% 18.17/18.42  # Proof object initial formulas used   : 18
% 18.17/18.42  # Proof object generating inferences   : 8
% 18.17/18.42  # Proof object simplifying inferences  : 93
% 18.17/18.42  # Training examples: 0 positive, 0 negative
% 18.17/18.42  # Parsed axioms                        : 18
% 18.17/18.42  # Removed by relevancy pruning/SinE    : 0
% 18.17/18.42  # Initial clauses                      : 26
% 18.17/18.42  # Removed in clause preprocessing      : 8
% 18.17/18.42  # Initial clauses in saturation        : 18
% 18.17/18.42  # Processed clauses                    : 5110
% 18.17/18.42  # ...of these trivial                  : 14
% 18.17/18.42  # ...subsumed                          : 4169
% 18.17/18.42  # ...remaining for further processing  : 927
% 18.17/18.42  # Other redundant clauses eliminated   : 195
% 18.17/18.42  # Clauses deleted for lack of memory   : 0
% 18.17/18.42  # Backward-subsumed                    : 108
% 18.17/18.42  # Backward-rewritten                   : 79
% 18.17/18.42  # Generated clauses                    : 336833
% 18.17/18.42  # ...of the previous two non-trivial   : 322078
% 18.17/18.42  # Contextual simplify-reflections      : 5
% 18.17/18.42  # Paramodulations                      : 336513
% 18.17/18.42  # Factorizations                       : 125
% 18.17/18.42  # Equation resolutions                 : 195
% 18.17/18.42  # Propositional unsat checks           : 0
% 18.17/18.42  #    Propositional check models        : 0
% 18.17/18.42  #    Propositional check unsatisfiable : 0
% 18.17/18.42  #    Propositional clauses             : 0
% 18.17/18.42  #    Propositional clauses after purity: 0
% 18.17/18.42  #    Propositional unsat core size     : 0
% 18.17/18.42  #    Propositional preprocessing time  : 0.000
% 18.17/18.42  #    Propositional encoding time       : 0.000
% 18.17/18.42  #    Propositional solver time         : 0.000
% 18.17/18.42  #    Success case prop preproc time    : 0.000
% 18.17/18.42  #    Success case prop encoding time   : 0.000
% 18.17/18.42  #    Success case prop solver time     : 0.000
% 18.17/18.42  # Current number of processed clauses  : 719
% 18.17/18.42  #    Positive orientable unit clauses  : 14
% 18.17/18.42  #    Positive unorientable unit clauses: 0
% 18.17/18.42  #    Negative unit clauses             : 1
% 18.17/18.42  #    Non-unit-clauses                  : 704
% 18.17/18.42  # Current number of unprocessed clauses: 316419
% 18.17/18.42  # ...number of literals in the above   : 2017417
% 18.17/18.42  # Current number of archived formulas  : 0
% 18.17/18.42  # Current number of archived clauses   : 213
% 18.17/18.42  # Clause-clause subsumption calls (NU) : 106453
% 18.17/18.42  # Rec. Clause-clause subsumption calls : 17032
% 18.17/18.42  # Non-unit clause-clause subsumptions  : 4280
% 18.17/18.42  # Unit Clause-clause subsumption calls : 722
% 18.17/18.42  # Rewrite failures with RHS unbound    : 0
% 18.17/18.42  # BW rewrite match attempts            : 158
% 18.17/18.42  # BW rewrite match successes           : 26
% 18.17/18.42  # Condensation attempts                : 0
% 18.17/18.42  # Condensation successes               : 0
% 18.17/18.42  # Termbank termtop insertions          : 117995457
% 18.17/18.43  
% 18.17/18.43  # -------------------------------------------------
% 18.17/18.43  # User time                : 17.900 s
% 18.17/18.43  # System time              : 0.161 s
% 18.17/18.43  # Total time               : 18.062 s
% 18.17/18.43  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
