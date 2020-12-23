%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:48:12 EST 2020

% Result     : Theorem 0.17s
% Output     : CNFRefutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :  102 (16490 expanded)
%              Number of clauses        :   73 (6263 expanded)
%              Number of leaves         :   14 (5016 expanded)
%              Depth                    :   35
%              Number of atoms          :  243 (25946 expanded)
%              Number of equality atoms :  125 (20810 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t23_relat_1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( X3 = k1_tarski(k4_tarski(X1,X2))
       => ( k1_relat_1(X3) = k1_tarski(X1)
          & k2_relat_1(X3) = k1_tarski(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_relat_1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(t129_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,k1_tarski(X4)))
    <=> ( r2_hidden(X1,X3)
        & X2 = X4 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_zfmisc_1)).

fof(t34_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k1_tarski(X3),k1_tarski(X4)))
    <=> ( X1 = X3
        & X2 = X4 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_zfmisc_1)).

fof(t128_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k1_tarski(X3),X4))
    <=> ( X1 = X3
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_zfmisc_1)).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ( X3 = k1_tarski(k4_tarski(X1,X2))
         => ( k1_relat_1(X3) = k1_tarski(X1)
            & k2_relat_1(X3) = k1_tarski(X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t23_relat_1])).

fof(c_0_15,plain,(
    ! [X8,X9,X10,X11,X12,X13] :
      ( ( ~ r2_hidden(X10,X9)
        | X10 = X8
        | X9 != k1_tarski(X8) )
      & ( X11 != X8
        | r2_hidden(X11,X9)
        | X9 != k1_tarski(X8) )
      & ( ~ r2_hidden(esk1_2(X12,X13),X13)
        | esk1_2(X12,X13) != X12
        | X13 = k1_tarski(X12) )
      & ( r2_hidden(esk1_2(X12,X13),X13)
        | esk1_2(X12,X13) = X12
        | X13 = k1_tarski(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_16,plain,(
    ! [X15] : k2_tarski(X15,X15) = k1_tarski(X15) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_17,plain,(
    ! [X16,X17] : k1_enumset1(X16,X16,X17) = k2_tarski(X16,X17) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_18,plain,(
    ! [X18,X19,X20] : k2_enumset1(X18,X18,X19,X20) = k1_enumset1(X18,X19,X20) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_19,plain,(
    ! [X21,X22,X23,X24] : k3_enumset1(X21,X21,X22,X23,X24) = k2_enumset1(X21,X22,X23,X24) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_20,plain,(
    ! [X25,X26,X27,X28,X29] : k4_enumset1(X25,X25,X26,X27,X28,X29) = k3_enumset1(X25,X26,X27,X28,X29) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_21,plain,(
    ! [X30,X31,X32,X33,X34,X35] : k5_enumset1(X30,X30,X31,X32,X33,X34,X35) = k4_enumset1(X30,X31,X32,X33,X34,X35) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_22,plain,(
    ! [X36,X37,X38,X39,X40,X41,X42] : k6_enumset1(X36,X36,X37,X38,X39,X40,X41,X42) = k5_enumset1(X36,X37,X38,X39,X40,X41,X42) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_23,negated_conjecture,
    ( v1_relat_1(esk12_0)
    & esk12_0 = k1_tarski(k4_tarski(esk10_0,esk11_0))
    & ( k1_relat_1(esk12_0) != k1_tarski(esk10_0)
      | k2_relat_1(esk12_0) != k1_tarski(esk11_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,negated_conjecture,
    ( k1_relat_1(esk12_0) != k1_tarski(esk10_0)
    | k2_relat_1(esk12_0) != k1_tarski(esk11_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | esk1_2(X1,X2) = X1
    | X2 = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_34,plain,(
    ! [X71,X72,X73,X75,X76,X77,X78,X80] :
      ( ( ~ r2_hidden(X73,X72)
        | r2_hidden(k4_tarski(esk7_3(X71,X72,X73),X73),X71)
        | X72 != k2_relat_1(X71) )
      & ( ~ r2_hidden(k4_tarski(X76,X75),X71)
        | r2_hidden(X75,X72)
        | X72 != k2_relat_1(X71) )
      & ( ~ r2_hidden(esk8_2(X77,X78),X78)
        | ~ r2_hidden(k4_tarski(X80,esk8_2(X77,X78)),X77)
        | X78 = k2_relat_1(X77) )
      & ( r2_hidden(esk8_2(X77,X78),X78)
        | r2_hidden(k4_tarski(esk9_2(X77,X78),esk8_2(X77,X78)),X77)
        | X78 = k2_relat_1(X77) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_25]),c_0_26]),c_0_27]),c_0_28]),c_0_29]),c_0_30]),c_0_31])).

cnf(c_0_36,negated_conjecture,
    ( esk12_0 = k1_tarski(k4_tarski(esk10_0,esk11_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_37,negated_conjecture,
    ( k1_relat_1(esk12_0) != k6_enumset1(esk10_0,esk10_0,esk10_0,esk10_0,esk10_0,esk10_0,esk10_0,esk10_0)
    | k2_relat_1(esk12_0) != k6_enumset1(esk11_0,esk11_0,esk11_0,esk11_0,esk11_0,esk11_0,esk11_0,esk11_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_25]),c_0_25]),c_0_26]),c_0_26]),c_0_27]),c_0_27]),c_0_28]),c_0_28]),c_0_29]),c_0_29]),c_0_30]),c_0_30]),c_0_31]),c_0_31])).

cnf(c_0_38,plain,
    ( esk1_2(X1,X2) = X1
    | X2 = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)
    | r2_hidden(esk1_2(X1,X2),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_25]),c_0_26]),c_0_27]),c_0_28]),c_0_29]),c_0_30]),c_0_31])).

cnf(c_0_39,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_35])])).

cnf(c_0_41,negated_conjecture,
    ( esk12_0 = k6_enumset1(k4_tarski(esk10_0,esk11_0),k4_tarski(esk10_0,esk11_0),k4_tarski(esk10_0,esk11_0),k4_tarski(esk10_0,esk11_0),k4_tarski(esk10_0,esk11_0),k4_tarski(esk10_0,esk11_0),k4_tarski(esk10_0,esk11_0),k4_tarski(esk10_0,esk11_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_25]),c_0_26]),c_0_27]),c_0_28]),c_0_29]),c_0_30]),c_0_31])).

cnf(c_0_42,plain,
    ( X2 = k1_tarski(X1)
    | ~ r2_hidden(esk1_2(X1,X2),X2)
    | esk1_2(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_43,negated_conjecture,
    ( esk1_2(esk11_0,k2_relat_1(esk12_0)) = esk11_0
    | r2_hidden(esk1_2(esk11_0,k2_relat_1(esk12_0)),k2_relat_1(esk12_0))
    | k6_enumset1(esk10_0,esk10_0,esk10_0,esk10_0,esk10_0,esk10_0,esk10_0,esk10_0) != k1_relat_1(esk12_0) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38])])).

cnf(c_0_44,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2) ),
    inference(er,[status(thm)],[c_0_39])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(k4_tarski(esk10_0,esk11_0),esk12_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

fof(c_0_46,plain,(
    ! [X60,X61,X62,X64,X65,X66,X67,X69] :
      ( ( ~ r2_hidden(X62,X61)
        | r2_hidden(k4_tarski(X62,esk4_3(X60,X61,X62)),X60)
        | X61 != k1_relat_1(X60) )
      & ( ~ r2_hidden(k4_tarski(X64,X65),X60)
        | r2_hidden(X64,X61)
        | X61 != k1_relat_1(X60) )
      & ( ~ r2_hidden(esk5_2(X66,X67),X67)
        | ~ r2_hidden(k4_tarski(esk5_2(X66,X67),X69),X66)
        | X67 = k1_relat_1(X66) )
      & ( r2_hidden(esk5_2(X66,X67),X67)
        | r2_hidden(k4_tarski(esk5_2(X66,X67),esk6_2(X66,X67)),X66)
        | X67 = k1_relat_1(X66) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

cnf(c_0_47,plain,
    ( X2 = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)
    | esk1_2(X1,X2) != X1
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_25]),c_0_26]),c_0_27]),c_0_28]),c_0_29]),c_0_30]),c_0_31])).

cnf(c_0_48,negated_conjecture,
    ( esk1_2(esk10_0,k1_relat_1(esk12_0)) = esk10_0
    | esk1_2(esk11_0,k2_relat_1(esk12_0)) = esk11_0
    | r2_hidden(esk1_2(esk10_0,k1_relat_1(esk12_0)),k1_relat_1(esk12_0))
    | r2_hidden(esk1_2(esk11_0,k2_relat_1(esk12_0)),k2_relat_1(esk12_0)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_38])])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk11_0,k2_relat_1(esk12_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_50,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_51,negated_conjecture,
    ( k6_enumset1(esk11_0,esk11_0,esk11_0,esk11_0,esk11_0,esk11_0,esk11_0,esk11_0) = k2_relat_1(esk12_0)
    | esk1_2(esk10_0,k1_relat_1(esk12_0)) = esk10_0
    | r2_hidden(esk1_2(esk11_0,k2_relat_1(esk12_0)),k2_relat_1(esk12_0))
    | r2_hidden(esk1_2(esk10_0,k1_relat_1(esk12_0)),k1_relat_1(esk12_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49])])).

cnf(c_0_52,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2) ),
    inference(er,[status(thm)],[c_0_50])).

cnf(c_0_53,negated_conjecture,
    ( esk1_2(esk10_0,k1_relat_1(esk12_0)) = esk10_0
    | r2_hidden(esk1_2(esk10_0,k1_relat_1(esk12_0)),k1_relat_1(esk12_0))
    | r2_hidden(esk1_2(esk11_0,k2_relat_1(esk12_0)),k2_relat_1(esk12_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_51]),c_0_38])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk10_0,k1_relat_1(esk12_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_45])).

cnf(c_0_55,negated_conjecture,
    ( k6_enumset1(esk10_0,esk10_0,esk10_0,esk10_0,esk10_0,esk10_0,esk10_0,esk10_0) = k1_relat_1(esk12_0)
    | r2_hidden(esk1_2(esk11_0,k2_relat_1(esk12_0)),k2_relat_1(esk12_0))
    | r2_hidden(esk1_2(esk10_0,k1_relat_1(esk12_0)),k1_relat_1(esk12_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_53]),c_0_54])])).

cnf(c_0_56,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_57,negated_conjecture,
    ( esk1_2(esk11_0,k2_relat_1(esk12_0)) = esk11_0
    | r2_hidden(esk1_2(esk10_0,k1_relat_1(esk12_0)),k1_relat_1(esk12_0))
    | r2_hidden(esk1_2(esk11_0,k2_relat_1(esk12_0)),k2_relat_1(esk12_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_55])).

cnf(c_0_58,plain,
    ( X1 = X3
    | X2 != k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_25]),c_0_26]),c_0_27]),c_0_28]),c_0_29]),c_0_30]),c_0_31])).

cnf(c_0_59,plain,
    ( r2_hidden(k4_tarski(esk7_3(X3,X2,X1),X1),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_60,negated_conjecture,
    ( k6_enumset1(esk11_0,esk11_0,esk11_0,esk11_0,esk11_0,esk11_0,esk11_0,esk11_0) = k2_relat_1(esk12_0)
    | r2_hidden(esk1_2(esk11_0,k2_relat_1(esk12_0)),k2_relat_1(esk12_0))
    | r2_hidden(esk1_2(esk10_0,k1_relat_1(esk12_0)),k1_relat_1(esk12_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_57]),c_0_49])])).

fof(c_0_61,plain,(
    ! [X52,X53,X54,X55] :
      ( ( r2_hidden(X52,X54)
        | ~ r2_hidden(k4_tarski(X52,X53),k2_zfmisc_1(X54,k1_tarski(X55))) )
      & ( X53 = X55
        | ~ r2_hidden(k4_tarski(X52,X53),k2_zfmisc_1(X54,k1_tarski(X55))) )
      & ( ~ r2_hidden(X52,X54)
        | X53 != X55
        | r2_hidden(k4_tarski(X52,X53),k2_zfmisc_1(X54,k1_tarski(X55))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t129_zfmisc_1])])])).

cnf(c_0_62,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_58])).

cnf(c_0_63,plain,
    ( r2_hidden(k4_tarski(esk7_3(X1,k2_relat_1(X1),X2),X2),X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_59])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(esk1_2(esk10_0,k1_relat_1(esk12_0)),k1_relat_1(esk12_0))
    | r2_hidden(esk1_2(esk11_0,k2_relat_1(esk12_0)),k2_relat_1(esk12_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_60]),c_0_55])).

fof(c_0_65,plain,(
    ! [X56,X57,X58,X59] :
      ( ( X56 = X58
        | ~ r2_hidden(k4_tarski(X56,X57),k2_zfmisc_1(k1_tarski(X58),k1_tarski(X59))) )
      & ( X57 = X59
        | ~ r2_hidden(k4_tarski(X56,X57),k2_zfmisc_1(k1_tarski(X58),k1_tarski(X59))) )
      & ( X56 != X58
        | X57 != X59
        | r2_hidden(k4_tarski(X56,X57),k2_zfmisc_1(k1_tarski(X58),k1_tarski(X59))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_zfmisc_1])])])).

cnf(c_0_66,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,k1_tarski(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_67,negated_conjecture,
    ( X1 = k4_tarski(esk10_0,esk11_0)
    | ~ r2_hidden(X1,esk12_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_41])).

cnf(c_0_68,negated_conjecture,
    ( r2_hidden(k4_tarski(esk7_3(esk12_0,k2_relat_1(esk12_0),esk1_2(esk11_0,k2_relat_1(esk12_0))),esk1_2(esk11_0,k2_relat_1(esk12_0))),esk12_0)
    | r2_hidden(esk1_2(esk10_0,k1_relat_1(esk12_0)),k1_relat_1(esk12_0)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_69,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X4)))
    | X1 != X2
    | X3 != X4 ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_70,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_25]),c_0_26]),c_0_27]),c_0_28]),c_0_29]),c_0_30]),c_0_31])).

cnf(c_0_71,negated_conjecture,
    ( k4_tarski(esk7_3(esk12_0,k2_relat_1(esk12_0),esk1_2(esk11_0,k2_relat_1(esk12_0))),esk1_2(esk11_0,k2_relat_1(esk12_0))) = k4_tarski(esk10_0,esk11_0)
    | r2_hidden(esk1_2(esk10_0,k1_relat_1(esk12_0)),k1_relat_1(esk12_0)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_72,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X4)))
    | X3 != X4
    | X1 != X2 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_25]),c_0_25]),c_0_26]),c_0_26]),c_0_27]),c_0_27]),c_0_28]),c_0_28]),c_0_29]),c_0_29]),c_0_30]),c_0_30]),c_0_31]),c_0_31])).

cnf(c_0_73,negated_conjecture,
    ( esk1_2(esk11_0,k2_relat_1(esk12_0)) = X1
    | r2_hidden(esk1_2(esk10_0,k1_relat_1(esk12_0)),k1_relat_1(esk12_0))
    | ~ r2_hidden(k4_tarski(esk10_0,esk11_0),k2_zfmisc_1(X2,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_74,plain,
    ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_72])])).

cnf(c_0_75,negated_conjecture,
    ( esk1_2(esk11_0,k2_relat_1(esk12_0)) = esk11_0
    | r2_hidden(esk1_2(esk10_0,k1_relat_1(esk12_0)),k1_relat_1(esk12_0)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_76,negated_conjecture,
    ( k6_enumset1(esk11_0,esk11_0,esk11_0,esk11_0,esk11_0,esk11_0,esk11_0,esk11_0) = k2_relat_1(esk12_0)
    | r2_hidden(esk1_2(esk10_0,k1_relat_1(esk12_0)),k1_relat_1(esk12_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_75]),c_0_49])])).

cnf(c_0_77,negated_conjecture,
    ( r2_hidden(esk1_2(esk10_0,k1_relat_1(esk12_0)),k1_relat_1(esk12_0))
    | k6_enumset1(esk10_0,esk10_0,esk10_0,esk10_0,esk10_0,esk10_0,esk10_0,esk10_0) != k1_relat_1(esk12_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_76])).

cnf(c_0_78,plain,
    ( r2_hidden(k4_tarski(X1,esk4_3(X3,X2,X1)),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_79,negated_conjecture,
    ( esk1_2(esk10_0,k1_relat_1(esk12_0)) = esk10_0
    | r2_hidden(esk1_2(esk10_0,k1_relat_1(esk12_0)),k1_relat_1(esk12_0)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_38])])).

fof(c_0_80,plain,(
    ! [X48,X49,X50,X51] :
      ( ( X48 = X50
        | ~ r2_hidden(k4_tarski(X48,X49),k2_zfmisc_1(k1_tarski(X50),X51)) )
      & ( r2_hidden(X49,X51)
        | ~ r2_hidden(k4_tarski(X48,X49),k2_zfmisc_1(k1_tarski(X50),X51)) )
      & ( X48 != X50
        | ~ r2_hidden(X49,X51)
        | r2_hidden(k4_tarski(X48,X49),k2_zfmisc_1(k1_tarski(X50),X51)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t128_zfmisc_1])])])).

cnf(c_0_81,plain,
    ( r2_hidden(k4_tarski(X1,esk4_3(X2,k1_relat_1(X2),X1)),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_78])).

cnf(c_0_82,negated_conjecture,
    ( r2_hidden(esk1_2(esk10_0,k1_relat_1(esk12_0)),k1_relat_1(esk12_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_79]),c_0_54])]),c_0_77])).

cnf(c_0_83,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(k1_tarski(X2),X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_84,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_2(esk10_0,k1_relat_1(esk12_0)),esk4_3(esk12_0,k1_relat_1(esk12_0),esk1_2(esk10_0,k1_relat_1(esk12_0)))),esk12_0) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_85,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),X4)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_83,c_0_25]),c_0_26]),c_0_27]),c_0_28]),c_0_29]),c_0_30]),c_0_31])).

cnf(c_0_86,negated_conjecture,
    ( k4_tarski(esk1_2(esk10_0,k1_relat_1(esk12_0)),esk4_3(esk12_0,k1_relat_1(esk12_0),esk1_2(esk10_0,k1_relat_1(esk12_0)))) = k4_tarski(esk10_0,esk11_0) ),
    inference(spm,[status(thm)],[c_0_67,c_0_84])).

cnf(c_0_87,negated_conjecture,
    ( esk1_2(esk10_0,k1_relat_1(esk12_0)) = X1
    | ~ r2_hidden(k4_tarski(esk10_0,esk11_0),k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)) ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_88,negated_conjecture,
    ( esk1_2(esk10_0,k1_relat_1(esk12_0)) = esk10_0 ),
    inference(spm,[status(thm)],[c_0_87,c_0_74])).

cnf(c_0_89,negated_conjecture,
    ( k6_enumset1(esk10_0,esk10_0,esk10_0,esk10_0,esk10_0,esk10_0,esk10_0,esk10_0) = k1_relat_1(esk12_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_88]),c_0_54])])).

cnf(c_0_90,negated_conjecture,
    ( esk1_2(esk11_0,k2_relat_1(esk12_0)) = esk11_0
    | r2_hidden(esk1_2(esk11_0,k2_relat_1(esk12_0)),k2_relat_1(esk12_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_89])])).

cnf(c_0_91,negated_conjecture,
    ( k6_enumset1(esk11_0,esk11_0,esk11_0,esk11_0,esk11_0,esk11_0,esk11_0,esk11_0) != k2_relat_1(esk12_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_89])])).

cnf(c_0_92,negated_conjecture,
    ( r2_hidden(esk1_2(esk11_0,k2_relat_1(esk12_0)),k2_relat_1(esk12_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_90]),c_0_49])]),c_0_91])).

cnf(c_0_93,negated_conjecture,
    ( r2_hidden(k4_tarski(esk7_3(esk12_0,k2_relat_1(esk12_0),esk1_2(esk11_0,k2_relat_1(esk12_0))),esk1_2(esk11_0,k2_relat_1(esk12_0))),esk12_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_92])).

cnf(c_0_94,negated_conjecture,
    ( X1 = esk10_0
    | ~ r2_hidden(X1,k1_relat_1(esk12_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_89])).

cnf(c_0_95,negated_conjecture,
    ( r2_hidden(esk7_3(esk12_0,k2_relat_1(esk12_0),esk1_2(esk11_0,k2_relat_1(esk12_0))),k1_relat_1(esk12_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_93])).

cnf(c_0_96,negated_conjecture,
    ( esk7_3(esk12_0,k2_relat_1(esk12_0),esk1_2(esk11_0,k2_relat_1(esk12_0))) = esk10_0 ),
    inference(spm,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_97,negated_conjecture,
    ( r2_hidden(k4_tarski(esk10_0,esk1_2(esk11_0,k2_relat_1(esk12_0))),esk12_0) ),
    inference(rw,[status(thm)],[c_0_93,c_0_96])).

cnf(c_0_98,negated_conjecture,
    ( k4_tarski(esk10_0,esk1_2(esk11_0,k2_relat_1(esk12_0))) = k4_tarski(esk10_0,esk11_0) ),
    inference(spm,[status(thm)],[c_0_67,c_0_97])).

cnf(c_0_99,negated_conjecture,
    ( esk1_2(esk11_0,k2_relat_1(esk12_0)) = X1
    | ~ r2_hidden(k4_tarski(esk10_0,esk11_0),k2_zfmisc_1(X2,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) ),
    inference(spm,[status(thm)],[c_0_70,c_0_98])).

cnf(c_0_100,negated_conjecture,
    ( esk1_2(esk11_0,k2_relat_1(esk12_0)) = esk11_0 ),
    inference(spm,[status(thm)],[c_0_99,c_0_74])).

cnf(c_0_101,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_100]),c_0_49])]),c_0_91]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.32  % Computer   : n017.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 11:09:16 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  # Version: 2.5pre002
% 0.11/0.32  # No SInE strategy applied
% 0.11/0.32  # Trying AutoSched0 for 299 seconds
% 0.17/0.45  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.17/0.45  # and selection function SelectNegativeLiterals.
% 0.17/0.45  #
% 0.17/0.45  # Preprocessing time       : 0.029 s
% 0.17/0.45  # Presaturation interreduction done
% 0.17/0.45  
% 0.17/0.45  # Proof found!
% 0.17/0.45  # SZS status Theorem
% 0.17/0.45  # SZS output start CNFRefutation
% 0.17/0.45  fof(t23_relat_1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>(X3=k1_tarski(k4_tarski(X1,X2))=>(k1_relat_1(X3)=k1_tarski(X1)&k2_relat_1(X3)=k1_tarski(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_relat_1)).
% 0.17/0.45  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 0.17/0.45  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.17/0.45  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.17/0.45  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.17/0.45  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.17/0.45  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.17/0.45  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.17/0.45  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.17/0.45  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 0.17/0.45  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 0.17/0.45  fof(t129_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,k1_tarski(X4)))<=>(r2_hidden(X1,X3)&X2=X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t129_zfmisc_1)).
% 0.17/0.45  fof(t34_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k1_tarski(X3),k1_tarski(X4)))<=>(X1=X3&X2=X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_zfmisc_1)).
% 0.17/0.45  fof(t128_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k1_tarski(X3),X4))<=>(X1=X3&r2_hidden(X2,X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t128_zfmisc_1)).
% 0.17/0.45  fof(c_0_14, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>(X3=k1_tarski(k4_tarski(X1,X2))=>(k1_relat_1(X3)=k1_tarski(X1)&k2_relat_1(X3)=k1_tarski(X2))))), inference(assume_negation,[status(cth)],[t23_relat_1])).
% 0.17/0.45  fof(c_0_15, plain, ![X8, X9, X10, X11, X12, X13]:(((~r2_hidden(X10,X9)|X10=X8|X9!=k1_tarski(X8))&(X11!=X8|r2_hidden(X11,X9)|X9!=k1_tarski(X8)))&((~r2_hidden(esk1_2(X12,X13),X13)|esk1_2(X12,X13)!=X12|X13=k1_tarski(X12))&(r2_hidden(esk1_2(X12,X13),X13)|esk1_2(X12,X13)=X12|X13=k1_tarski(X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.17/0.45  fof(c_0_16, plain, ![X15]:k2_tarski(X15,X15)=k1_tarski(X15), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.17/0.45  fof(c_0_17, plain, ![X16, X17]:k1_enumset1(X16,X16,X17)=k2_tarski(X16,X17), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.17/0.45  fof(c_0_18, plain, ![X18, X19, X20]:k2_enumset1(X18,X18,X19,X20)=k1_enumset1(X18,X19,X20), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.17/0.45  fof(c_0_19, plain, ![X21, X22, X23, X24]:k3_enumset1(X21,X21,X22,X23,X24)=k2_enumset1(X21,X22,X23,X24), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.17/0.45  fof(c_0_20, plain, ![X25, X26, X27, X28, X29]:k4_enumset1(X25,X25,X26,X27,X28,X29)=k3_enumset1(X25,X26,X27,X28,X29), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.17/0.45  fof(c_0_21, plain, ![X30, X31, X32, X33, X34, X35]:k5_enumset1(X30,X30,X31,X32,X33,X34,X35)=k4_enumset1(X30,X31,X32,X33,X34,X35), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.17/0.45  fof(c_0_22, plain, ![X36, X37, X38, X39, X40, X41, X42]:k6_enumset1(X36,X36,X37,X38,X39,X40,X41,X42)=k5_enumset1(X36,X37,X38,X39,X40,X41,X42), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.17/0.45  fof(c_0_23, negated_conjecture, (v1_relat_1(esk12_0)&(esk12_0=k1_tarski(k4_tarski(esk10_0,esk11_0))&(k1_relat_1(esk12_0)!=k1_tarski(esk10_0)|k2_relat_1(esk12_0)!=k1_tarski(esk11_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.17/0.45  cnf(c_0_24, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.17/0.45  cnf(c_0_25, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.17/0.45  cnf(c_0_26, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.17/0.45  cnf(c_0_27, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.17/0.45  cnf(c_0_28, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.17/0.45  cnf(c_0_29, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.17/0.45  cnf(c_0_30, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.17/0.45  cnf(c_0_31, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.17/0.45  cnf(c_0_32, negated_conjecture, (k1_relat_1(esk12_0)!=k1_tarski(esk10_0)|k2_relat_1(esk12_0)!=k1_tarski(esk11_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.17/0.45  cnf(c_0_33, plain, (r2_hidden(esk1_2(X1,X2),X2)|esk1_2(X1,X2)=X1|X2=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.17/0.45  fof(c_0_34, plain, ![X71, X72, X73, X75, X76, X77, X78, X80]:(((~r2_hidden(X73,X72)|r2_hidden(k4_tarski(esk7_3(X71,X72,X73),X73),X71)|X72!=k2_relat_1(X71))&(~r2_hidden(k4_tarski(X76,X75),X71)|r2_hidden(X75,X72)|X72!=k2_relat_1(X71)))&((~r2_hidden(esk8_2(X77,X78),X78)|~r2_hidden(k4_tarski(X80,esk8_2(X77,X78)),X77)|X78=k2_relat_1(X77))&(r2_hidden(esk8_2(X77,X78),X78)|r2_hidden(k4_tarski(esk9_2(X77,X78),esk8_2(X77,X78)),X77)|X78=k2_relat_1(X77)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 0.17/0.45  cnf(c_0_35, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_25]), c_0_26]), c_0_27]), c_0_28]), c_0_29]), c_0_30]), c_0_31])).
% 0.17/0.45  cnf(c_0_36, negated_conjecture, (esk12_0=k1_tarski(k4_tarski(esk10_0,esk11_0))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.17/0.45  cnf(c_0_37, negated_conjecture, (k1_relat_1(esk12_0)!=k6_enumset1(esk10_0,esk10_0,esk10_0,esk10_0,esk10_0,esk10_0,esk10_0,esk10_0)|k2_relat_1(esk12_0)!=k6_enumset1(esk11_0,esk11_0,esk11_0,esk11_0,esk11_0,esk11_0,esk11_0,esk11_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_25]), c_0_25]), c_0_26]), c_0_26]), c_0_27]), c_0_27]), c_0_28]), c_0_28]), c_0_29]), c_0_29]), c_0_30]), c_0_30]), c_0_31]), c_0_31])).
% 0.17/0.45  cnf(c_0_38, plain, (esk1_2(X1,X2)=X1|X2=k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)|r2_hidden(esk1_2(X1,X2),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_25]), c_0_26]), c_0_27]), c_0_28]), c_0_29]), c_0_30]), c_0_31])).
% 0.17/0.45  cnf(c_0_39, plain, (r2_hidden(X2,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.17/0.45  cnf(c_0_40, plain, (r2_hidden(X1,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_35])])).
% 0.17/0.45  cnf(c_0_41, negated_conjecture, (esk12_0=k6_enumset1(k4_tarski(esk10_0,esk11_0),k4_tarski(esk10_0,esk11_0),k4_tarski(esk10_0,esk11_0),k4_tarski(esk10_0,esk11_0),k4_tarski(esk10_0,esk11_0),k4_tarski(esk10_0,esk11_0),k4_tarski(esk10_0,esk11_0),k4_tarski(esk10_0,esk11_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_25]), c_0_26]), c_0_27]), c_0_28]), c_0_29]), c_0_30]), c_0_31])).
% 0.17/0.45  cnf(c_0_42, plain, (X2=k1_tarski(X1)|~r2_hidden(esk1_2(X1,X2),X2)|esk1_2(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.17/0.45  cnf(c_0_43, negated_conjecture, (esk1_2(esk11_0,k2_relat_1(esk12_0))=esk11_0|r2_hidden(esk1_2(esk11_0,k2_relat_1(esk12_0)),k2_relat_1(esk12_0))|k6_enumset1(esk10_0,esk10_0,esk10_0,esk10_0,esk10_0,esk10_0,esk10_0,esk10_0)!=k1_relat_1(esk12_0)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38])])).
% 0.17/0.45  cnf(c_0_44, plain, (r2_hidden(X1,k2_relat_1(X2))|~r2_hidden(k4_tarski(X3,X1),X2)), inference(er,[status(thm)],[c_0_39])).
% 0.17/0.45  cnf(c_0_45, negated_conjecture, (r2_hidden(k4_tarski(esk10_0,esk11_0),esk12_0)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.17/0.45  fof(c_0_46, plain, ![X60, X61, X62, X64, X65, X66, X67, X69]:(((~r2_hidden(X62,X61)|r2_hidden(k4_tarski(X62,esk4_3(X60,X61,X62)),X60)|X61!=k1_relat_1(X60))&(~r2_hidden(k4_tarski(X64,X65),X60)|r2_hidden(X64,X61)|X61!=k1_relat_1(X60)))&((~r2_hidden(esk5_2(X66,X67),X67)|~r2_hidden(k4_tarski(esk5_2(X66,X67),X69),X66)|X67=k1_relat_1(X66))&(r2_hidden(esk5_2(X66,X67),X67)|r2_hidden(k4_tarski(esk5_2(X66,X67),esk6_2(X66,X67)),X66)|X67=k1_relat_1(X66)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 0.17/0.45  cnf(c_0_47, plain, (X2=k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)|esk1_2(X1,X2)!=X1|~r2_hidden(esk1_2(X1,X2),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_25]), c_0_26]), c_0_27]), c_0_28]), c_0_29]), c_0_30]), c_0_31])).
% 0.17/0.45  cnf(c_0_48, negated_conjecture, (esk1_2(esk10_0,k1_relat_1(esk12_0))=esk10_0|esk1_2(esk11_0,k2_relat_1(esk12_0))=esk11_0|r2_hidden(esk1_2(esk10_0,k1_relat_1(esk12_0)),k1_relat_1(esk12_0))|r2_hidden(esk1_2(esk11_0,k2_relat_1(esk12_0)),k2_relat_1(esk12_0))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_38])])).
% 0.17/0.45  cnf(c_0_49, negated_conjecture, (r2_hidden(esk11_0,k2_relat_1(esk12_0))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.17/0.45  cnf(c_0_50, plain, (r2_hidden(X1,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.17/0.45  cnf(c_0_51, negated_conjecture, (k6_enumset1(esk11_0,esk11_0,esk11_0,esk11_0,esk11_0,esk11_0,esk11_0,esk11_0)=k2_relat_1(esk12_0)|esk1_2(esk10_0,k1_relat_1(esk12_0))=esk10_0|r2_hidden(esk1_2(esk11_0,k2_relat_1(esk12_0)),k2_relat_1(esk12_0))|r2_hidden(esk1_2(esk10_0,k1_relat_1(esk12_0)),k1_relat_1(esk12_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49])])).
% 0.17/0.45  cnf(c_0_52, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)), inference(er,[status(thm)],[c_0_50])).
% 0.17/0.45  cnf(c_0_53, negated_conjecture, (esk1_2(esk10_0,k1_relat_1(esk12_0))=esk10_0|r2_hidden(esk1_2(esk10_0,k1_relat_1(esk12_0)),k1_relat_1(esk12_0))|r2_hidden(esk1_2(esk11_0,k2_relat_1(esk12_0)),k2_relat_1(esk12_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_51]), c_0_38])).
% 0.17/0.45  cnf(c_0_54, negated_conjecture, (r2_hidden(esk10_0,k1_relat_1(esk12_0))), inference(spm,[status(thm)],[c_0_52, c_0_45])).
% 0.17/0.45  cnf(c_0_55, negated_conjecture, (k6_enumset1(esk10_0,esk10_0,esk10_0,esk10_0,esk10_0,esk10_0,esk10_0,esk10_0)=k1_relat_1(esk12_0)|r2_hidden(esk1_2(esk11_0,k2_relat_1(esk12_0)),k2_relat_1(esk12_0))|r2_hidden(esk1_2(esk10_0,k1_relat_1(esk12_0)),k1_relat_1(esk12_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_53]), c_0_54])])).
% 0.17/0.45  cnf(c_0_56, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.17/0.45  cnf(c_0_57, negated_conjecture, (esk1_2(esk11_0,k2_relat_1(esk12_0))=esk11_0|r2_hidden(esk1_2(esk10_0,k1_relat_1(esk12_0)),k1_relat_1(esk12_0))|r2_hidden(esk1_2(esk11_0,k2_relat_1(esk12_0)),k2_relat_1(esk12_0))), inference(spm,[status(thm)],[c_0_43, c_0_55])).
% 0.17/0.45  cnf(c_0_58, plain, (X1=X3|X2!=k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_25]), c_0_26]), c_0_27]), c_0_28]), c_0_29]), c_0_30]), c_0_31])).
% 0.17/0.45  cnf(c_0_59, plain, (r2_hidden(k4_tarski(esk7_3(X3,X2,X1),X1),X3)|~r2_hidden(X1,X2)|X2!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.17/0.45  cnf(c_0_60, negated_conjecture, (k6_enumset1(esk11_0,esk11_0,esk11_0,esk11_0,esk11_0,esk11_0,esk11_0,esk11_0)=k2_relat_1(esk12_0)|r2_hidden(esk1_2(esk11_0,k2_relat_1(esk12_0)),k2_relat_1(esk12_0))|r2_hidden(esk1_2(esk10_0,k1_relat_1(esk12_0)),k1_relat_1(esk12_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_57]), c_0_49])])).
% 0.17/0.45  fof(c_0_61, plain, ![X52, X53, X54, X55]:(((r2_hidden(X52,X54)|~r2_hidden(k4_tarski(X52,X53),k2_zfmisc_1(X54,k1_tarski(X55))))&(X53=X55|~r2_hidden(k4_tarski(X52,X53),k2_zfmisc_1(X54,k1_tarski(X55)))))&(~r2_hidden(X52,X54)|X53!=X55|r2_hidden(k4_tarski(X52,X53),k2_zfmisc_1(X54,k1_tarski(X55))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t129_zfmisc_1])])])).
% 0.17/0.45  cnf(c_0_62, plain, (X1=X2|~r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_58])).
% 0.17/0.45  cnf(c_0_63, plain, (r2_hidden(k4_tarski(esk7_3(X1,k2_relat_1(X1),X2),X2),X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_59])).
% 0.17/0.45  cnf(c_0_64, negated_conjecture, (r2_hidden(esk1_2(esk10_0,k1_relat_1(esk12_0)),k1_relat_1(esk12_0))|r2_hidden(esk1_2(esk11_0,k2_relat_1(esk12_0)),k2_relat_1(esk12_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_60]), c_0_55])).
% 0.17/0.45  fof(c_0_65, plain, ![X56, X57, X58, X59]:(((X56=X58|~r2_hidden(k4_tarski(X56,X57),k2_zfmisc_1(k1_tarski(X58),k1_tarski(X59))))&(X57=X59|~r2_hidden(k4_tarski(X56,X57),k2_zfmisc_1(k1_tarski(X58),k1_tarski(X59)))))&(X56!=X58|X57!=X59|r2_hidden(k4_tarski(X56,X57),k2_zfmisc_1(k1_tarski(X58),k1_tarski(X59))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_zfmisc_1])])])).
% 0.17/0.45  cnf(c_0_66, plain, (X1=X2|~r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,k1_tarski(X2)))), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.17/0.45  cnf(c_0_67, negated_conjecture, (X1=k4_tarski(esk10_0,esk11_0)|~r2_hidden(X1,esk12_0)), inference(spm,[status(thm)],[c_0_62, c_0_41])).
% 0.17/0.45  cnf(c_0_68, negated_conjecture, (r2_hidden(k4_tarski(esk7_3(esk12_0,k2_relat_1(esk12_0),esk1_2(esk11_0,k2_relat_1(esk12_0))),esk1_2(esk11_0,k2_relat_1(esk12_0))),esk12_0)|r2_hidden(esk1_2(esk10_0,k1_relat_1(esk12_0)),k1_relat_1(esk12_0))), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.17/0.45  cnf(c_0_69, plain, (r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X4)))|X1!=X2|X3!=X4), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.17/0.45  cnf(c_0_70, plain, (X1=X2|~r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_25]), c_0_26]), c_0_27]), c_0_28]), c_0_29]), c_0_30]), c_0_31])).
% 0.17/0.45  cnf(c_0_71, negated_conjecture, (k4_tarski(esk7_3(esk12_0,k2_relat_1(esk12_0),esk1_2(esk11_0,k2_relat_1(esk12_0))),esk1_2(esk11_0,k2_relat_1(esk12_0)))=k4_tarski(esk10_0,esk11_0)|r2_hidden(esk1_2(esk10_0,k1_relat_1(esk12_0)),k1_relat_1(esk12_0))), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.17/0.45  cnf(c_0_72, plain, (r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X4)))|X3!=X4|X1!=X2), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69, c_0_25]), c_0_25]), c_0_26]), c_0_26]), c_0_27]), c_0_27]), c_0_28]), c_0_28]), c_0_29]), c_0_29]), c_0_30]), c_0_30]), c_0_31]), c_0_31])).
% 0.17/0.45  cnf(c_0_73, negated_conjecture, (esk1_2(esk11_0,k2_relat_1(esk12_0))=X1|r2_hidden(esk1_2(esk10_0,k1_relat_1(esk12_0)),k1_relat_1(esk12_0))|~r2_hidden(k4_tarski(esk10_0,esk11_0),k2_zfmisc_1(X2,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 0.17/0.45  cnf(c_0_74, plain, (r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_72])])).
% 0.17/0.45  cnf(c_0_75, negated_conjecture, (esk1_2(esk11_0,k2_relat_1(esk12_0))=esk11_0|r2_hidden(esk1_2(esk10_0,k1_relat_1(esk12_0)),k1_relat_1(esk12_0))), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.17/0.45  cnf(c_0_76, negated_conjecture, (k6_enumset1(esk11_0,esk11_0,esk11_0,esk11_0,esk11_0,esk11_0,esk11_0,esk11_0)=k2_relat_1(esk12_0)|r2_hidden(esk1_2(esk10_0,k1_relat_1(esk12_0)),k1_relat_1(esk12_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_75]), c_0_49])])).
% 0.17/0.45  cnf(c_0_77, negated_conjecture, (r2_hidden(esk1_2(esk10_0,k1_relat_1(esk12_0)),k1_relat_1(esk12_0))|k6_enumset1(esk10_0,esk10_0,esk10_0,esk10_0,esk10_0,esk10_0,esk10_0,esk10_0)!=k1_relat_1(esk12_0)), inference(spm,[status(thm)],[c_0_37, c_0_76])).
% 0.17/0.45  cnf(c_0_78, plain, (r2_hidden(k4_tarski(X1,esk4_3(X3,X2,X1)),X3)|~r2_hidden(X1,X2)|X2!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.17/0.45  cnf(c_0_79, negated_conjecture, (esk1_2(esk10_0,k1_relat_1(esk12_0))=esk10_0|r2_hidden(esk1_2(esk10_0,k1_relat_1(esk12_0)),k1_relat_1(esk12_0))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_38])])).
% 0.17/0.45  fof(c_0_80, plain, ![X48, X49, X50, X51]:(((X48=X50|~r2_hidden(k4_tarski(X48,X49),k2_zfmisc_1(k1_tarski(X50),X51)))&(r2_hidden(X49,X51)|~r2_hidden(k4_tarski(X48,X49),k2_zfmisc_1(k1_tarski(X50),X51))))&(X48!=X50|~r2_hidden(X49,X51)|r2_hidden(k4_tarski(X48,X49),k2_zfmisc_1(k1_tarski(X50),X51)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t128_zfmisc_1])])])).
% 0.17/0.45  cnf(c_0_81, plain, (r2_hidden(k4_tarski(X1,esk4_3(X2,k1_relat_1(X2),X1)),X2)|~r2_hidden(X1,k1_relat_1(X2))), inference(er,[status(thm)],[c_0_78])).
% 0.17/0.45  cnf(c_0_82, negated_conjecture, (r2_hidden(esk1_2(esk10_0,k1_relat_1(esk12_0)),k1_relat_1(esk12_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_79]), c_0_54])]), c_0_77])).
% 0.17/0.45  cnf(c_0_83, plain, (X1=X2|~r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(k1_tarski(X2),X4))), inference(split_conjunct,[status(thm)],[c_0_80])).
% 0.17/0.45  cnf(c_0_84, negated_conjecture, (r2_hidden(k4_tarski(esk1_2(esk10_0,k1_relat_1(esk12_0)),esk4_3(esk12_0,k1_relat_1(esk12_0),esk1_2(esk10_0,k1_relat_1(esk12_0)))),esk12_0)), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 0.17/0.45  cnf(c_0_85, plain, (X1=X2|~r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),X4))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_83, c_0_25]), c_0_26]), c_0_27]), c_0_28]), c_0_29]), c_0_30]), c_0_31])).
% 0.17/0.45  cnf(c_0_86, negated_conjecture, (k4_tarski(esk1_2(esk10_0,k1_relat_1(esk12_0)),esk4_3(esk12_0,k1_relat_1(esk12_0),esk1_2(esk10_0,k1_relat_1(esk12_0))))=k4_tarski(esk10_0,esk11_0)), inference(spm,[status(thm)],[c_0_67, c_0_84])).
% 0.17/0.45  cnf(c_0_87, negated_conjecture, (esk1_2(esk10_0,k1_relat_1(esk12_0))=X1|~r2_hidden(k4_tarski(esk10_0,esk11_0),k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2))), inference(spm,[status(thm)],[c_0_85, c_0_86])).
% 0.17/0.45  cnf(c_0_88, negated_conjecture, (esk1_2(esk10_0,k1_relat_1(esk12_0))=esk10_0), inference(spm,[status(thm)],[c_0_87, c_0_74])).
% 0.17/0.45  cnf(c_0_89, negated_conjecture, (k6_enumset1(esk10_0,esk10_0,esk10_0,esk10_0,esk10_0,esk10_0,esk10_0,esk10_0)=k1_relat_1(esk12_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_88]), c_0_54])])).
% 0.17/0.45  cnf(c_0_90, negated_conjecture, (esk1_2(esk11_0,k2_relat_1(esk12_0))=esk11_0|r2_hidden(esk1_2(esk11_0,k2_relat_1(esk12_0)),k2_relat_1(esk12_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_89])])).
% 0.17/0.45  cnf(c_0_91, negated_conjecture, (k6_enumset1(esk11_0,esk11_0,esk11_0,esk11_0,esk11_0,esk11_0,esk11_0,esk11_0)!=k2_relat_1(esk12_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_89])])).
% 0.17/0.45  cnf(c_0_92, negated_conjecture, (r2_hidden(esk1_2(esk11_0,k2_relat_1(esk12_0)),k2_relat_1(esk12_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_90]), c_0_49])]), c_0_91])).
% 0.17/0.45  cnf(c_0_93, negated_conjecture, (r2_hidden(k4_tarski(esk7_3(esk12_0,k2_relat_1(esk12_0),esk1_2(esk11_0,k2_relat_1(esk12_0))),esk1_2(esk11_0,k2_relat_1(esk12_0))),esk12_0)), inference(spm,[status(thm)],[c_0_63, c_0_92])).
% 0.17/0.45  cnf(c_0_94, negated_conjecture, (X1=esk10_0|~r2_hidden(X1,k1_relat_1(esk12_0))), inference(spm,[status(thm)],[c_0_62, c_0_89])).
% 0.17/0.45  cnf(c_0_95, negated_conjecture, (r2_hidden(esk7_3(esk12_0,k2_relat_1(esk12_0),esk1_2(esk11_0,k2_relat_1(esk12_0))),k1_relat_1(esk12_0))), inference(spm,[status(thm)],[c_0_52, c_0_93])).
% 0.17/0.45  cnf(c_0_96, negated_conjecture, (esk7_3(esk12_0,k2_relat_1(esk12_0),esk1_2(esk11_0,k2_relat_1(esk12_0)))=esk10_0), inference(spm,[status(thm)],[c_0_94, c_0_95])).
% 0.17/0.45  cnf(c_0_97, negated_conjecture, (r2_hidden(k4_tarski(esk10_0,esk1_2(esk11_0,k2_relat_1(esk12_0))),esk12_0)), inference(rw,[status(thm)],[c_0_93, c_0_96])).
% 0.17/0.45  cnf(c_0_98, negated_conjecture, (k4_tarski(esk10_0,esk1_2(esk11_0,k2_relat_1(esk12_0)))=k4_tarski(esk10_0,esk11_0)), inference(spm,[status(thm)],[c_0_67, c_0_97])).
% 0.17/0.45  cnf(c_0_99, negated_conjecture, (esk1_2(esk11_0,k2_relat_1(esk12_0))=X1|~r2_hidden(k4_tarski(esk10_0,esk11_0),k2_zfmisc_1(X2,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))), inference(spm,[status(thm)],[c_0_70, c_0_98])).
% 0.17/0.45  cnf(c_0_100, negated_conjecture, (esk1_2(esk11_0,k2_relat_1(esk12_0))=esk11_0), inference(spm,[status(thm)],[c_0_99, c_0_74])).
% 0.17/0.45  cnf(c_0_101, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_100]), c_0_49])]), c_0_91]), ['proof']).
% 0.17/0.45  # SZS output end CNFRefutation
% 0.17/0.45  # Proof object total steps             : 102
% 0.17/0.45  # Proof object clause steps            : 73
% 0.17/0.45  # Proof object formula steps           : 29
% 0.17/0.45  # Proof object conjectures             : 44
% 0.17/0.45  # Proof object clause conjectures      : 41
% 0.17/0.45  # Proof object formula conjectures     : 3
% 0.17/0.45  # Proof object initial clauses used    : 20
% 0.17/0.45  # Proof object initial formulas used   : 14
% 0.17/0.45  # Proof object generating inferences   : 34
% 0.17/0.45  # Proof object simplifying inferences  : 115
% 0.17/0.45  # Training examples: 0 positive, 0 negative
% 0.17/0.45  # Parsed axioms                        : 15
% 0.17/0.45  # Removed by relevancy pruning/SinE    : 0
% 0.17/0.45  # Initial clauses                      : 32
% 0.17/0.45  # Removed in clause preprocessing      : 7
% 0.17/0.45  # Initial clauses in saturation        : 25
% 0.17/0.45  # Processed clauses                    : 416
% 0.17/0.45  # ...of these trivial                  : 9
% 0.17/0.45  # ...subsumed                          : 124
% 0.17/0.45  # ...remaining for further processing  : 283
% 0.17/0.45  # Other redundant clauses eliminated   : 23
% 0.17/0.45  # Clauses deleted for lack of memory   : 0
% 0.17/0.45  # Backward-subsumed                    : 13
% 0.17/0.45  # Backward-rewritten                   : 99
% 0.17/0.45  # Generated clauses                    : 5294
% 0.17/0.45  # ...of the previous two non-trivial   : 5094
% 0.17/0.45  # Contextual simplify-reflections      : 4
% 0.17/0.45  # Paramodulations                      : 5271
% 0.17/0.45  # Factorizations                       : 2
% 0.17/0.45  # Equation resolutions                 : 23
% 0.17/0.45  # Propositional unsat checks           : 0
% 0.17/0.45  #    Propositional check models        : 0
% 0.17/0.45  #    Propositional check unsatisfiable : 0
% 0.17/0.45  #    Propositional clauses             : 0
% 0.17/0.45  #    Propositional clauses after purity: 0
% 0.17/0.45  #    Propositional unsat core size     : 0
% 0.17/0.45  #    Propositional preprocessing time  : 0.000
% 0.17/0.45  #    Propositional encoding time       : 0.000
% 0.17/0.45  #    Propositional solver time         : 0.000
% 0.17/0.45  #    Success case prop preproc time    : 0.000
% 0.17/0.45  #    Success case prop encoding time   : 0.000
% 0.17/0.45  #    Success case prop solver time     : 0.000
% 0.17/0.45  # Current number of processed clauses  : 139
% 0.17/0.45  #    Positive orientable unit clauses  : 48
% 0.17/0.45  #    Positive unorientable unit clauses: 0
% 0.17/0.45  #    Negative unit clauses             : 1
% 0.17/0.45  #    Non-unit-clauses                  : 90
% 0.17/0.45  # Current number of unprocessed clauses: 4614
% 0.17/0.45  # ...number of literals in the above   : 20278
% 0.17/0.45  # Current number of archived formulas  : 0
% 0.17/0.45  # Current number of archived clauses   : 142
% 0.17/0.45  # Clause-clause subsumption calls (NU) : 3281
% 0.17/0.45  # Rec. Clause-clause subsumption calls : 2477
% 0.17/0.45  # Non-unit clause-clause subsumptions  : 141
% 0.17/0.45  # Unit Clause-clause subsumption calls : 226
% 0.17/0.45  # Rewrite failures with RHS unbound    : 0
% 0.17/0.45  # BW rewrite match attempts            : 55
% 0.17/0.45  # BW rewrite match successes           : 25
% 0.17/0.45  # Condensation attempts                : 0
% 0.17/0.45  # Condensation successes               : 0
% 0.17/0.45  # Termbank termtop insertions          : 121643
% 0.17/0.45  
% 0.17/0.45  # -------------------------------------------------
% 0.17/0.45  # User time                : 0.126 s
% 0.17/0.45  # System time              : 0.007 s
% 0.17/0.45  # Total time               : 0.133 s
% 0.17/0.45  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
