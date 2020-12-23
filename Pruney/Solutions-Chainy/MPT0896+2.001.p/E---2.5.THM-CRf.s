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
% DateTime   : Thu Dec  3 10:59:58 EST 2020

% Result     : Theorem 0.68s
% Output     : CNFRefutation 0.68s
% Verified   : 
% Statistics : Number of formulae       :  199 (2393 expanded)
%              Number of clauses        :  137 (1003 expanded)
%              Number of leaves         :   31 ( 619 expanded)
%              Depth                    :   25
%              Number of atoms          :  528 (8403 expanded)
%              Number of equality atoms :  383 (7572 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal clause size      :   15 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t56_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k4_zfmisc_1(X1,X2,X3,X4) = k4_zfmisc_1(X5,X6,X7,X8)
     => ( X1 = k1_xboole_0
        | X2 = k1_xboole_0
        | X3 = k1_xboole_0
        | X4 = k1_xboole_0
        | ( X1 = X5
          & X2 = X6
          & X3 = X7
          & X4 = X8 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_mcart_1)).

fof(t53_mcart_1,axiom,(
    ! [X1,X2,X3,X4] : k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_mcart_1)).

fof(t195_relat_1,axiom,(
    ! [X1,X2] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & ~ ( k1_relat_1(k2_zfmisc_1(X1,X2)) = X1
            & k2_relat_1(k2_zfmisc_1(X1,X2)) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t195_relat_1)).

fof(fc3_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X2)
     => v1_xboole_0(k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_zfmisc_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t55_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & X4 != k1_xboole_0 )
    <=> k4_zfmisc_1(X1,X2,X3,X4) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_mcart_1)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

fof(t36_mcart_1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( k3_zfmisc_1(X1,X2,X3) = k3_zfmisc_1(X4,X5,X6)
     => ( X1 = k1_xboole_0
        | X2 = k1_xboole_0
        | X3 = k1_xboole_0
        | ( X1 = X4
          & X2 = X5
          & X3 = X6 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_mcart_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(t35_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0 )
    <=> k3_zfmisc_1(X1,X2,X3) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_mcart_1)).

fof(t139_zfmisc_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2,X3,X4] :
          ( ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))
            | r1_tarski(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X4,X3)) )
         => r1_tarski(X2,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_zfmisc_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t82_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t66_xboole_1,axiom,(
    ! [X1] :
      ( ~ ( ~ r1_xboole_0(X1,X1)
          & X1 = k1_xboole_0 )
      & ~ ( X1 != k1_xboole_0
          & r1_xboole_0(X1,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(t65_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,k1_tarski(X2)) = X1
    <=> ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(t82_enumset1,axiom,(
    ! [X1] : k2_enumset1(X1,X1,X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_enumset1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t107_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k5_xboole_0(X2,X3))
    <=> ( r1_tarski(X1,k2_xboole_0(X2,X3))
        & r1_xboole_0(X1,k3_xboole_0(X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_xboole_1)).

fof(t106_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k4_xboole_0(X2,X3))
     => ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(t194_relat_1,axiom,(
    ! [X1,X2] : r1_tarski(k2_relat_1(k2_zfmisc_1(X1,X2)),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t194_relat_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t193_relat_1,axiom,(
    ! [X1,X2] : r1_tarski(k1_relat_1(k2_zfmisc_1(X1,X2)),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t193_relat_1)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(c_0_31,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6,X7,X8] :
        ( k4_zfmisc_1(X1,X2,X3,X4) = k4_zfmisc_1(X5,X6,X7,X8)
       => ( X1 = k1_xboole_0
          | X2 = k1_xboole_0
          | X3 = k1_xboole_0
          | X4 = k1_xboole_0
          | ( X1 = X5
            & X2 = X6
            & X3 = X7
            & X4 = X8 ) ) ) ),
    inference(assume_negation,[status(cth)],[t56_mcart_1])).

fof(c_0_32,negated_conjecture,
    ( k4_zfmisc_1(esk4_0,esk5_0,esk6_0,esk7_0) = k4_zfmisc_1(esk8_0,esk9_0,esk10_0,esk11_0)
    & esk4_0 != k1_xboole_0
    & esk5_0 != k1_xboole_0
    & esk6_0 != k1_xboole_0
    & esk7_0 != k1_xboole_0
    & ( esk4_0 != esk8_0
      | esk5_0 != esk9_0
      | esk6_0 != esk10_0
      | esk7_0 != esk11_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_31])])])).

fof(c_0_33,plain,(
    ! [X116,X117,X118,X119] : k4_zfmisc_1(X116,X117,X118,X119) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X116,X117),X118),X119) ),
    inference(variable_rename,[status(thm)],[t53_mcart_1])).

fof(c_0_34,plain,(
    ! [X88,X89] :
      ( ( k1_relat_1(k2_zfmisc_1(X88,X89)) = X88
        | X88 = k1_xboole_0
        | X89 = k1_xboole_0 )
      & ( k2_relat_1(k2_zfmisc_1(X88,X89)) = X89
        | X88 = k1_xboole_0
        | X89 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t195_relat_1])])])).

cnf(c_0_35,negated_conjecture,
    ( k4_zfmisc_1(esk4_0,esk5_0,esk6_0,esk7_0) = k4_zfmisc_1(esk8_0,esk9_0,esk10_0,esk11_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_36,plain,
    ( k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_37,plain,(
    ! [X64,X65] :
      ( ~ v1_xboole_0(X65)
      | v1_xboole_0(k2_zfmisc_1(X64,X65)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc3_zfmisc_1])])).

cnf(c_0_38,plain,
    ( k2_relat_1(k2_zfmisc_1(X1,X2)) = X2
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_39,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0),esk10_0),esk11_0) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0),esk7_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_36]),c_0_36])).

fof(c_0_40,plain,(
    ! [X68,X69] :
      ( ( k2_zfmisc_1(X68,X69) != k1_xboole_0
        | X68 = k1_xboole_0
        | X69 = k1_xboole_0 )
      & ( X68 != k1_xboole_0
        | k2_zfmisc_1(X68,X69) = k1_xboole_0 )
      & ( X69 != k1_xboole_0
        | k2_zfmisc_1(X68,X69) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_41,plain,(
    ! [X120,X121,X122,X123] :
      ( ( X120 = k1_xboole_0
        | X121 = k1_xboole_0
        | X122 = k1_xboole_0
        | X123 = k1_xboole_0
        | k4_zfmisc_1(X120,X121,X122,X123) != k1_xboole_0 )
      & ( X120 != k1_xboole_0
        | k4_zfmisc_1(X120,X121,X122,X123) = k1_xboole_0 )
      & ( X121 != k1_xboole_0
        | k4_zfmisc_1(X120,X121,X122,X123) = k1_xboole_0 )
      & ( X122 != k1_xboole_0
        | k4_zfmisc_1(X120,X121,X122,X123) = k1_xboole_0 )
      & ( X123 != k1_xboole_0
        | k4_zfmisc_1(X120,X121,X122,X123) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_mcart_1])])])).

fof(c_0_42,plain,(
    ! [X56] :
      ( ~ v1_xboole_0(X56)
      | X56 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_43,plain,
    ( v1_xboole_0(k2_zfmisc_1(X2,X1))
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_44,negated_conjecture,
    ( k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0),esk7_0)) = esk11_0
    | k2_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0),esk10_0) = k1_xboole_0
    | esk11_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_45,negated_conjecture,
    ( esk7_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_46,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_47,plain,(
    ! [X98,X99,X100,X101,X102,X103] :
      ( ( X98 = X101
        | X98 = k1_xboole_0
        | X99 = k1_xboole_0
        | X100 = k1_xboole_0
        | k3_zfmisc_1(X98,X99,X100) != k3_zfmisc_1(X101,X102,X103) )
      & ( X99 = X102
        | X98 = k1_xboole_0
        | X99 = k1_xboole_0
        | X100 = k1_xboole_0
        | k3_zfmisc_1(X98,X99,X100) != k3_zfmisc_1(X101,X102,X103) )
      & ( X100 = X103
        | X98 = k1_xboole_0
        | X99 = k1_xboole_0
        | X100 = k1_xboole_0
        | k3_zfmisc_1(X98,X99,X100) != k3_zfmisc_1(X101,X102,X103) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t36_mcart_1])])])).

fof(c_0_48,plain,(
    ! [X92,X93,X94] : k3_zfmisc_1(X92,X93,X94) = k2_zfmisc_1(k2_zfmisc_1(X92,X93),X94) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

cnf(c_0_49,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | k4_zfmisc_1(X1,X2,X3,X4) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_50,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_51,negated_conjecture,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0),esk7_0))
    | ~ v1_xboole_0(esk11_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_39])).

fof(c_0_52,plain,(
    ! [X95,X96,X97] :
      ( ( X95 = k1_xboole_0
        | X96 = k1_xboole_0
        | X97 = k1_xboole_0
        | k3_zfmisc_1(X95,X96,X97) != k1_xboole_0 )
      & ( X95 != k1_xboole_0
        | k3_zfmisc_1(X95,X96,X97) = k1_xboole_0 )
      & ( X96 != k1_xboole_0
        | k3_zfmisc_1(X95,X96,X97) = k1_xboole_0 )
      & ( X97 != k1_xboole_0
        | k3_zfmisc_1(X95,X96,X97) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_mcart_1])])])).

cnf(c_0_53,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0),esk10_0) = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0) = k1_xboole_0
    | esk11_0 = k1_xboole_0
    | esk11_0 = esk7_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_44]),c_0_45])).

cnf(c_0_54,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_46])).

cnf(c_0_55,plain,
    ( X1 = X2
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X1 = k1_xboole_0
    | k3_zfmisc_1(X3,X4,X1) != k3_zfmisc_1(X5,X6,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_56,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

fof(c_0_57,plain,(
    ! [X76,X77,X78,X79] :
      ( ( ~ r1_tarski(k2_zfmisc_1(X76,X77),k2_zfmisc_1(X78,X79))
        | r1_tarski(X77,X79)
        | v1_xboole_0(X76) )
      & ( ~ r1_tarski(k2_zfmisc_1(X77,X76),k2_zfmisc_1(X79,X78))
        | r1_tarski(X77,X79)
        | v1_xboole_0(X76) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t139_zfmisc_1])])])])])).

cnf(c_0_58,plain,
    ( X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_49,c_0_36])).

cnf(c_0_59,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0),esk7_0) = k1_xboole_0
    | ~ v1_xboole_0(esk11_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_60,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_61,negated_conjecture,
    ( esk5_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_62,negated_conjecture,
    ( esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_63,plain,(
    ! [X31,X32] :
      ( ( r1_tarski(X31,X32)
        | X31 != X32 )
      & ( r1_tarski(X32,X31)
        | X31 != X32 )
      & ( ~ r1_tarski(X31,X32)
        | ~ r1_tarski(X32,X31)
        | X31 = X32 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_64,plain,(
    ! [X57,X58] : r1_xboole_0(k4_xboole_0(X57,X58),k4_xboole_0(X58,X57)) ),
    inference(variable_rename,[status(thm)],[t82_xboole_1])).

fof(c_0_65,plain,(
    ! [X39,X40] : k4_xboole_0(X39,X40) = k5_xboole_0(X39,k3_xboole_0(X39,X40)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_66,plain,(
    ! [X52] : k4_xboole_0(X52,k1_xboole_0) = X52 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_67,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | k3_zfmisc_1(X1,X2,X3) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_68,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | k2_zfmisc_1(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_69,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0),esk7_0) = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0) = k1_xboole_0
    | esk11_0 = esk7_0
    | esk11_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_53]),c_0_54])).

cnf(c_0_70,plain,
    ( X1 = X2
    | X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X1 = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(X3,X4),X1) != k2_zfmisc_1(k2_zfmisc_1(X5,X6),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_56]),c_0_56])).

cnf(c_0_71,plain,
    ( r1_tarski(X1,X3)
    | v1_xboole_0(X2)
    | ~ r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_72,negated_conjecture,
    ( ~ v1_xboole_0(esk11_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_60]),c_0_61]),c_0_62]),c_0_45])).

cnf(c_0_73,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

fof(c_0_74,plain,(
    ! [X53,X54] : k4_xboole_0(X53,k4_xboole_0(X53,X54)) = k3_xboole_0(X53,X54) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_75,plain,(
    ! [X55] :
      ( ( r1_xboole_0(X55,X55)
        | X55 != k1_xboole_0 )
      & ( X55 = k1_xboole_0
        | ~ r1_xboole_0(X55,X55) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t66_xboole_1])])])).

cnf(c_0_76,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_77,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_78,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

fof(c_0_79,plain,(
    ! [X51] : k3_xboole_0(X51,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

cnf(c_0_80,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_67,c_0_56])).

cnf(c_0_81,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0) = k1_xboole_0
    | esk11_0 = k1_xboole_0
    | esk11_0 = esk7_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_45])).

cnf(c_0_82,negated_conjecture,
    ( X1 = esk11_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X1 = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(X3,X2),X1) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_70,c_0_39])).

cnf(c_0_83,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0),esk10_0),X1)
    | ~ r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0),esk7_0),k2_zfmisc_1(X1,X2)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_39]),c_0_72])).

cnf(c_0_84,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_73])).

fof(c_0_85,plain,(
    ! [X80,X81] :
      ( ( k4_xboole_0(X80,k1_tarski(X81)) != X80
        | ~ r2_hidden(X81,X80) )
      & ( r2_hidden(X81,X80)
        | k4_xboole_0(X80,k1_tarski(X81)) = X80 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).

fof(c_0_86,plain,(
    ! [X63] : k2_enumset1(X63,X63,X63,X63) = k1_tarski(X63) ),
    inference(variable_rename,[status(thm)],[t82_enumset1])).

cnf(c_0_87,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_88,plain,
    ( X1 = k1_xboole_0
    | ~ r1_xboole_0(X1,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_89,plain,
    ( r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_77]),c_0_77])).

cnf(c_0_90,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[c_0_78,c_0_77])).

cnf(c_0_91,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

fof(c_0_92,plain,(
    ! [X49,X50] :
      ( ~ r1_tarski(X49,X50)
      | k3_xboole_0(X49,X50) = X49 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_93,negated_conjecture,
    ( esk11_0 = esk7_0
    | esk11_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_60]),c_0_61]),c_0_62])).

cnf(c_0_94,negated_conjecture,
    ( k2_zfmisc_1(esk4_0,esk5_0) = k1_xboole_0
    | esk11_0 = esk7_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_82]),c_0_62]),c_0_45])).

cnf(c_0_95,plain,
    ( r1_tarski(X2,X4)
    | v1_xboole_0(X1)
    | ~ r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_96,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0),esk10_0),k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0)) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_97,plain,
    ( k4_xboole_0(X1,k1_tarski(X2)) != X1
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

cnf(c_0_98,plain,
    ( k2_enumset1(X1,X1,X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_86])).

fof(c_0_99,plain,(
    ! [X23,X24] :
      ( ( ~ r1_xboole_0(X23,X24)
        | k3_xboole_0(X23,X24) = k1_xboole_0 )
      & ( k3_xboole_0(X23,X24) != k1_xboole_0
        | r1_xboole_0(X23,X24) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

fof(c_0_100,plain,(
    ! [X44,X45,X46] :
      ( ( r1_tarski(X44,k2_xboole_0(X45,X46))
        | ~ r1_tarski(X44,k5_xboole_0(X45,X46)) )
      & ( r1_xboole_0(X44,k3_xboole_0(X45,X46))
        | ~ r1_tarski(X44,k5_xboole_0(X45,X46)) )
      & ( ~ r1_tarski(X44,k2_xboole_0(X45,X46))
        | ~ r1_xboole_0(X44,k3_xboole_0(X45,X46))
        | r1_tarski(X44,k5_xboole_0(X45,X46)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t107_xboole_1])])])).

cnf(c_0_101,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_87,c_0_77]),c_0_77])).

cnf(c_0_102,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_103,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_104,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_92])).

cnf(c_0_105,plain,
    ( k1_relat_1(k2_zfmisc_1(X1,X2)) = X1
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_106,plain,(
    ! [X41,X42,X43] :
      ( ( r1_tarski(X41,X42)
        | ~ r1_tarski(X41,k4_xboole_0(X42,X43)) )
      & ( r1_xboole_0(X41,X43)
        | ~ r1_tarski(X41,k4_xboole_0(X42,X43)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).

fof(c_0_107,plain,(
    ! [X11,X12] : k3_xboole_0(X11,X12) = k3_xboole_0(X12,X11) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_108,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0),esk10_0),esk7_0) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0),esk7_0)
    | esk11_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_39,c_0_93])).

cnf(c_0_109,negated_conjecture,
    ( esk11_0 = esk7_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_94]),c_0_60]),c_0_61])).

cnf(c_0_110,negated_conjecture,
    ( r1_tarski(esk10_0,esk6_0)
    | v1_xboole_0(k2_zfmisc_1(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_95,c_0_96])).

cnf(c_0_111,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))) != X1
    | ~ r2_hidden(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_97,c_0_98]),c_0_77])).

cnf(c_0_112,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_99])).

cnf(c_0_113,plain,
    ( r1_xboole_0(X1,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_100])).

cnf(c_0_114,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_102]),c_0_91]),c_0_103])).

cnf(c_0_115,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_104]),c_0_84])])).

cnf(c_0_116,negated_conjecture,
    ( k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0),esk7_0)) = k2_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0),esk10_0)
    | k2_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0),esk10_0) = k1_xboole_0
    | esk11_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_105,c_0_39])).

cnf(c_0_117,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_106])).

cnf(c_0_118,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_107])).

cnf(c_0_119,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0),esk10_0),esk7_0) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0),esk7_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_108,c_0_109]),c_0_45])).

cnf(c_0_120,negated_conjecture,
    ( k2_zfmisc_1(esk8_0,esk9_0) = k1_xboole_0
    | r1_tarski(esk10_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_110])).

cnf(c_0_121,plain,
    ( ~ r1_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))
    | ~ r2_hidden(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_112]),c_0_103])])).

cnf(c_0_122,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_114]),c_0_115])).

fof(c_0_123,plain,(
    ! [X13,X14,X15] :
      ( ( ~ v1_xboole_0(X13)
        | ~ r2_hidden(X14,X13) )
      & ( r2_hidden(esk1_1(X15),X15)
        | v1_xboole_0(X15) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_124,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0),esk10_0) = k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0)
    | k2_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0),esk10_0) = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0) = k1_xboole_0
    | esk11_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_116]),c_0_45])).

fof(c_0_125,plain,(
    ! [X59,X60] :
      ( ( ~ r1_xboole_0(X59,X60)
        | k4_xboole_0(X59,X60) = X59 )
      & ( k4_xboole_0(X59,X60) != X59
        | r1_xboole_0(X59,X60) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

cnf(c_0_126,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,k5_xboole_0(X3,k3_xboole_0(X3,X2))) ),
    inference(rw,[status(thm)],[c_0_117,c_0_77])).

cnf(c_0_127,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_118,c_0_112])).

cnf(c_0_128,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0),esk7_0) = k1_xboole_0
    | r1_tarski(esk10_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_120]),c_0_54]),c_0_54])).

cnf(c_0_129,plain,
    ( ~ r1_tarski(X1,k1_xboole_0)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_121,c_0_122])).

cnf(c_0_130,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_123])).

fof(c_0_131,plain,(
    ! [X86,X87] : r1_tarski(k2_relat_1(k2_zfmisc_1(X86,X87)),X87) ),
    inference(variable_rename,[status(thm)],[t194_relat_1])).

cnf(c_0_132,negated_conjecture,
    ( k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0)) = esk10_0
    | k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0) = k1_xboole_0
    | k2_zfmisc_1(esk8_0,esk9_0) = k1_xboole_0
    | esk11_0 = k1_xboole_0
    | esk10_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_124]),c_0_68])).

fof(c_0_133,plain,(
    ! [X35,X36] :
      ( ( k4_xboole_0(X35,X36) != k1_xboole_0
        | r1_tarski(X35,X36) )
      & ( ~ r1_tarski(X35,X36)
        | k4_xboole_0(X35,X36) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_134,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_125])).

cnf(c_0_135,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X2,X3)
    | ~ r1_tarski(X1,X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126,c_0_127]),c_0_103])).

cnf(c_0_136,negated_conjecture,
    ( r1_tarski(esk10_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_128]),c_0_60]),c_0_61]),c_0_62]),c_0_45])).

cnf(c_0_137,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_50,c_0_43])).

cnf(c_0_138,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_129,c_0_130])).

cnf(c_0_139,negated_conjecture,
    ( k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0)) = k2_zfmisc_1(esk8_0,esk9_0)
    | k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0) = k1_xboole_0
    | k2_zfmisc_1(esk8_0,esk9_0) = k1_xboole_0
    | esk11_0 = k1_xboole_0
    | esk10_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_124]),c_0_68])).

cnf(c_0_140,plain,
    ( r1_tarski(k2_relat_1(k2_zfmisc_1(X1,X2)),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_131])).

cnf(c_0_141,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0) = k1_xboole_0
    | k2_zfmisc_1(esk8_0,esk9_0) = k1_xboole_0
    | k2_zfmisc_1(esk4_0,esk5_0) = k1_xboole_0
    | esk10_0 = k1_xboole_0
    | esk11_0 = k1_xboole_0
    | esk10_0 = esk6_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_132]),c_0_62])).

cnf(c_0_142,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_133])).

cnf(c_0_143,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_134,c_0_77])).

cnf(c_0_144,negated_conjecture,
    ( r1_xboole_0(esk10_0,X1)
    | ~ r1_xboole_0(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_135,c_0_136])).

cnf(c_0_145,plain,
    ( r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_126,c_0_84])).

cnf(c_0_146,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_137,c_0_138])).

cnf(c_0_147,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0) = k1_xboole_0
    | k2_zfmisc_1(esk8_0,esk9_0) = k2_zfmisc_1(esk4_0,esk5_0)
    | k2_zfmisc_1(esk8_0,esk9_0) = k1_xboole_0
    | k2_zfmisc_1(esk4_0,esk5_0) = k1_xboole_0
    | esk10_0 = k1_xboole_0
    | esk11_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_139]),c_0_62])).

cnf(c_0_148,negated_conjecture,
    ( r1_tarski(k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0),esk7_0)),esk11_0) ),
    inference(spm,[status(thm)],[c_0_140,c_0_39])).

cnf(c_0_149,negated_conjecture,
    ( k2_zfmisc_1(esk8_0,esk9_0) = k1_xboole_0
    | k2_zfmisc_1(esk4_0,esk5_0) = k1_xboole_0
    | esk10_0 = esk6_0
    | esk11_0 = k1_xboole_0
    | esk10_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_141]),c_0_62])).

cnf(c_0_150,plain,
    ( r1_tarski(X1,X2)
    | k5_xboole_0(X1,k3_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_142,c_0_77])).

cnf(c_0_151,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X2,X1)))) = k3_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_101,c_0_118])).

cnf(c_0_152,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_143,c_0_101])).

cnf(c_0_153,negated_conjecture,
    ( r1_xboole_0(esk10_0,k5_xboole_0(X1,k3_xboole_0(X1,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_144,c_0_145])).

cnf(c_0_154,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0),esk7_0) = k1_xboole_0
    | ~ r1_tarski(esk10_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_146]),c_0_54])).

cnf(c_0_155,negated_conjecture,
    ( k2_zfmisc_1(esk8_0,esk9_0) = k2_zfmisc_1(esk4_0,esk5_0)
    | k2_zfmisc_1(esk8_0,esk9_0) = k1_xboole_0
    | k2_zfmisc_1(esk4_0,esk5_0) = k1_xboole_0
    | esk11_0 = k1_xboole_0
    | esk10_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_147]),c_0_62])).

cnf(c_0_156,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0) = k1_xboole_0
    | r1_tarski(esk7_0,esk11_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_148,c_0_38]),c_0_45])).

fof(c_0_157,plain,(
    ! [X84,X85] : r1_tarski(k1_relat_1(k2_zfmisc_1(X84,X85)),X84) ),
    inference(variable_rename,[status(thm)],[t193_relat_1])).

cnf(c_0_158,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_159,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0),esk7_0) = k1_xboole_0
    | k2_zfmisc_1(esk4_0,esk5_0) = k1_xboole_0
    | esk10_0 = k1_xboole_0
    | esk11_0 = k1_xboole_0
    | esk10_0 = esk6_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_149]),c_0_54]),c_0_54])).

cnf(c_0_160,plain,
    ( r1_tarski(X1,k5_xboole_0(X1,k3_xboole_0(X2,X1)))
    | k3_xboole_0(X2,X1) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_150,c_0_151])).

cnf(c_0_161,negated_conjecture,
    ( k3_xboole_0(esk6_0,esk10_0) = esk10_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_152,c_0_153]),c_0_118])).

cnf(c_0_162,negated_conjecture,
    ( ~ r1_tarski(esk10_0,k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_154]),c_0_60]),c_0_61]),c_0_62]),c_0_45])).

cnf(c_0_163,negated_conjecture,
    ( k1_relat_1(k2_zfmisc_1(esk4_0,esk5_0)) = esk8_0
    | k2_zfmisc_1(esk4_0,esk5_0) = k1_xboole_0
    | esk10_0 = k1_xboole_0
    | esk11_0 = k1_xboole_0
    | esk9_0 = k1_xboole_0
    | esk8_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_155]),c_0_68])).

cnf(c_0_164,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_165,negated_conjecture,
    ( r1_tarski(esk7_0,esk11_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_156]),c_0_60]),c_0_61]),c_0_62])).

cnf(c_0_166,negated_conjecture,
    ( esk4_0 != esk8_0
    | esk5_0 != esk9_0
    | esk6_0 != esk10_0
    | esk7_0 != esk11_0 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_167,plain,
    ( r1_tarski(k1_relat_1(k2_zfmisc_1(X1,X2)),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_157])).

cnf(c_0_168,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_158])).

cnf(c_0_169,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_170,negated_conjecture,
    ( k2_zfmisc_1(esk4_0,esk5_0) = k1_xboole_0
    | esk10_0 = esk6_0
    | esk11_0 = k1_xboole_0
    | esk10_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_159]),c_0_62]),c_0_45])).

cnf(c_0_171,negated_conjecture,
    ( k2_zfmisc_1(esk8_0,esk9_0) = k2_zfmisc_1(esk4_0,esk5_0)
    | k2_zfmisc_1(esk4_0,esk5_0) = k1_xboole_0
    | k2_zfmisc_1(esk8_0,esk9_0) = k1_xboole_0
    | esk10_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_155,c_0_109]),c_0_45])).

cnf(c_0_172,negated_conjecture,
    ( esk10_0 != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_160,c_0_161]),c_0_115]),c_0_162])).

cnf(c_0_173,negated_conjecture,
    ( k2_zfmisc_1(esk4_0,esk5_0) = k1_xboole_0
    | esk8_0 = k1_xboole_0
    | esk9_0 = k1_xboole_0
    | esk11_0 = k1_xboole_0
    | esk10_0 = k1_xboole_0
    | esk8_0 = esk4_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_163]),c_0_60]),c_0_61])).

cnf(c_0_174,negated_conjecture,
    ( esk11_0 = esk7_0
    | ~ r1_tarski(esk11_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_164,c_0_165])).

cnf(c_0_175,negated_conjecture,
    ( esk11_0 = k1_xboole_0
    | esk8_0 != esk4_0
    | esk9_0 != esk5_0
    | esk10_0 != esk6_0 ),
    inference(spm,[status(thm)],[c_0_166,c_0_93])).

cnf(c_0_176,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_167,c_0_168]),c_0_169])).

cnf(c_0_177,negated_conjecture,
    ( esk10_0 = k1_xboole_0
    | esk11_0 = k1_xboole_0
    | esk10_0 = esk6_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_170]),c_0_60]),c_0_61])).

cnf(c_0_178,negated_conjecture,
    ( k2_zfmisc_1(esk8_0,esk9_0) = k2_zfmisc_1(esk4_0,esk5_0)
    | k2_zfmisc_1(esk8_0,esk9_0) = k1_xboole_0
    | k2_zfmisc_1(esk4_0,esk5_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[c_0_171,c_0_172])).

cnf(c_0_179,negated_conjecture,
    ( esk8_0 = esk4_0
    | esk10_0 = k1_xboole_0
    | esk11_0 = k1_xboole_0
    | esk9_0 = k1_xboole_0
    | esk8_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_173]),c_0_60]),c_0_61])).

cnf(c_0_180,negated_conjecture,
    ( esk8_0 != esk4_0
    | esk9_0 != esk5_0
    | esk10_0 != esk6_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_174,c_0_175]),c_0_176])]),c_0_45])).

cnf(c_0_181,negated_conjecture,
    ( esk10_0 = esk6_0
    | esk10_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_174,c_0_177]),c_0_176])]),c_0_45])).

cnf(c_0_182,negated_conjecture,
    ( k2_relat_1(k2_zfmisc_1(esk4_0,esk5_0)) = esk9_0
    | k2_zfmisc_1(esk4_0,esk5_0) = k1_xboole_0
    | esk9_0 = k1_xboole_0
    | esk8_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_178]),c_0_68])).

cnf(c_0_183,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0),esk7_0) = k1_xboole_0
    | ~ r1_tarski(esk9_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_146]),c_0_54]),c_0_54])).

cnf(c_0_184,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | esk9_0 = k1_xboole_0
    | esk10_0 = k1_xboole_0
    | esk8_0 = esk4_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_174,c_0_179]),c_0_176])]),c_0_45])).

cnf(c_0_185,negated_conjecture,
    ( esk10_0 = k1_xboole_0
    | esk8_0 != esk4_0
    | esk9_0 != esk5_0 ),
    inference(spm,[status(thm)],[c_0_180,c_0_181])).

cnf(c_0_186,negated_conjecture,
    ( k2_zfmisc_1(esk4_0,esk5_0) = k1_xboole_0
    | esk8_0 = k1_xboole_0
    | esk9_0 = k1_xboole_0
    | esk9_0 = esk5_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_182]),c_0_60]),c_0_61])).

cnf(c_0_187,negated_conjecture,
    ( ~ r1_tarski(esk9_0,k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_183]),c_0_60]),c_0_61]),c_0_62]),c_0_45])).

cnf(c_0_188,negated_conjecture,
    ( esk8_0 = esk4_0
    | esk9_0 = k1_xboole_0
    | esk8_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_162,c_0_184]),c_0_176])])).

cnf(c_0_189,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0),esk6_0),esk11_0) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0),esk7_0)
    | esk10_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_39,c_0_181])).

cnf(c_0_190,negated_conjecture,
    ( esk8_0 != esk4_0
    | esk9_0 != esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_162,c_0_185]),c_0_176])])).

cnf(c_0_191,negated_conjecture,
    ( esk9_0 = esk5_0
    | esk9_0 = k1_xboole_0
    | esk8_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_186]),c_0_60]),c_0_61])).

cnf(c_0_192,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | esk8_0 = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_187,c_0_188]),c_0_176])])).

cnf(c_0_193,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0),esk6_0),esk7_0) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0),esk7_0)
    | esk10_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_189,c_0_109])).

cnf(c_0_194,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | esk9_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_190,c_0_191]),c_0_192])).

cnf(c_0_195,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0),esk6_0),esk7_0) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0),esk7_0) ),
    inference(sr,[status(thm)],[c_0_193,c_0_172])).

cnf(c_0_196,negated_conjecture,
    ( esk8_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_187,c_0_194]),c_0_176])])).

cnf(c_0_197,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0),esk7_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_195,c_0_196]),c_0_54]),c_0_54]),c_0_54])).

cnf(c_0_198,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_197]),c_0_60]),c_0_61]),c_0_62]),c_0_45]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:33:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.68/0.88  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.68/0.88  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.68/0.88  #
% 0.68/0.88  # Preprocessing time       : 0.030 s
% 0.68/0.88  
% 0.68/0.88  # Proof found!
% 0.68/0.88  # SZS status Theorem
% 0.68/0.88  # SZS output start CNFRefutation
% 0.68/0.88  fof(t56_mcart_1, conjecture, ![X1, X2, X3, X4, X5, X6, X7, X8]:(k4_zfmisc_1(X1,X2,X3,X4)=k4_zfmisc_1(X5,X6,X7,X8)=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|(((X1=X5&X2=X6)&X3=X7)&X4=X8))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_mcart_1)).
% 0.68/0.88  fof(t53_mcart_1, axiom, ![X1, X2, X3, X4]:k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_mcart_1)).
% 0.68/0.88  fof(t195_relat_1, axiom, ![X1, X2]:~(((X1!=k1_xboole_0&X2!=k1_xboole_0)&~((k1_relat_1(k2_zfmisc_1(X1,X2))=X1&k2_relat_1(k2_zfmisc_1(X1,X2))=X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t195_relat_1)).
% 0.68/0.88  fof(fc3_zfmisc_1, axiom, ![X1, X2]:(v1_xboole_0(X2)=>v1_xboole_0(k2_zfmisc_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_zfmisc_1)).
% 0.68/0.88  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.68/0.88  fof(t55_mcart_1, axiom, ![X1, X2, X3, X4]:((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&X4!=k1_xboole_0)<=>k4_zfmisc_1(X1,X2,X3,X4)!=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_mcart_1)).
% 0.68/0.88  fof(t6_boole, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_boole)).
% 0.68/0.88  fof(t36_mcart_1, axiom, ![X1, X2, X3, X4, X5, X6]:(k3_zfmisc_1(X1,X2,X3)=k3_zfmisc_1(X4,X5,X6)=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|((X1=X4&X2=X5)&X3=X6))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_mcart_1)).
% 0.68/0.88  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 0.68/0.88  fof(t35_mcart_1, axiom, ![X1, X2, X3]:(((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)<=>k3_zfmisc_1(X1,X2,X3)!=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_mcart_1)).
% 0.68/0.88  fof(t139_zfmisc_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2, X3, X4]:((r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))|r1_tarski(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X4,X3)))=>r1_tarski(X2,X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_zfmisc_1)).
% 0.68/0.88  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.68/0.88  fof(t82_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_xboole_1)).
% 0.68/0.88  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.68/0.88  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 0.68/0.88  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.68/0.88  fof(t66_xboole_1, axiom, ![X1]:(~((~(r1_xboole_0(X1,X1))&X1=k1_xboole_0))&~((X1!=k1_xboole_0&r1_xboole_0(X1,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 0.68/0.88  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 0.68/0.88  fof(t65_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(X1,k1_tarski(X2))=X1<=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 0.68/0.88  fof(t82_enumset1, axiom, ![X1]:k2_enumset1(X1,X1,X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_enumset1)).
% 0.68/0.88  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.68/0.88  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.68/0.88  fof(t107_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k5_xboole_0(X2,X3))<=>(r1_tarski(X1,k2_xboole_0(X2,X3))&r1_xboole_0(X1,k3_xboole_0(X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t107_xboole_1)).
% 0.68/0.88  fof(t106_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k4_xboole_0(X2,X3))=>(r1_tarski(X1,X2)&r1_xboole_0(X1,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 0.68/0.88  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.68/0.88  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.68/0.88  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.68/0.88  fof(t194_relat_1, axiom, ![X1, X2]:r1_tarski(k2_relat_1(k2_zfmisc_1(X1,X2)),X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t194_relat_1)).
% 0.68/0.88  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.68/0.88  fof(t193_relat_1, axiom, ![X1, X2]:r1_tarski(k1_relat_1(k2_zfmisc_1(X1,X2)),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t193_relat_1)).
% 0.68/0.88  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 0.68/0.88  fof(c_0_31, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6, X7, X8]:(k4_zfmisc_1(X1,X2,X3,X4)=k4_zfmisc_1(X5,X6,X7,X8)=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|(((X1=X5&X2=X6)&X3=X7)&X4=X8)))), inference(assume_negation,[status(cth)],[t56_mcart_1])).
% 0.68/0.88  fof(c_0_32, negated_conjecture, (k4_zfmisc_1(esk4_0,esk5_0,esk6_0,esk7_0)=k4_zfmisc_1(esk8_0,esk9_0,esk10_0,esk11_0)&((((esk4_0!=k1_xboole_0&esk5_0!=k1_xboole_0)&esk6_0!=k1_xboole_0)&esk7_0!=k1_xboole_0)&(esk4_0!=esk8_0|esk5_0!=esk9_0|esk6_0!=esk10_0|esk7_0!=esk11_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_31])])])).
% 0.68/0.88  fof(c_0_33, plain, ![X116, X117, X118, X119]:k4_zfmisc_1(X116,X117,X118,X119)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X116,X117),X118),X119), inference(variable_rename,[status(thm)],[t53_mcart_1])).
% 0.68/0.88  fof(c_0_34, plain, ![X88, X89]:((k1_relat_1(k2_zfmisc_1(X88,X89))=X88|(X88=k1_xboole_0|X89=k1_xboole_0))&(k2_relat_1(k2_zfmisc_1(X88,X89))=X89|(X88=k1_xboole_0|X89=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t195_relat_1])])])).
% 0.68/0.88  cnf(c_0_35, negated_conjecture, (k4_zfmisc_1(esk4_0,esk5_0,esk6_0,esk7_0)=k4_zfmisc_1(esk8_0,esk9_0,esk10_0,esk11_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.68/0.88  cnf(c_0_36, plain, (k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.68/0.88  fof(c_0_37, plain, ![X64, X65]:(~v1_xboole_0(X65)|v1_xboole_0(k2_zfmisc_1(X64,X65))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc3_zfmisc_1])])).
% 0.68/0.88  cnf(c_0_38, plain, (k2_relat_1(k2_zfmisc_1(X1,X2))=X2|X1=k1_xboole_0|X2=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.68/0.88  cnf(c_0_39, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0),esk10_0),esk11_0)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0),esk7_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_36]), c_0_36])).
% 0.68/0.88  fof(c_0_40, plain, ![X68, X69]:((k2_zfmisc_1(X68,X69)!=k1_xboole_0|(X68=k1_xboole_0|X69=k1_xboole_0))&((X68!=k1_xboole_0|k2_zfmisc_1(X68,X69)=k1_xboole_0)&(X69!=k1_xboole_0|k2_zfmisc_1(X68,X69)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.68/0.88  fof(c_0_41, plain, ![X120, X121, X122, X123]:((X120=k1_xboole_0|X121=k1_xboole_0|X122=k1_xboole_0|X123=k1_xboole_0|k4_zfmisc_1(X120,X121,X122,X123)!=k1_xboole_0)&((((X120!=k1_xboole_0|k4_zfmisc_1(X120,X121,X122,X123)=k1_xboole_0)&(X121!=k1_xboole_0|k4_zfmisc_1(X120,X121,X122,X123)=k1_xboole_0))&(X122!=k1_xboole_0|k4_zfmisc_1(X120,X121,X122,X123)=k1_xboole_0))&(X123!=k1_xboole_0|k4_zfmisc_1(X120,X121,X122,X123)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_mcart_1])])])).
% 0.68/0.88  fof(c_0_42, plain, ![X56]:(~v1_xboole_0(X56)|X56=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).
% 0.68/0.88  cnf(c_0_43, plain, (v1_xboole_0(k2_zfmisc_1(X2,X1))|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.68/0.88  cnf(c_0_44, negated_conjecture, (k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0),esk7_0))=esk11_0|k2_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0),esk10_0)=k1_xboole_0|esk11_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.68/0.88  cnf(c_0_45, negated_conjecture, (esk7_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.68/0.88  cnf(c_0_46, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.68/0.88  fof(c_0_47, plain, ![X98, X99, X100, X101, X102, X103]:(((X98=X101|(X98=k1_xboole_0|X99=k1_xboole_0|X100=k1_xboole_0)|k3_zfmisc_1(X98,X99,X100)!=k3_zfmisc_1(X101,X102,X103))&(X99=X102|(X98=k1_xboole_0|X99=k1_xboole_0|X100=k1_xboole_0)|k3_zfmisc_1(X98,X99,X100)!=k3_zfmisc_1(X101,X102,X103)))&(X100=X103|(X98=k1_xboole_0|X99=k1_xboole_0|X100=k1_xboole_0)|k3_zfmisc_1(X98,X99,X100)!=k3_zfmisc_1(X101,X102,X103))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t36_mcart_1])])])).
% 0.68/0.88  fof(c_0_48, plain, ![X92, X93, X94]:k3_zfmisc_1(X92,X93,X94)=k2_zfmisc_1(k2_zfmisc_1(X92,X93),X94), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 0.68/0.88  cnf(c_0_49, plain, (X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|k4_zfmisc_1(X1,X2,X3,X4)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.68/0.88  cnf(c_0_50, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.68/0.88  cnf(c_0_51, negated_conjecture, (v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0),esk7_0))|~v1_xboole_0(esk11_0)), inference(spm,[status(thm)],[c_0_43, c_0_39])).
% 0.68/0.88  fof(c_0_52, plain, ![X95, X96, X97]:((X95=k1_xboole_0|X96=k1_xboole_0|X97=k1_xboole_0|k3_zfmisc_1(X95,X96,X97)!=k1_xboole_0)&(((X95!=k1_xboole_0|k3_zfmisc_1(X95,X96,X97)=k1_xboole_0)&(X96!=k1_xboole_0|k3_zfmisc_1(X95,X96,X97)=k1_xboole_0))&(X97!=k1_xboole_0|k3_zfmisc_1(X95,X96,X97)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_mcart_1])])])).
% 0.68/0.88  cnf(c_0_53, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0),esk10_0)=k1_xboole_0|k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0)=k1_xboole_0|esk11_0=k1_xboole_0|esk11_0=esk7_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_44]), c_0_45])).
% 0.68/0.88  cnf(c_0_54, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_46])).
% 0.68/0.88  cnf(c_0_55, plain, (X1=X2|X3=k1_xboole_0|X4=k1_xboole_0|X1=k1_xboole_0|k3_zfmisc_1(X3,X4,X1)!=k3_zfmisc_1(X5,X6,X2)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.68/0.88  cnf(c_0_56, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.68/0.88  fof(c_0_57, plain, ![X76, X77, X78, X79]:((~r1_tarski(k2_zfmisc_1(X76,X77),k2_zfmisc_1(X78,X79))|r1_tarski(X77,X79)|v1_xboole_0(X76))&(~r1_tarski(k2_zfmisc_1(X77,X76),k2_zfmisc_1(X79,X78))|r1_tarski(X77,X79)|v1_xboole_0(X76))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t139_zfmisc_1])])])])])).
% 0.68/0.88  cnf(c_0_58, plain, (X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_49, c_0_36])).
% 0.68/0.88  cnf(c_0_59, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0),esk7_0)=k1_xboole_0|~v1_xboole_0(esk11_0)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.68/0.88  cnf(c_0_60, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.68/0.88  cnf(c_0_61, negated_conjecture, (esk5_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.68/0.88  cnf(c_0_62, negated_conjecture, (esk6_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.68/0.88  fof(c_0_63, plain, ![X31, X32]:(((r1_tarski(X31,X32)|X31!=X32)&(r1_tarski(X32,X31)|X31!=X32))&(~r1_tarski(X31,X32)|~r1_tarski(X32,X31)|X31=X32)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.68/0.88  fof(c_0_64, plain, ![X57, X58]:r1_xboole_0(k4_xboole_0(X57,X58),k4_xboole_0(X58,X57)), inference(variable_rename,[status(thm)],[t82_xboole_1])).
% 0.68/0.88  fof(c_0_65, plain, ![X39, X40]:k4_xboole_0(X39,X40)=k5_xboole_0(X39,k3_xboole_0(X39,X40)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.68/0.88  fof(c_0_66, plain, ![X52]:k4_xboole_0(X52,k1_xboole_0)=X52, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.68/0.88  cnf(c_0_67, plain, (X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|k3_zfmisc_1(X1,X2,X3)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.68/0.88  cnf(c_0_68, plain, (X1=k1_xboole_0|X2=k1_xboole_0|k2_zfmisc_1(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.68/0.88  cnf(c_0_69, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0),esk7_0)=k1_xboole_0|k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0)=k1_xboole_0|esk11_0=esk7_0|esk11_0=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_53]), c_0_54])).
% 0.68/0.88  cnf(c_0_70, plain, (X1=X2|X4=k1_xboole_0|X3=k1_xboole_0|X1=k1_xboole_0|k2_zfmisc_1(k2_zfmisc_1(X3,X4),X1)!=k2_zfmisc_1(k2_zfmisc_1(X5,X6),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_56]), c_0_56])).
% 0.68/0.88  cnf(c_0_71, plain, (r1_tarski(X1,X3)|v1_xboole_0(X2)|~r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.68/0.88  cnf(c_0_72, negated_conjecture, (~v1_xboole_0(esk11_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_60]), c_0_61]), c_0_62]), c_0_45])).
% 0.68/0.88  cnf(c_0_73, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.68/0.88  fof(c_0_74, plain, ![X53, X54]:k4_xboole_0(X53,k4_xboole_0(X53,X54))=k3_xboole_0(X53,X54), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.68/0.88  fof(c_0_75, plain, ![X55]:((r1_xboole_0(X55,X55)|X55!=k1_xboole_0)&(X55=k1_xboole_0|~r1_xboole_0(X55,X55))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t66_xboole_1])])])).
% 0.68/0.88  cnf(c_0_76, plain, (r1_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.68/0.88  cnf(c_0_77, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.68/0.88  cnf(c_0_78, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.68/0.88  fof(c_0_79, plain, ![X51]:k3_xboole_0(X51,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.68/0.88  cnf(c_0_80, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_67, c_0_56])).
% 0.68/0.88  cnf(c_0_81, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0)=k1_xboole_0|esk11_0=k1_xboole_0|esk11_0=esk7_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_45])).
% 0.68/0.88  cnf(c_0_82, negated_conjecture, (X1=esk11_0|X2=k1_xboole_0|X3=k1_xboole_0|X1=k1_xboole_0|k2_zfmisc_1(k2_zfmisc_1(X3,X2),X1)!=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0),esk7_0)), inference(spm,[status(thm)],[c_0_70, c_0_39])).
% 0.68/0.88  cnf(c_0_83, negated_conjecture, (r1_tarski(k2_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0),esk10_0),X1)|~r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0),esk7_0),k2_zfmisc_1(X1,X2))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_39]), c_0_72])).
% 0.68/0.88  cnf(c_0_84, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_73])).
% 0.68/0.88  fof(c_0_85, plain, ![X80, X81]:((k4_xboole_0(X80,k1_tarski(X81))!=X80|~r2_hidden(X81,X80))&(r2_hidden(X81,X80)|k4_xboole_0(X80,k1_tarski(X81))=X80)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).
% 0.68/0.88  fof(c_0_86, plain, ![X63]:k2_enumset1(X63,X63,X63,X63)=k1_tarski(X63), inference(variable_rename,[status(thm)],[t82_enumset1])).
% 0.68/0.88  cnf(c_0_87, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.68/0.88  cnf(c_0_88, plain, (X1=k1_xboole_0|~r1_xboole_0(X1,X1)), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.68/0.88  cnf(c_0_89, plain, (r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76, c_0_77]), c_0_77])).
% 0.68/0.88  cnf(c_0_90, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[c_0_78, c_0_77])).
% 0.68/0.88  cnf(c_0_91, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_79])).
% 0.68/0.88  fof(c_0_92, plain, ![X49, X50]:(~r1_tarski(X49,X50)|k3_xboole_0(X49,X50)=X49), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.68/0.88  cnf(c_0_93, negated_conjecture, (esk11_0=esk7_0|esk11_0=k1_xboole_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_60]), c_0_61]), c_0_62])).
% 0.68/0.88  cnf(c_0_94, negated_conjecture, (k2_zfmisc_1(esk4_0,esk5_0)=k1_xboole_0|esk11_0=esk7_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_82]), c_0_62]), c_0_45])).
% 0.68/0.88  cnf(c_0_95, plain, (r1_tarski(X2,X4)|v1_xboole_0(X1)|~r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.68/0.88  cnf(c_0_96, negated_conjecture, (r1_tarski(k2_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0),esk10_0),k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0))), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 0.68/0.88  cnf(c_0_97, plain, (k4_xboole_0(X1,k1_tarski(X2))!=X1|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_85])).
% 0.68/0.88  cnf(c_0_98, plain, (k2_enumset1(X1,X1,X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_86])).
% 0.68/0.88  fof(c_0_99, plain, ![X23, X24]:((~r1_xboole_0(X23,X24)|k3_xboole_0(X23,X24)=k1_xboole_0)&(k3_xboole_0(X23,X24)!=k1_xboole_0|r1_xboole_0(X23,X24))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.68/0.88  fof(c_0_100, plain, ![X44, X45, X46]:(((r1_tarski(X44,k2_xboole_0(X45,X46))|~r1_tarski(X44,k5_xboole_0(X45,X46)))&(r1_xboole_0(X44,k3_xboole_0(X45,X46))|~r1_tarski(X44,k5_xboole_0(X45,X46))))&(~r1_tarski(X44,k2_xboole_0(X45,X46))|~r1_xboole_0(X44,k3_xboole_0(X45,X46))|r1_tarski(X44,k5_xboole_0(X45,X46)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t107_xboole_1])])])).
% 0.68/0.88  cnf(c_0_101, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_87, c_0_77]), c_0_77])).
% 0.68/0.88  cnf(c_0_102, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_88, c_0_89])).
% 0.68/0.88  cnf(c_0_103, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[c_0_90, c_0_91])).
% 0.68/0.88  cnf(c_0_104, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_92])).
% 0.68/0.88  cnf(c_0_105, plain, (k1_relat_1(k2_zfmisc_1(X1,X2))=X1|X1=k1_xboole_0|X2=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.68/0.88  fof(c_0_106, plain, ![X41, X42, X43]:((r1_tarski(X41,X42)|~r1_tarski(X41,k4_xboole_0(X42,X43)))&(r1_xboole_0(X41,X43)|~r1_tarski(X41,k4_xboole_0(X42,X43)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).
% 0.68/0.88  fof(c_0_107, plain, ![X11, X12]:k3_xboole_0(X11,X12)=k3_xboole_0(X12,X11), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.68/0.88  cnf(c_0_108, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0),esk10_0),esk7_0)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0),esk7_0)|esk11_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_39, c_0_93])).
% 0.68/0.88  cnf(c_0_109, negated_conjecture, (esk11_0=esk7_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_94]), c_0_60]), c_0_61])).
% 0.68/0.88  cnf(c_0_110, negated_conjecture, (r1_tarski(esk10_0,esk6_0)|v1_xboole_0(k2_zfmisc_1(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_95, c_0_96])).
% 0.68/0.88  cnf(c_0_111, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))!=X1|~r2_hidden(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_97, c_0_98]), c_0_77])).
% 0.68/0.88  cnf(c_0_112, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_99])).
% 0.68/0.88  cnf(c_0_113, plain, (r1_xboole_0(X1,k3_xboole_0(X2,X3))|~r1_tarski(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_100])).
% 0.68/0.88  cnf(c_0_114, plain, (k3_xboole_0(X1,X1)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_102]), c_0_91]), c_0_103])).
% 0.68/0.88  cnf(c_0_115, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_104]), c_0_84])])).
% 0.68/0.88  cnf(c_0_116, negated_conjecture, (k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0),esk7_0))=k2_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0),esk10_0)|k2_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0),esk10_0)=k1_xboole_0|esk11_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_105, c_0_39])).
% 0.68/0.88  cnf(c_0_117, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X1,k4_xboole_0(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_106])).
% 0.68/0.88  cnf(c_0_118, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_107])).
% 0.68/0.88  cnf(c_0_119, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0),esk10_0),esk7_0)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0),esk7_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_108, c_0_109]), c_0_45])).
% 0.68/0.88  cnf(c_0_120, negated_conjecture, (k2_zfmisc_1(esk8_0,esk9_0)=k1_xboole_0|r1_tarski(esk10_0,esk6_0)), inference(spm,[status(thm)],[c_0_50, c_0_110])).
% 0.68/0.88  cnf(c_0_121, plain, (~r1_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))|~r2_hidden(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_112]), c_0_103])])).
% 0.68/0.88  cnf(c_0_122, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_114]), c_0_115])).
% 0.68/0.88  fof(c_0_123, plain, ![X13, X14, X15]:((~v1_xboole_0(X13)|~r2_hidden(X14,X13))&(r2_hidden(esk1_1(X15),X15)|v1_xboole_0(X15))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.68/0.88  cnf(c_0_124, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0),esk10_0)=k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0)|k2_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0),esk10_0)=k1_xboole_0|k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0)=k1_xboole_0|esk11_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_116]), c_0_45])).
% 0.68/0.88  fof(c_0_125, plain, ![X59, X60]:((~r1_xboole_0(X59,X60)|k4_xboole_0(X59,X60)=X59)&(k4_xboole_0(X59,X60)!=X59|r1_xboole_0(X59,X60))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.68/0.88  cnf(c_0_126, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X1,k5_xboole_0(X3,k3_xboole_0(X3,X2)))), inference(rw,[status(thm)],[c_0_117, c_0_77])).
% 0.68/0.88  cnf(c_0_127, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_118, c_0_112])).
% 0.68/0.88  cnf(c_0_128, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0),esk7_0)=k1_xboole_0|r1_tarski(esk10_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119, c_0_120]), c_0_54]), c_0_54])).
% 0.68/0.88  cnf(c_0_129, plain, (~r1_tarski(X1,k1_xboole_0)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_121, c_0_122])).
% 0.68/0.88  cnf(c_0_130, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_123])).
% 0.68/0.88  fof(c_0_131, plain, ![X86, X87]:r1_tarski(k2_relat_1(k2_zfmisc_1(X86,X87)),X87), inference(variable_rename,[status(thm)],[t194_relat_1])).
% 0.68/0.88  cnf(c_0_132, negated_conjecture, (k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0))=esk10_0|k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0)=k1_xboole_0|k2_zfmisc_1(esk8_0,esk9_0)=k1_xboole_0|esk11_0=k1_xboole_0|esk10_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_124]), c_0_68])).
% 0.68/0.88  fof(c_0_133, plain, ![X35, X36]:((k4_xboole_0(X35,X36)!=k1_xboole_0|r1_tarski(X35,X36))&(~r1_tarski(X35,X36)|k4_xboole_0(X35,X36)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.68/0.88  cnf(c_0_134, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_125])).
% 0.68/0.88  cnf(c_0_135, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X2,X3)|~r1_tarski(X1,X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126, c_0_127]), c_0_103])).
% 0.68/0.88  cnf(c_0_136, negated_conjecture, (r1_tarski(esk10_0,esk6_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_128]), c_0_60]), c_0_61]), c_0_62]), c_0_45])).
% 0.68/0.88  cnf(c_0_137, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_50, c_0_43])).
% 0.68/0.88  cnf(c_0_138, plain, (v1_xboole_0(X1)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_129, c_0_130])).
% 0.68/0.88  cnf(c_0_139, negated_conjecture, (k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0))=k2_zfmisc_1(esk8_0,esk9_0)|k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0)=k1_xboole_0|k2_zfmisc_1(esk8_0,esk9_0)=k1_xboole_0|esk11_0=k1_xboole_0|esk10_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_124]), c_0_68])).
% 0.68/0.88  cnf(c_0_140, plain, (r1_tarski(k2_relat_1(k2_zfmisc_1(X1,X2)),X2)), inference(split_conjunct,[status(thm)],[c_0_131])).
% 0.68/0.88  cnf(c_0_141, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0)=k1_xboole_0|k2_zfmisc_1(esk8_0,esk9_0)=k1_xboole_0|k2_zfmisc_1(esk4_0,esk5_0)=k1_xboole_0|esk10_0=k1_xboole_0|esk11_0=k1_xboole_0|esk10_0=esk6_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_132]), c_0_62])).
% 0.68/0.88  cnf(c_0_142, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_133])).
% 0.68/0.88  cnf(c_0_143, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=X1|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_134, c_0_77])).
% 0.68/0.88  cnf(c_0_144, negated_conjecture, (r1_xboole_0(esk10_0,X1)|~r1_xboole_0(X1,esk6_0)), inference(spm,[status(thm)],[c_0_135, c_0_136])).
% 0.68/0.88  cnf(c_0_145, plain, (r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2)), inference(spm,[status(thm)],[c_0_126, c_0_84])).
% 0.68/0.88  cnf(c_0_146, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|~r1_tarski(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_137, c_0_138])).
% 0.68/0.88  cnf(c_0_147, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0)=k1_xboole_0|k2_zfmisc_1(esk8_0,esk9_0)=k2_zfmisc_1(esk4_0,esk5_0)|k2_zfmisc_1(esk8_0,esk9_0)=k1_xboole_0|k2_zfmisc_1(esk4_0,esk5_0)=k1_xboole_0|esk10_0=k1_xboole_0|esk11_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_139]), c_0_62])).
% 0.68/0.88  cnf(c_0_148, negated_conjecture, (r1_tarski(k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0),esk7_0)),esk11_0)), inference(spm,[status(thm)],[c_0_140, c_0_39])).
% 0.68/0.88  cnf(c_0_149, negated_conjecture, (k2_zfmisc_1(esk8_0,esk9_0)=k1_xboole_0|k2_zfmisc_1(esk4_0,esk5_0)=k1_xboole_0|esk10_0=esk6_0|esk11_0=k1_xboole_0|esk10_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_141]), c_0_62])).
% 0.68/0.88  cnf(c_0_150, plain, (r1_tarski(X1,X2)|k5_xboole_0(X1,k3_xboole_0(X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_142, c_0_77])).
% 0.68/0.88  cnf(c_0_151, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X2,X1))))=k3_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_101, c_0_118])).
% 0.68/0.88  cnf(c_0_152, plain, (k3_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_143, c_0_101])).
% 0.68/0.88  cnf(c_0_153, negated_conjecture, (r1_xboole_0(esk10_0,k5_xboole_0(X1,k3_xboole_0(X1,esk6_0)))), inference(spm,[status(thm)],[c_0_144, c_0_145])).
% 0.68/0.88  cnf(c_0_154, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0),esk7_0)=k1_xboole_0|~r1_tarski(esk10_0,k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_146]), c_0_54])).
% 0.68/0.88  cnf(c_0_155, negated_conjecture, (k2_zfmisc_1(esk8_0,esk9_0)=k2_zfmisc_1(esk4_0,esk5_0)|k2_zfmisc_1(esk8_0,esk9_0)=k1_xboole_0|k2_zfmisc_1(esk4_0,esk5_0)=k1_xboole_0|esk11_0=k1_xboole_0|esk10_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_147]), c_0_62])).
% 0.68/0.88  cnf(c_0_156, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0)=k1_xboole_0|r1_tarski(esk7_0,esk11_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_148, c_0_38]), c_0_45])).
% 0.68/0.88  fof(c_0_157, plain, ![X84, X85]:r1_tarski(k1_relat_1(k2_zfmisc_1(X84,X85)),X84), inference(variable_rename,[status(thm)],[t193_relat_1])).
% 0.68/0.88  cnf(c_0_158, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.68/0.88  cnf(c_0_159, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0),esk7_0)=k1_xboole_0|k2_zfmisc_1(esk4_0,esk5_0)=k1_xboole_0|esk10_0=k1_xboole_0|esk11_0=k1_xboole_0|esk10_0=esk6_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_149]), c_0_54]), c_0_54])).
% 0.68/0.88  cnf(c_0_160, plain, (r1_tarski(X1,k5_xboole_0(X1,k3_xboole_0(X2,X1)))|k3_xboole_0(X2,X1)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_150, c_0_151])).
% 0.68/0.88  cnf(c_0_161, negated_conjecture, (k3_xboole_0(esk6_0,esk10_0)=esk10_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_152, c_0_153]), c_0_118])).
% 0.68/0.88  cnf(c_0_162, negated_conjecture, (~r1_tarski(esk10_0,k1_xboole_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_154]), c_0_60]), c_0_61]), c_0_62]), c_0_45])).
% 0.68/0.88  cnf(c_0_163, negated_conjecture, (k1_relat_1(k2_zfmisc_1(esk4_0,esk5_0))=esk8_0|k2_zfmisc_1(esk4_0,esk5_0)=k1_xboole_0|esk10_0=k1_xboole_0|esk11_0=k1_xboole_0|esk9_0=k1_xboole_0|esk8_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_155]), c_0_68])).
% 0.68/0.88  cnf(c_0_164, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.68/0.88  cnf(c_0_165, negated_conjecture, (r1_tarski(esk7_0,esk11_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_156]), c_0_60]), c_0_61]), c_0_62])).
% 0.68/0.88  cnf(c_0_166, negated_conjecture, (esk4_0!=esk8_0|esk5_0!=esk9_0|esk6_0!=esk10_0|esk7_0!=esk11_0), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.68/0.88  cnf(c_0_167, plain, (r1_tarski(k1_relat_1(k2_zfmisc_1(X1,X2)),X1)), inference(split_conjunct,[status(thm)],[c_0_157])).
% 0.68/0.88  cnf(c_0_168, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_158])).
% 0.68/0.88  cnf(c_0_169, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.68/0.88  cnf(c_0_170, negated_conjecture, (k2_zfmisc_1(esk4_0,esk5_0)=k1_xboole_0|esk10_0=esk6_0|esk11_0=k1_xboole_0|esk10_0=k1_xboole_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_159]), c_0_62]), c_0_45])).
% 0.68/0.88  cnf(c_0_171, negated_conjecture, (k2_zfmisc_1(esk8_0,esk9_0)=k2_zfmisc_1(esk4_0,esk5_0)|k2_zfmisc_1(esk4_0,esk5_0)=k1_xboole_0|k2_zfmisc_1(esk8_0,esk9_0)=k1_xboole_0|esk10_0=k1_xboole_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_155, c_0_109]), c_0_45])).
% 0.68/0.88  cnf(c_0_172, negated_conjecture, (esk10_0!=k1_xboole_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_160, c_0_161]), c_0_115]), c_0_162])).
% 0.68/0.88  cnf(c_0_173, negated_conjecture, (k2_zfmisc_1(esk4_0,esk5_0)=k1_xboole_0|esk8_0=k1_xboole_0|esk9_0=k1_xboole_0|esk11_0=k1_xboole_0|esk10_0=k1_xboole_0|esk8_0=esk4_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_163]), c_0_60]), c_0_61])).
% 0.68/0.88  cnf(c_0_174, negated_conjecture, (esk11_0=esk7_0|~r1_tarski(esk11_0,esk7_0)), inference(spm,[status(thm)],[c_0_164, c_0_165])).
% 0.68/0.88  cnf(c_0_175, negated_conjecture, (esk11_0=k1_xboole_0|esk8_0!=esk4_0|esk9_0!=esk5_0|esk10_0!=esk6_0), inference(spm,[status(thm)],[c_0_166, c_0_93])).
% 0.68/0.88  cnf(c_0_176, plain, (r1_tarski(k1_xboole_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_167, c_0_168]), c_0_169])).
% 0.68/0.88  cnf(c_0_177, negated_conjecture, (esk10_0=k1_xboole_0|esk11_0=k1_xboole_0|esk10_0=esk6_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_170]), c_0_60]), c_0_61])).
% 0.68/0.88  cnf(c_0_178, negated_conjecture, (k2_zfmisc_1(esk8_0,esk9_0)=k2_zfmisc_1(esk4_0,esk5_0)|k2_zfmisc_1(esk8_0,esk9_0)=k1_xboole_0|k2_zfmisc_1(esk4_0,esk5_0)=k1_xboole_0), inference(sr,[status(thm)],[c_0_171, c_0_172])).
% 0.68/0.88  cnf(c_0_179, negated_conjecture, (esk8_0=esk4_0|esk10_0=k1_xboole_0|esk11_0=k1_xboole_0|esk9_0=k1_xboole_0|esk8_0=k1_xboole_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_173]), c_0_60]), c_0_61])).
% 0.68/0.88  cnf(c_0_180, negated_conjecture, (esk8_0!=esk4_0|esk9_0!=esk5_0|esk10_0!=esk6_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_174, c_0_175]), c_0_176])]), c_0_45])).
% 0.68/0.88  cnf(c_0_181, negated_conjecture, (esk10_0=esk6_0|esk10_0=k1_xboole_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_174, c_0_177]), c_0_176])]), c_0_45])).
% 0.68/0.88  cnf(c_0_182, negated_conjecture, (k2_relat_1(k2_zfmisc_1(esk4_0,esk5_0))=esk9_0|k2_zfmisc_1(esk4_0,esk5_0)=k1_xboole_0|esk9_0=k1_xboole_0|esk8_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_178]), c_0_68])).
% 0.68/0.88  cnf(c_0_183, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0),esk7_0)=k1_xboole_0|~r1_tarski(esk9_0,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_146]), c_0_54]), c_0_54])).
% 0.68/0.88  cnf(c_0_184, negated_conjecture, (esk8_0=k1_xboole_0|esk9_0=k1_xboole_0|esk10_0=k1_xboole_0|esk8_0=esk4_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_174, c_0_179]), c_0_176])]), c_0_45])).
% 0.68/0.88  cnf(c_0_185, negated_conjecture, (esk10_0=k1_xboole_0|esk8_0!=esk4_0|esk9_0!=esk5_0), inference(spm,[status(thm)],[c_0_180, c_0_181])).
% 0.68/0.88  cnf(c_0_186, negated_conjecture, (k2_zfmisc_1(esk4_0,esk5_0)=k1_xboole_0|esk8_0=k1_xboole_0|esk9_0=k1_xboole_0|esk9_0=esk5_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_182]), c_0_60]), c_0_61])).
% 0.68/0.88  cnf(c_0_187, negated_conjecture, (~r1_tarski(esk9_0,k1_xboole_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_183]), c_0_60]), c_0_61]), c_0_62]), c_0_45])).
% 0.68/0.88  cnf(c_0_188, negated_conjecture, (esk8_0=esk4_0|esk9_0=k1_xboole_0|esk8_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_162, c_0_184]), c_0_176])])).
% 0.68/0.88  cnf(c_0_189, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0),esk6_0),esk11_0)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0),esk7_0)|esk10_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_39, c_0_181])).
% 0.68/0.88  cnf(c_0_190, negated_conjecture, (esk8_0!=esk4_0|esk9_0!=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_162, c_0_185]), c_0_176])])).
% 0.68/0.88  cnf(c_0_191, negated_conjecture, (esk9_0=esk5_0|esk9_0=k1_xboole_0|esk8_0=k1_xboole_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_186]), c_0_60]), c_0_61])).
% 0.68/0.88  cnf(c_0_192, negated_conjecture, (esk8_0=k1_xboole_0|esk8_0=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_187, c_0_188]), c_0_176])])).
% 0.68/0.88  cnf(c_0_193, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0),esk6_0),esk7_0)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0),esk7_0)|esk10_0=k1_xboole_0), inference(rw,[status(thm)],[c_0_189, c_0_109])).
% 0.68/0.88  cnf(c_0_194, negated_conjecture, (esk8_0=k1_xboole_0|esk9_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_190, c_0_191]), c_0_192])).
% 0.68/0.88  cnf(c_0_195, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0),esk6_0),esk7_0)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0),esk7_0)), inference(sr,[status(thm)],[c_0_193, c_0_172])).
% 0.68/0.88  cnf(c_0_196, negated_conjecture, (esk8_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_187, c_0_194]), c_0_176])])).
% 0.68/0.88  cnf(c_0_197, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0),esk7_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_195, c_0_196]), c_0_54]), c_0_54]), c_0_54])).
% 0.68/0.88  cnf(c_0_198, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_197]), c_0_60]), c_0_61]), c_0_62]), c_0_45]), ['proof']).
% 0.68/0.88  # SZS output end CNFRefutation
% 0.68/0.88  # Proof object total steps             : 199
% 0.68/0.88  # Proof object clause steps            : 137
% 0.68/0.88  # Proof object formula steps           : 62
% 0.68/0.88  # Proof object conjectures             : 75
% 0.68/0.88  # Proof object clause conjectures      : 72
% 0.68/0.88  # Proof object formula conjectures     : 3
% 0.68/0.88  # Proof object initial clauses used    : 41
% 0.68/0.88  # Proof object initial formulas used   : 31
% 0.68/0.88  # Proof object generating inferences   : 75
% 0.68/0.88  # Proof object simplifying inferences  : 124
% 0.68/0.88  # Training examples: 0 positive, 0 negative
% 0.68/0.88  # Parsed axioms                        : 45
% 0.68/0.88  # Removed by relevancy pruning/SinE    : 0
% 0.68/0.88  # Initial clauses                      : 86
% 0.68/0.88  # Removed in clause preprocessing      : 5
% 0.68/0.88  # Initial clauses in saturation        : 81
% 0.68/0.88  # Processed clauses                    : 6629
% 0.68/0.88  # ...of these trivial                  : 761
% 0.68/0.88  # ...subsumed                          : 4614
% 0.68/0.88  # ...remaining for further processing  : 1254
% 0.68/0.88  # Other redundant clauses eliminated   : 126
% 0.68/0.88  # Clauses deleted for lack of memory   : 0
% 0.68/0.88  # Backward-subsumed                    : 154
% 0.68/0.88  # Backward-rewritten                   : 525
% 0.68/0.88  # Generated clauses                    : 54386
% 0.68/0.88  # ...of the previous two non-trivial   : 35117
% 0.68/0.88  # Contextual simplify-reflections      : 12
% 0.68/0.88  # Paramodulations                      : 54202
% 0.68/0.88  # Factorizations                       : 31
% 0.68/0.88  # Equation resolutions                 : 133
% 0.68/0.88  # Propositional unsat checks           : 0
% 0.68/0.88  #    Propositional check models        : 0
% 0.68/0.88  #    Propositional check unsatisfiable : 0
% 0.68/0.88  #    Propositional clauses             : 0
% 0.68/0.88  #    Propositional clauses after purity: 0
% 0.68/0.88  #    Propositional unsat core size     : 0
% 0.68/0.88  #    Propositional preprocessing time  : 0.000
% 0.68/0.88  #    Propositional encoding time       : 0.000
% 0.68/0.88  #    Propositional solver time         : 0.000
% 0.68/0.88  #    Success case prop preproc time    : 0.000
% 0.68/0.88  #    Success case prop encoding time   : 0.000
% 0.68/0.88  #    Success case prop solver time     : 0.000
% 0.68/0.88  # Current number of processed clauses  : 542
% 0.68/0.88  #    Positive orientable unit clauses  : 208
% 0.68/0.88  #    Positive unorientable unit clauses: 3
% 0.68/0.88  #    Negative unit clauses             : 17
% 0.68/0.88  #    Non-unit-clauses                  : 314
% 0.68/0.88  # Current number of unprocessed clauses: 27107
% 0.68/0.88  # ...number of literals in the above   : 91119
% 0.68/0.88  # Current number of archived formulas  : 0
% 0.68/0.88  # Current number of archived clauses   : 704
% 0.68/0.88  # Clause-clause subsumption calls (NU) : 52724
% 0.68/0.88  # Rec. Clause-clause subsumption calls : 38374
% 0.68/0.88  # Non-unit clause-clause subsumptions  : 3484
% 0.68/0.88  # Unit Clause-clause subsumption calls : 2182
% 0.68/0.88  # Rewrite failures with RHS unbound    : 0
% 0.68/0.88  # BW rewrite match attempts            : 546
% 0.68/0.88  # BW rewrite match successes           : 88
% 0.68/0.88  # Condensation attempts                : 0
% 0.68/0.88  # Condensation successes               : 0
% 0.68/0.88  # Termbank termtop insertions          : 538549
% 0.68/0.88  
% 0.68/0.88  # -------------------------------------------------
% 0.68/0.88  # User time                : 0.507 s
% 0.68/0.88  # System time              : 0.018 s
% 0.68/0.88  # Total time               : 0.525 s
% 0.68/0.88  # Maximum resident set size: 1620 pages
%------------------------------------------------------------------------------
