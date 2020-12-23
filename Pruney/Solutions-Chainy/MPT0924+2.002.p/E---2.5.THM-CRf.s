%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:32 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 686 expanded)
%              Number of clauses        :   52 ( 365 expanded)
%              Number of leaves         :    8 ( 156 expanded)
%              Depth                    :   14
%              Number of atoms          :  184 (2754 expanded)
%              Number of equality atoms :   47 (1146 expanded)
%              Maximal formula depth    :   23 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d2_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_zfmisc_1(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ? [X5,X6] :
              ( r2_hidden(X5,X1)
              & r2_hidden(X6,X2)
              & X4 = k4_tarski(X5,X6) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(t84_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] :
      ( r2_hidden(k4_mcart_1(X1,X2,X3,X4),k4_zfmisc_1(X5,X6,X7,X8))
    <=> ( r2_hidden(X1,X5)
        & r2_hidden(X2,X6)
        & r2_hidden(X3,X7)
        & r2_hidden(X4,X8) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_mcart_1)).

fof(d4_mcart_1,axiom,(
    ! [X1,X2,X3,X4] : k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k3_mcart_1(X1,X2,X3),X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_mcart_1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(d4_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(t10_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
     => ( r2_hidden(k1_mcart_1(X1),X2)
        & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(c_0_8,plain,(
    ! [X16,X17,X18,X19,X22,X23,X24,X25,X26,X27,X29,X30] :
      ( ( r2_hidden(esk2_4(X16,X17,X18,X19),X16)
        | ~ r2_hidden(X19,X18)
        | X18 != k2_zfmisc_1(X16,X17) )
      & ( r2_hidden(esk3_4(X16,X17,X18,X19),X17)
        | ~ r2_hidden(X19,X18)
        | X18 != k2_zfmisc_1(X16,X17) )
      & ( X19 = k4_tarski(esk2_4(X16,X17,X18,X19),esk3_4(X16,X17,X18,X19))
        | ~ r2_hidden(X19,X18)
        | X18 != k2_zfmisc_1(X16,X17) )
      & ( ~ r2_hidden(X23,X16)
        | ~ r2_hidden(X24,X17)
        | X22 != k4_tarski(X23,X24)
        | r2_hidden(X22,X18)
        | X18 != k2_zfmisc_1(X16,X17) )
      & ( ~ r2_hidden(esk4_3(X25,X26,X27),X27)
        | ~ r2_hidden(X29,X25)
        | ~ r2_hidden(X30,X26)
        | esk4_3(X25,X26,X27) != k4_tarski(X29,X30)
        | X27 = k2_zfmisc_1(X25,X26) )
      & ( r2_hidden(esk5_3(X25,X26,X27),X25)
        | r2_hidden(esk4_3(X25,X26,X27),X27)
        | X27 = k2_zfmisc_1(X25,X26) )
      & ( r2_hidden(esk6_3(X25,X26,X27),X26)
        | r2_hidden(esk4_3(X25,X26,X27),X27)
        | X27 = k2_zfmisc_1(X25,X26) )
      & ( esk4_3(X25,X26,X27) = k4_tarski(esk5_3(X25,X26,X27),esk6_3(X25,X26,X27))
        | r2_hidden(esk4_3(X25,X26,X27),X27)
        | X27 = k2_zfmisc_1(X25,X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).

fof(c_0_9,plain,(
    ! [X9,X10,X11,X12,X13,X14] :
      ( ( ~ r2_hidden(X11,X10)
        | X11 = X9
        | X10 != k1_tarski(X9) )
      & ( X12 != X9
        | r2_hidden(X12,X10)
        | X10 != k1_tarski(X9) )
      & ( ~ r2_hidden(esk1_2(X13,X14),X14)
        | esk1_2(X13,X14) != X13
        | X14 = k1_tarski(X13) )
      & ( r2_hidden(esk1_2(X13,X14),X14)
        | esk1_2(X13,X14) = X13
        | X14 = k1_tarski(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_10,plain,
    ( r2_hidden(X5,X6)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4)
    | X5 != k4_tarski(X1,X3)
    | X6 != k2_zfmisc_1(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6,X7,X8] :
        ( r2_hidden(k4_mcart_1(X1,X2,X3,X4),k4_zfmisc_1(X5,X6,X7,X8))
      <=> ( r2_hidden(X1,X5)
          & r2_hidden(X2,X6)
          & r2_hidden(X3,X7)
          & r2_hidden(X4,X8) ) ) ),
    inference(assume_negation,[status(cth)],[t84_mcart_1])).

fof(c_0_13,plain,(
    ! [X39,X40,X41,X42] : k4_mcart_1(X39,X40,X41,X42) = k4_tarski(k3_mcart_1(X39,X40,X41),X42) ),
    inference(variable_rename,[status(thm)],[d4_mcart_1])).

fof(c_0_14,plain,(
    ! [X33,X34,X35] : k3_mcart_1(X33,X34,X35) = k4_tarski(k4_tarski(X33,X34),X35) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

fof(c_0_15,plain,(
    ! [X43,X44,X45,X46] : k4_zfmisc_1(X43,X44,X45,X46) = k2_zfmisc_1(k3_zfmisc_1(X43,X44,X45),X46) ),
    inference(variable_rename,[status(thm)],[d4_zfmisc_1])).

fof(c_0_16,plain,(
    ! [X36,X37,X38] : k3_zfmisc_1(X36,X37,X38) = k2_zfmisc_1(k2_zfmisc_1(X36,X37),X38) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

cnf(c_0_17,plain,
    ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    | ~ r2_hidden(X2,X4)
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_10])])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,k1_tarski(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_11])])).

fof(c_0_19,negated_conjecture,
    ( ( ~ r2_hidden(k4_mcart_1(esk7_0,esk8_0,esk9_0,esk10_0),k4_zfmisc_1(esk11_0,esk12_0,esk13_0,esk14_0))
      | ~ r2_hidden(esk7_0,esk11_0)
      | ~ r2_hidden(esk8_0,esk12_0)
      | ~ r2_hidden(esk9_0,esk13_0)
      | ~ r2_hidden(esk10_0,esk14_0) )
    & ( r2_hidden(esk7_0,esk11_0)
      | r2_hidden(k4_mcart_1(esk7_0,esk8_0,esk9_0,esk10_0),k4_zfmisc_1(esk11_0,esk12_0,esk13_0,esk14_0)) )
    & ( r2_hidden(esk8_0,esk12_0)
      | r2_hidden(k4_mcart_1(esk7_0,esk8_0,esk9_0,esk10_0),k4_zfmisc_1(esk11_0,esk12_0,esk13_0,esk14_0)) )
    & ( r2_hidden(esk9_0,esk13_0)
      | r2_hidden(k4_mcart_1(esk7_0,esk8_0,esk9_0,esk10_0),k4_zfmisc_1(esk11_0,esk12_0,esk13_0,esk14_0)) )
    & ( r2_hidden(esk10_0,esk14_0)
      | r2_hidden(k4_mcart_1(esk7_0,esk8_0,esk9_0,esk10_0),k4_zfmisc_1(esk11_0,esk12_0,esk13_0,esk14_0)) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])])).

cnf(c_0_20,plain,
    ( k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k3_mcart_1(X1,X2,X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_24,plain,(
    ! [X47,X48,X49] :
      ( ( r2_hidden(k1_mcart_1(X47),X48)
        | ~ r2_hidden(X47,k2_zfmisc_1(X48,X49)) )
      & ( r2_hidden(k2_mcart_1(X47),X49)
        | ~ r2_hidden(X47,k2_zfmisc_1(X48,X49)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).

cnf(c_0_25,plain,
    ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,k1_tarski(X2)))
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk8_0,esk12_0)
    | r2_hidden(k4_mcart_1(esk7_0,esk8_0,esk9_0,esk10_0),k4_zfmisc_1(esk11_0,esk12_0,esk13_0,esk14_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_28,plain,
    ( k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4) ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_29,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_30,plain,
    ( r2_hidden(k1_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2))) ),
    inference(spm,[status(thm)],[c_0_25,c_0_18])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk8_0,esk12_0)
    | r2_hidden(k4_tarski(k4_tarski(k4_tarski(esk7_0,esk8_0),esk9_0),esk10_0),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk11_0,esk12_0),esk13_0),esk14_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_27]),c_0_28])).

cnf(c_0_33,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k1_tarski(X2)) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_34,plain,
    ( r2_hidden(k1_mcart_1(k4_tarski(X1,X2)),k1_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk7_0,esk11_0)
    | r2_hidden(k4_mcart_1(esk7_0,esk8_0,esk9_0,esk10_0),k4_zfmisc_1(esk11_0,esk12_0,esk13_0,esk14_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk9_0,esk13_0)
    | r2_hidden(k4_mcart_1(esk7_0,esk8_0,esk9_0,esk10_0),k4_zfmisc_1(esk11_0,esk12_0,esk13_0,esk14_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(k1_mcart_1(k4_tarski(k4_tarski(k4_tarski(esk7_0,esk8_0),esk9_0),esk10_0)),k2_zfmisc_1(k2_zfmisc_1(esk11_0,esk12_0),esk13_0))
    | r2_hidden(esk8_0,esk12_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_32])).

cnf(c_0_38,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X1 ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_39,plain,
    ( r2_hidden(k2_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk7_0,esk11_0)
    | r2_hidden(k4_tarski(k4_tarski(k4_tarski(esk7_0,esk8_0),esk9_0),esk10_0),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk11_0,esk12_0),esk13_0),esk14_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_27]),c_0_28])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk10_0,esk14_0)
    | r2_hidden(k4_mcart_1(esk7_0,esk8_0,esk9_0,esk10_0),k4_zfmisc_1(esk11_0,esk12_0,esk13_0,esk14_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk9_0,esk13_0)
    | r2_hidden(k4_tarski(k4_tarski(k4_tarski(esk7_0,esk8_0),esk9_0),esk10_0),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk11_0,esk12_0),esk13_0),esk14_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_27]),c_0_28])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(k4_tarski(k4_tarski(esk7_0,esk8_0),esk9_0),k2_zfmisc_1(k2_zfmisc_1(esk11_0,esk12_0),esk13_0))
    | r2_hidden(esk8_0,esk12_0) ),
    inference(rw,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_44,plain,
    ( r2_hidden(k2_mcart_1(k4_tarski(X1,X2)),k1_tarski(X2)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_31])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(k1_mcart_1(k4_tarski(k4_tarski(k4_tarski(esk7_0,esk8_0),esk9_0),esk10_0)),k2_zfmisc_1(k2_zfmisc_1(esk11_0,esk12_0),esk13_0))
    | r2_hidden(esk7_0,esk11_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_40])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk10_0,esk14_0)
    | r2_hidden(k4_tarski(k4_tarski(k4_tarski(esk7_0,esk8_0),esk9_0),esk10_0),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk11_0,esk12_0),esk13_0),esk14_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_27]),c_0_28])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(k1_mcart_1(k4_tarski(k4_tarski(k4_tarski(esk7_0,esk8_0),esk9_0),esk10_0)),k2_zfmisc_1(k2_zfmisc_1(esk11_0,esk12_0),esk13_0))
    | r2_hidden(esk9_0,esk13_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_42])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(esk11_0,esk12_0))
    | r2_hidden(esk8_0,esk12_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_43]),c_0_38])).

cnf(c_0_49,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(spm,[status(thm)],[c_0_33,c_0_44])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(k4_tarski(k4_tarski(esk7_0,esk8_0),esk9_0),k2_zfmisc_1(k2_zfmisc_1(esk11_0,esk12_0),esk13_0))
    | r2_hidden(esk7_0,esk11_0) ),
    inference(rw,[status(thm)],[c_0_45,c_0_38])).

cnf(c_0_51,negated_conjecture,
    ( ~ r2_hidden(k4_mcart_1(esk7_0,esk8_0,esk9_0,esk10_0),k4_zfmisc_1(esk11_0,esk12_0,esk13_0,esk14_0))
    | ~ r2_hidden(esk7_0,esk11_0)
    | ~ r2_hidden(esk8_0,esk12_0)
    | ~ r2_hidden(esk9_0,esk13_0)
    | ~ r2_hidden(esk10_0,esk14_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(k2_mcart_1(k4_tarski(k4_tarski(k4_tarski(esk7_0,esk8_0),esk9_0),esk10_0)),esk14_0)
    | r2_hidden(esk10_0,esk14_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_46])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(k4_tarski(k4_tarski(esk7_0,esk8_0),esk9_0),k2_zfmisc_1(k2_zfmisc_1(esk11_0,esk12_0),esk13_0))
    | r2_hidden(esk9_0,esk13_0) ),
    inference(rw,[status(thm)],[c_0_47,c_0_38])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk8_0,esk12_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_48]),c_0_49])])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(esk11_0,esk12_0))
    | r2_hidden(esk7_0,esk11_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_50]),c_0_38])).

cnf(c_0_56,negated_conjecture,
    ( ~ r2_hidden(esk7_0,esk11_0)
    | ~ r2_hidden(esk8_0,esk12_0)
    | ~ r2_hidden(esk9_0,esk13_0)
    | ~ r2_hidden(esk10_0,esk14_0)
    | ~ r2_hidden(k4_tarski(k4_tarski(k4_tarski(esk7_0,esk8_0),esk9_0),esk10_0),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk11_0,esk12_0),esk13_0),esk14_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_27]),c_0_28])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(esk10_0,esk14_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_49])])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(esk9_0,esk13_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_53]),c_0_49])])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk8_0),k2_zfmisc_1(X2,esk12_0))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_17,c_0_54])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(esk7_0,esk11_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_55]),c_0_38])])).

cnf(c_0_61,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(k4_tarski(k4_tarski(esk7_0,esk8_0),esk9_0),esk10_0),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk11_0,esk12_0),esk13_0),esk14_0))
    | ~ r2_hidden(esk7_0,esk11_0)
    | ~ r2_hidden(esk8_0,esk12_0)
    | ~ r2_hidden(esk9_0,esk13_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_57])])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk9_0),k2_zfmisc_1(X2,esk13_0))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_17,c_0_58])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(esk11_0,esk12_0)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_64,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(k4_tarski(k4_tarski(esk7_0,esk8_0),esk9_0),esk10_0),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk11_0,esk12_0),esk13_0),esk14_0))
    | ~ r2_hidden(esk9_0,esk13_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_54])]),c_0_60])])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk10_0),k2_zfmisc_1(X2,esk14_0))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_17,c_0_57])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(k4_tarski(k4_tarski(esk7_0,esk8_0),esk9_0),k2_zfmisc_1(k2_zfmisc_1(esk11_0,esk12_0),esk13_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_67,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(k4_tarski(k4_tarski(esk7_0,esk8_0),esk9_0),esk10_0),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk11_0,esk12_0),esk13_0),esk14_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_58])])).

cnf(c_0_68,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:38:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.19/0.46  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_S2mI
% 0.19/0.46  # and selection function SelectCQArNTNpEqFirst.
% 0.19/0.46  #
% 0.19/0.46  # Preprocessing time       : 0.027 s
% 0.19/0.46  # Presaturation interreduction done
% 0.19/0.46  
% 0.19/0.46  # Proof found!
% 0.19/0.46  # SZS status Theorem
% 0.19/0.46  # SZS output start CNFRefutation
% 0.19/0.46  fof(d2_zfmisc_1, axiom, ![X1, X2, X3]:(X3=k2_zfmisc_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5, X6]:((r2_hidden(X5,X1)&r2_hidden(X6,X2))&X4=k4_tarski(X5,X6)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 0.19/0.46  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 0.19/0.46  fof(t84_mcart_1, conjecture, ![X1, X2, X3, X4, X5, X6, X7, X8]:(r2_hidden(k4_mcart_1(X1,X2,X3,X4),k4_zfmisc_1(X5,X6,X7,X8))<=>(((r2_hidden(X1,X5)&r2_hidden(X2,X6))&r2_hidden(X3,X7))&r2_hidden(X4,X8))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_mcart_1)).
% 0.19/0.46  fof(d4_mcart_1, axiom, ![X1, X2, X3, X4]:k4_mcart_1(X1,X2,X3,X4)=k4_tarski(k3_mcart_1(X1,X2,X3),X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_mcart_1)).
% 0.19/0.46  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 0.19/0.46  fof(d4_zfmisc_1, axiom, ![X1, X2, X3, X4]:k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 0.19/0.46  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 0.19/0.46  fof(t10_mcart_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(X2,X3))=>(r2_hidden(k1_mcart_1(X1),X2)&r2_hidden(k2_mcart_1(X1),X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 0.19/0.46  fof(c_0_8, plain, ![X16, X17, X18, X19, X22, X23, X24, X25, X26, X27, X29, X30]:(((((r2_hidden(esk2_4(X16,X17,X18,X19),X16)|~r2_hidden(X19,X18)|X18!=k2_zfmisc_1(X16,X17))&(r2_hidden(esk3_4(X16,X17,X18,X19),X17)|~r2_hidden(X19,X18)|X18!=k2_zfmisc_1(X16,X17)))&(X19=k4_tarski(esk2_4(X16,X17,X18,X19),esk3_4(X16,X17,X18,X19))|~r2_hidden(X19,X18)|X18!=k2_zfmisc_1(X16,X17)))&(~r2_hidden(X23,X16)|~r2_hidden(X24,X17)|X22!=k4_tarski(X23,X24)|r2_hidden(X22,X18)|X18!=k2_zfmisc_1(X16,X17)))&((~r2_hidden(esk4_3(X25,X26,X27),X27)|(~r2_hidden(X29,X25)|~r2_hidden(X30,X26)|esk4_3(X25,X26,X27)!=k4_tarski(X29,X30))|X27=k2_zfmisc_1(X25,X26))&(((r2_hidden(esk5_3(X25,X26,X27),X25)|r2_hidden(esk4_3(X25,X26,X27),X27)|X27=k2_zfmisc_1(X25,X26))&(r2_hidden(esk6_3(X25,X26,X27),X26)|r2_hidden(esk4_3(X25,X26,X27),X27)|X27=k2_zfmisc_1(X25,X26)))&(esk4_3(X25,X26,X27)=k4_tarski(esk5_3(X25,X26,X27),esk6_3(X25,X26,X27))|r2_hidden(esk4_3(X25,X26,X27),X27)|X27=k2_zfmisc_1(X25,X26))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).
% 0.19/0.46  fof(c_0_9, plain, ![X9, X10, X11, X12, X13, X14]:(((~r2_hidden(X11,X10)|X11=X9|X10!=k1_tarski(X9))&(X12!=X9|r2_hidden(X12,X10)|X10!=k1_tarski(X9)))&((~r2_hidden(esk1_2(X13,X14),X14)|esk1_2(X13,X14)!=X13|X14=k1_tarski(X13))&(r2_hidden(esk1_2(X13,X14),X14)|esk1_2(X13,X14)=X13|X14=k1_tarski(X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.19/0.46  cnf(c_0_10, plain, (r2_hidden(X5,X6)|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)|X5!=k4_tarski(X1,X3)|X6!=k2_zfmisc_1(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.46  cnf(c_0_11, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.46  fof(c_0_12, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6, X7, X8]:(r2_hidden(k4_mcart_1(X1,X2,X3,X4),k4_zfmisc_1(X5,X6,X7,X8))<=>(((r2_hidden(X1,X5)&r2_hidden(X2,X6))&r2_hidden(X3,X7))&r2_hidden(X4,X8)))), inference(assume_negation,[status(cth)],[t84_mcart_1])).
% 0.19/0.46  fof(c_0_13, plain, ![X39, X40, X41, X42]:k4_mcart_1(X39,X40,X41,X42)=k4_tarski(k3_mcart_1(X39,X40,X41),X42), inference(variable_rename,[status(thm)],[d4_mcart_1])).
% 0.19/0.46  fof(c_0_14, plain, ![X33, X34, X35]:k3_mcart_1(X33,X34,X35)=k4_tarski(k4_tarski(X33,X34),X35), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 0.19/0.46  fof(c_0_15, plain, ![X43, X44, X45, X46]:k4_zfmisc_1(X43,X44,X45,X46)=k2_zfmisc_1(k3_zfmisc_1(X43,X44,X45),X46), inference(variable_rename,[status(thm)],[d4_zfmisc_1])).
% 0.19/0.46  fof(c_0_16, plain, ![X36, X37, X38]:k3_zfmisc_1(X36,X37,X38)=k2_zfmisc_1(k2_zfmisc_1(X36,X37),X38), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 0.19/0.46  cnf(c_0_17, plain, (r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))|~r2_hidden(X2,X4)|~r2_hidden(X1,X3)), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_10])])).
% 0.19/0.46  cnf(c_0_18, plain, (r2_hidden(X1,k1_tarski(X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_11])])).
% 0.19/0.46  fof(c_0_19, negated_conjecture, ((~r2_hidden(k4_mcart_1(esk7_0,esk8_0,esk9_0,esk10_0),k4_zfmisc_1(esk11_0,esk12_0,esk13_0,esk14_0))|(~r2_hidden(esk7_0,esk11_0)|~r2_hidden(esk8_0,esk12_0)|~r2_hidden(esk9_0,esk13_0)|~r2_hidden(esk10_0,esk14_0)))&((((r2_hidden(esk7_0,esk11_0)|r2_hidden(k4_mcart_1(esk7_0,esk8_0,esk9_0,esk10_0),k4_zfmisc_1(esk11_0,esk12_0,esk13_0,esk14_0)))&(r2_hidden(esk8_0,esk12_0)|r2_hidden(k4_mcart_1(esk7_0,esk8_0,esk9_0,esk10_0),k4_zfmisc_1(esk11_0,esk12_0,esk13_0,esk14_0))))&(r2_hidden(esk9_0,esk13_0)|r2_hidden(k4_mcart_1(esk7_0,esk8_0,esk9_0,esk10_0),k4_zfmisc_1(esk11_0,esk12_0,esk13_0,esk14_0))))&(r2_hidden(esk10_0,esk14_0)|r2_hidden(k4_mcart_1(esk7_0,esk8_0,esk9_0,esk10_0),k4_zfmisc_1(esk11_0,esk12_0,esk13_0,esk14_0))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])])).
% 0.19/0.46  cnf(c_0_20, plain, (k4_mcart_1(X1,X2,X3,X4)=k4_tarski(k3_mcart_1(X1,X2,X3),X4)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.46  cnf(c_0_21, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.46  cnf(c_0_22, plain, (k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.46  cnf(c_0_23, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.46  fof(c_0_24, plain, ![X47, X48, X49]:((r2_hidden(k1_mcart_1(X47),X48)|~r2_hidden(X47,k2_zfmisc_1(X48,X49)))&(r2_hidden(k2_mcart_1(X47),X49)|~r2_hidden(X47,k2_zfmisc_1(X48,X49)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).
% 0.19/0.46  cnf(c_0_25, plain, (r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,k1_tarski(X2)))|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.19/0.46  cnf(c_0_26, negated_conjecture, (r2_hidden(esk8_0,esk12_0)|r2_hidden(k4_mcart_1(esk7_0,esk8_0,esk9_0,esk10_0),k4_zfmisc_1(esk11_0,esk12_0,esk13_0,esk14_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.46  cnf(c_0_27, plain, (k4_mcart_1(X1,X2,X3,X4)=k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4)), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 0.19/0.46  cnf(c_0_28, plain, (k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)), inference(rw,[status(thm)],[c_0_22, c_0_23])).
% 0.19/0.46  cnf(c_0_29, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.46  cnf(c_0_30, plain, (r2_hidden(k1_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.46  cnf(c_0_31, plain, (r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2)))), inference(spm,[status(thm)],[c_0_25, c_0_18])).
% 0.19/0.46  cnf(c_0_32, negated_conjecture, (r2_hidden(esk8_0,esk12_0)|r2_hidden(k4_tarski(k4_tarski(k4_tarski(esk7_0,esk8_0),esk9_0),esk10_0),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk11_0,esk12_0),esk13_0),esk14_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_27]), c_0_28])).
% 0.19/0.46  cnf(c_0_33, plain, (X1=X2|~r2_hidden(X1,k1_tarski(X2))), inference(er,[status(thm)],[c_0_29])).
% 0.19/0.46  cnf(c_0_34, plain, (r2_hidden(k1_mcart_1(k4_tarski(X1,X2)),k1_tarski(X1))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.19/0.46  cnf(c_0_35, negated_conjecture, (r2_hidden(esk7_0,esk11_0)|r2_hidden(k4_mcart_1(esk7_0,esk8_0,esk9_0,esk10_0),k4_zfmisc_1(esk11_0,esk12_0,esk13_0,esk14_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.46  cnf(c_0_36, negated_conjecture, (r2_hidden(esk9_0,esk13_0)|r2_hidden(k4_mcart_1(esk7_0,esk8_0,esk9_0,esk10_0),k4_zfmisc_1(esk11_0,esk12_0,esk13_0,esk14_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.46  cnf(c_0_37, negated_conjecture, (r2_hidden(k1_mcart_1(k4_tarski(k4_tarski(k4_tarski(esk7_0,esk8_0),esk9_0),esk10_0)),k2_zfmisc_1(k2_zfmisc_1(esk11_0,esk12_0),esk13_0))|r2_hidden(esk8_0,esk12_0)), inference(spm,[status(thm)],[c_0_30, c_0_32])).
% 0.19/0.46  cnf(c_0_38, plain, (k1_mcart_1(k4_tarski(X1,X2))=X1), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.19/0.46  cnf(c_0_39, plain, (r2_hidden(k2_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.46  cnf(c_0_40, negated_conjecture, (r2_hidden(esk7_0,esk11_0)|r2_hidden(k4_tarski(k4_tarski(k4_tarski(esk7_0,esk8_0),esk9_0),esk10_0),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk11_0,esk12_0),esk13_0),esk14_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_27]), c_0_28])).
% 0.19/0.46  cnf(c_0_41, negated_conjecture, (r2_hidden(esk10_0,esk14_0)|r2_hidden(k4_mcart_1(esk7_0,esk8_0,esk9_0,esk10_0),k4_zfmisc_1(esk11_0,esk12_0,esk13_0,esk14_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.46  cnf(c_0_42, negated_conjecture, (r2_hidden(esk9_0,esk13_0)|r2_hidden(k4_tarski(k4_tarski(k4_tarski(esk7_0,esk8_0),esk9_0),esk10_0),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk11_0,esk12_0),esk13_0),esk14_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_27]), c_0_28])).
% 0.19/0.46  cnf(c_0_43, negated_conjecture, (r2_hidden(k4_tarski(k4_tarski(esk7_0,esk8_0),esk9_0),k2_zfmisc_1(k2_zfmisc_1(esk11_0,esk12_0),esk13_0))|r2_hidden(esk8_0,esk12_0)), inference(rw,[status(thm)],[c_0_37, c_0_38])).
% 0.19/0.46  cnf(c_0_44, plain, (r2_hidden(k2_mcart_1(k4_tarski(X1,X2)),k1_tarski(X2))), inference(spm,[status(thm)],[c_0_39, c_0_31])).
% 0.19/0.46  cnf(c_0_45, negated_conjecture, (r2_hidden(k1_mcart_1(k4_tarski(k4_tarski(k4_tarski(esk7_0,esk8_0),esk9_0),esk10_0)),k2_zfmisc_1(k2_zfmisc_1(esk11_0,esk12_0),esk13_0))|r2_hidden(esk7_0,esk11_0)), inference(spm,[status(thm)],[c_0_30, c_0_40])).
% 0.19/0.46  cnf(c_0_46, negated_conjecture, (r2_hidden(esk10_0,esk14_0)|r2_hidden(k4_tarski(k4_tarski(k4_tarski(esk7_0,esk8_0),esk9_0),esk10_0),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk11_0,esk12_0),esk13_0),esk14_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_27]), c_0_28])).
% 0.19/0.46  cnf(c_0_47, negated_conjecture, (r2_hidden(k1_mcart_1(k4_tarski(k4_tarski(k4_tarski(esk7_0,esk8_0),esk9_0),esk10_0)),k2_zfmisc_1(k2_zfmisc_1(esk11_0,esk12_0),esk13_0))|r2_hidden(esk9_0,esk13_0)), inference(spm,[status(thm)],[c_0_30, c_0_42])).
% 0.19/0.46  cnf(c_0_48, negated_conjecture, (r2_hidden(k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(esk11_0,esk12_0))|r2_hidden(esk8_0,esk12_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_43]), c_0_38])).
% 0.19/0.46  cnf(c_0_49, plain, (k2_mcart_1(k4_tarski(X1,X2))=X2), inference(spm,[status(thm)],[c_0_33, c_0_44])).
% 0.19/0.46  cnf(c_0_50, negated_conjecture, (r2_hidden(k4_tarski(k4_tarski(esk7_0,esk8_0),esk9_0),k2_zfmisc_1(k2_zfmisc_1(esk11_0,esk12_0),esk13_0))|r2_hidden(esk7_0,esk11_0)), inference(rw,[status(thm)],[c_0_45, c_0_38])).
% 0.19/0.46  cnf(c_0_51, negated_conjecture, (~r2_hidden(k4_mcart_1(esk7_0,esk8_0,esk9_0,esk10_0),k4_zfmisc_1(esk11_0,esk12_0,esk13_0,esk14_0))|~r2_hidden(esk7_0,esk11_0)|~r2_hidden(esk8_0,esk12_0)|~r2_hidden(esk9_0,esk13_0)|~r2_hidden(esk10_0,esk14_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.46  cnf(c_0_52, negated_conjecture, (r2_hidden(k2_mcart_1(k4_tarski(k4_tarski(k4_tarski(esk7_0,esk8_0),esk9_0),esk10_0)),esk14_0)|r2_hidden(esk10_0,esk14_0)), inference(spm,[status(thm)],[c_0_39, c_0_46])).
% 0.19/0.46  cnf(c_0_53, negated_conjecture, (r2_hidden(k4_tarski(k4_tarski(esk7_0,esk8_0),esk9_0),k2_zfmisc_1(k2_zfmisc_1(esk11_0,esk12_0),esk13_0))|r2_hidden(esk9_0,esk13_0)), inference(rw,[status(thm)],[c_0_47, c_0_38])).
% 0.19/0.46  cnf(c_0_54, negated_conjecture, (r2_hidden(esk8_0,esk12_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_48]), c_0_49])])).
% 0.19/0.46  cnf(c_0_55, negated_conjecture, (r2_hidden(k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(esk11_0,esk12_0))|r2_hidden(esk7_0,esk11_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_50]), c_0_38])).
% 0.19/0.46  cnf(c_0_56, negated_conjecture, (~r2_hidden(esk7_0,esk11_0)|~r2_hidden(esk8_0,esk12_0)|~r2_hidden(esk9_0,esk13_0)|~r2_hidden(esk10_0,esk14_0)|~r2_hidden(k4_tarski(k4_tarski(k4_tarski(esk7_0,esk8_0),esk9_0),esk10_0),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk11_0,esk12_0),esk13_0),esk14_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_27]), c_0_28])).
% 0.19/0.46  cnf(c_0_57, negated_conjecture, (r2_hidden(esk10_0,esk14_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_49])])).
% 0.19/0.46  cnf(c_0_58, negated_conjecture, (r2_hidden(esk9_0,esk13_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_53]), c_0_49])])).
% 0.19/0.46  cnf(c_0_59, negated_conjecture, (r2_hidden(k4_tarski(X1,esk8_0),k2_zfmisc_1(X2,esk12_0))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_17, c_0_54])).
% 0.19/0.46  cnf(c_0_60, negated_conjecture, (r2_hidden(esk7_0,esk11_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_55]), c_0_38])])).
% 0.19/0.46  cnf(c_0_61, negated_conjecture, (~r2_hidden(k4_tarski(k4_tarski(k4_tarski(esk7_0,esk8_0),esk9_0),esk10_0),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk11_0,esk12_0),esk13_0),esk14_0))|~r2_hidden(esk7_0,esk11_0)|~r2_hidden(esk8_0,esk12_0)|~r2_hidden(esk9_0,esk13_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_57])])).
% 0.19/0.46  cnf(c_0_62, negated_conjecture, (r2_hidden(k4_tarski(X1,esk9_0),k2_zfmisc_1(X2,esk13_0))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_17, c_0_58])).
% 0.19/0.46  cnf(c_0_63, negated_conjecture, (r2_hidden(k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(esk11_0,esk12_0))), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.19/0.46  cnf(c_0_64, negated_conjecture, (~r2_hidden(k4_tarski(k4_tarski(k4_tarski(esk7_0,esk8_0),esk9_0),esk10_0),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk11_0,esk12_0),esk13_0),esk14_0))|~r2_hidden(esk9_0,esk13_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_54])]), c_0_60])])).
% 0.19/0.46  cnf(c_0_65, negated_conjecture, (r2_hidden(k4_tarski(X1,esk10_0),k2_zfmisc_1(X2,esk14_0))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_17, c_0_57])).
% 0.19/0.46  cnf(c_0_66, negated_conjecture, (r2_hidden(k4_tarski(k4_tarski(esk7_0,esk8_0),esk9_0),k2_zfmisc_1(k2_zfmisc_1(esk11_0,esk12_0),esk13_0))), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.19/0.46  cnf(c_0_67, negated_conjecture, (~r2_hidden(k4_tarski(k4_tarski(k4_tarski(esk7_0,esk8_0),esk9_0),esk10_0),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk11_0,esk12_0),esk13_0),esk14_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_64, c_0_58])])).
% 0.19/0.46  cnf(c_0_68, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_67]), ['proof']).
% 0.19/0.46  # SZS output end CNFRefutation
% 0.19/0.46  # Proof object total steps             : 69
% 0.19/0.46  # Proof object clause steps            : 52
% 0.19/0.46  # Proof object formula steps           : 17
% 0.19/0.46  # Proof object conjectures             : 35
% 0.19/0.46  # Proof object clause conjectures      : 32
% 0.19/0.46  # Proof object formula conjectures     : 3
% 0.19/0.46  # Proof object initial clauses used    : 14
% 0.19/0.46  # Proof object initial formulas used   : 8
% 0.19/0.46  # Proof object generating inferences   : 21
% 0.19/0.46  # Proof object simplifying inferences  : 39
% 0.19/0.46  # Training examples: 0 positive, 0 negative
% 0.19/0.46  # Parsed axioms                        : 8
% 0.19/0.46  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.46  # Initial clauses                      : 23
% 0.19/0.46  # Removed in clause preprocessing      : 4
% 0.19/0.46  # Initial clauses in saturation        : 19
% 0.19/0.46  # Processed clauses                    : 249
% 0.19/0.46  # ...of these trivial                  : 4
% 0.19/0.46  # ...subsumed                          : 0
% 0.19/0.46  # ...remaining for further processing  : 245
% 0.19/0.46  # Other redundant clauses eliminated   : 11
% 0.19/0.46  # Clauses deleted for lack of memory   : 0
% 0.19/0.46  # Backward-subsumed                    : 1
% 0.19/0.46  # Backward-rewritten                   : 24
% 0.19/0.46  # Generated clauses                    : 8114
% 0.19/0.46  # ...of the previous two non-trivial   : 7854
% 0.19/0.46  # Contextual simplify-reflections      : 0
% 0.19/0.46  # Paramodulations                      : 8103
% 0.19/0.46  # Factorizations                       : 2
% 0.19/0.46  # Equation resolutions                 : 11
% 0.19/0.46  # Propositional unsat checks           : 0
% 0.19/0.46  #    Propositional check models        : 0
% 0.19/0.46  #    Propositional check unsatisfiable : 0
% 0.19/0.46  #    Propositional clauses             : 0
% 0.19/0.46  #    Propositional clauses after purity: 0
% 0.19/0.46  #    Propositional unsat core size     : 0
% 0.19/0.46  #    Propositional preprocessing time  : 0.000
% 0.19/0.46  #    Propositional encoding time       : 0.000
% 0.19/0.46  #    Propositional solver time         : 0.000
% 0.19/0.46  #    Success case prop preproc time    : 0.000
% 0.19/0.46  #    Success case prop encoding time   : 0.000
% 0.19/0.46  #    Success case prop solver time     : 0.000
% 0.19/0.46  # Current number of processed clauses  : 195
% 0.19/0.46  #    Positive orientable unit clauses  : 115
% 0.19/0.46  #    Positive unorientable unit clauses: 0
% 0.19/0.46  #    Negative unit clauses             : 1
% 0.19/0.46  #    Non-unit-clauses                  : 79
% 0.19/0.46  # Current number of unprocessed clauses: 7604
% 0.19/0.46  # ...number of literals in the above   : 10865
% 0.19/0.46  # Current number of archived formulas  : 0
% 0.19/0.46  # Current number of archived clauses   : 48
% 0.19/0.46  # Clause-clause subsumption calls (NU) : 597
% 0.19/0.46  # Rec. Clause-clause subsumption calls : 535
% 0.19/0.46  # Non-unit clause-clause subsumptions  : 0
% 0.19/0.46  # Unit Clause-clause subsumption calls : 108
% 0.19/0.46  # Rewrite failures with RHS unbound    : 0
% 0.19/0.46  # BW rewrite match attempts            : 418
% 0.19/0.46  # BW rewrite match successes           : 9
% 0.19/0.46  # Condensation attempts                : 0
% 0.19/0.46  # Condensation successes               : 0
% 0.19/0.46  # Termbank termtop insertions          : 175199
% 0.19/0.46  
% 0.19/0.46  # -------------------------------------------------
% 0.19/0.46  # User time                : 0.114 s
% 0.19/0.46  # System time              : 0.006 s
% 0.19/0.46  # Total time               : 0.120 s
% 0.19/0.46  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
