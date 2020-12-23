%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:32 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 359 expanded)
%              Number of clauses        :   47 ( 182 expanded)
%              Number of leaves         :    9 (  84 expanded)
%              Depth                    :   12
%              Number of atoms          :  194 (1093 expanded)
%              Number of equality atoms :   72 ( 552 expanded)
%              Maximal formula depth    :   23 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t84_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] :
      ( r2_hidden(k4_mcart_1(X1,X2,X3,X4),k4_zfmisc_1(X5,X6,X7,X8))
    <=> ( r2_hidden(X1,X5)
        & r2_hidden(X2,X6)
        & r2_hidden(X3,X7)
        & r2_hidden(X4,X8) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_mcart_1)).

fof(d4_mcart_1,axiom,(
    ! [X1,X2,X3,X4] : k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k3_mcart_1(X1,X2,X3),X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_mcart_1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(d4_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(d1_mcart_1,axiom,(
    ! [X1] :
      ( ? [X2,X3] : X1 = k4_tarski(X2,X3)
     => ! [X2] :
          ( X2 = k1_mcart_1(X1)
        <=> ! [X3,X4] :
              ( X1 = k4_tarski(X3,X4)
             => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_mcart_1)).

fof(d2_mcart_1,axiom,(
    ! [X1] :
      ( ? [X2,X3] : X1 = k4_tarski(X2,X3)
     => ! [X2] :
          ( X2 = k2_mcart_1(X1)
        <=> ! [X3,X4] :
              ( X1 = k4_tarski(X3,X4)
             => X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_mcart_1)).

fof(t10_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
     => ( r2_hidden(k1_mcart_1(X1),X2)
        & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(d2_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_zfmisc_1(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ? [X5,X6] :
              ( r2_hidden(X5,X1)
              & r2_hidden(X6,X2)
              & X4 = k4_tarski(X5,X6) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6,X7,X8] :
        ( r2_hidden(k4_mcart_1(X1,X2,X3,X4),k4_zfmisc_1(X5,X6,X7,X8))
      <=> ( r2_hidden(X1,X5)
          & r2_hidden(X2,X6)
          & r2_hidden(X3,X7)
          & r2_hidden(X4,X8) ) ) ),
    inference(assume_negation,[status(cth)],[t84_mcart_1])).

fof(c_0_10,plain,(
    ! [X50,X51,X52,X53] : k4_mcart_1(X50,X51,X52,X53) = k4_tarski(k3_mcart_1(X50,X51,X52),X53) ),
    inference(variable_rename,[status(thm)],[d4_mcart_1])).

fof(c_0_11,plain,(
    ! [X44,X45,X46] : k3_mcart_1(X44,X45,X46) = k4_tarski(k4_tarski(X44,X45),X46) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

fof(c_0_12,plain,(
    ! [X54,X55,X56,X57] : k4_zfmisc_1(X54,X55,X56,X57) = k2_zfmisc_1(k3_zfmisc_1(X54,X55,X56),X57) ),
    inference(variable_rename,[status(thm)],[d4_zfmisc_1])).

fof(c_0_13,plain,(
    ! [X47,X48,X49] : k3_zfmisc_1(X47,X48,X49) = k2_zfmisc_1(k2_zfmisc_1(X47,X48),X49) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_14,plain,(
    ! [X26,X27,X28,X29,X30,X31,X32] :
      ( ( X29 != k1_mcart_1(X26)
        | X26 != k4_tarski(X30,X31)
        | X29 = X30
        | X26 != k4_tarski(X27,X28) )
      & ( X26 = k4_tarski(esk6_2(X26,X32),esk7_2(X26,X32))
        | X32 = k1_mcart_1(X26)
        | X26 != k4_tarski(X27,X28) )
      & ( X32 != esk6_2(X26,X32)
        | X32 = k1_mcart_1(X26)
        | X26 != k4_tarski(X27,X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_mcart_1])])])])])])).

fof(c_0_15,negated_conjecture,
    ( ( ~ r2_hidden(k4_mcart_1(esk10_0,esk11_0,esk12_0,esk13_0),k4_zfmisc_1(esk14_0,esk15_0,esk16_0,esk17_0))
      | ~ r2_hidden(esk10_0,esk14_0)
      | ~ r2_hidden(esk11_0,esk15_0)
      | ~ r2_hidden(esk12_0,esk16_0)
      | ~ r2_hidden(esk13_0,esk17_0) )
    & ( r2_hidden(esk10_0,esk14_0)
      | r2_hidden(k4_mcart_1(esk10_0,esk11_0,esk12_0,esk13_0),k4_zfmisc_1(esk14_0,esk15_0,esk16_0,esk17_0)) )
    & ( r2_hidden(esk11_0,esk15_0)
      | r2_hidden(k4_mcart_1(esk10_0,esk11_0,esk12_0,esk13_0),k4_zfmisc_1(esk14_0,esk15_0,esk16_0,esk17_0)) )
    & ( r2_hidden(esk12_0,esk16_0)
      | r2_hidden(k4_mcart_1(esk10_0,esk11_0,esk12_0,esk13_0),k4_zfmisc_1(esk14_0,esk15_0,esk16_0,esk17_0)) )
    & ( r2_hidden(esk13_0,esk17_0)
      | r2_hidden(k4_mcart_1(esk10_0,esk11_0,esk12_0,esk13_0),k4_zfmisc_1(esk14_0,esk15_0,esk16_0,esk17_0)) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])])).

cnf(c_0_16,plain,
    ( k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k3_mcart_1(X1,X2,X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( X1 = X3
    | X1 != k1_mcart_1(X2)
    | X2 != k4_tarski(X3,X4)
    | X2 != k4_tarski(X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_21,plain,(
    ! [X35,X36,X37,X38,X39,X40,X41] :
      ( ( X38 != k2_mcart_1(X35)
        | X35 != k4_tarski(X39,X40)
        | X38 = X40
        | X35 != k4_tarski(X36,X37) )
      & ( X35 = k4_tarski(esk8_2(X35,X41),esk9_2(X35,X41))
        | X41 = k2_mcart_1(X35)
        | X35 != k4_tarski(X36,X37) )
      & ( X41 != esk9_2(X35,X41)
        | X41 = k2_mcart_1(X35)
        | X35 != k4_tarski(X36,X37) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_mcart_1])])])])])])).

fof(c_0_22,plain,(
    ! [X58,X59,X60] :
      ( ( r2_hidden(k1_mcart_1(X58),X59)
        | ~ r2_hidden(X58,k2_zfmisc_1(X59,X60)) )
      & ( r2_hidden(k2_mcart_1(X58),X60)
        | ~ r2_hidden(X58,k2_zfmisc_1(X59,X60)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(esk10_0,esk14_0)
    | r2_hidden(k4_mcart_1(esk10_0,esk11_0,esk12_0,esk13_0),k4_zfmisc_1(esk14_0,esk15_0,esk16_0,esk17_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_25,plain,
    ( k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4) ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk11_0,esk15_0)
    | r2_hidden(k4_mcart_1(esk10_0,esk11_0,esk12_0,esk13_0),k4_zfmisc_1(esk14_0,esk15_0,esk16_0,esk17_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_27,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X3
    | k4_tarski(X1,X2) != k4_tarski(X3,X4) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_20])])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk13_0,esk17_0)
    | r2_hidden(k4_mcart_1(esk10_0,esk11_0,esk12_0,esk13_0),k4_zfmisc_1(esk14_0,esk15_0,esk16_0,esk17_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_29,plain,
    ( X1 = X4
    | X1 != k2_mcart_1(X2)
    | X2 != k4_tarski(X3,X4)
    | X2 != k4_tarski(X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( r2_hidden(k1_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk10_0,esk14_0)
    | r2_hidden(k4_tarski(k4_tarski(k4_tarski(esk10_0,esk11_0),esk12_0),esk13_0),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk14_0,esk15_0),esk16_0),esk17_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_24]),c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk11_0,esk15_0)
    | r2_hidden(k4_tarski(k4_tarski(k4_tarski(esk10_0,esk11_0),esk12_0),esk13_0),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk14_0,esk15_0),esk16_0),esk17_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_24]),c_0_25])).

cnf(c_0_33,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X1 ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_34,plain,
    ( r2_hidden(k2_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk13_0,esk17_0)
    | r2_hidden(k4_tarski(k4_tarski(k4_tarski(esk10_0,esk11_0),esk12_0),esk13_0),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk14_0,esk15_0),esk16_0),esk17_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_24]),c_0_25])).

cnf(c_0_36,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X3
    | k4_tarski(X1,X2) != k4_tarski(X4,X3) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_29])])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(k1_mcart_1(k4_tarski(k4_tarski(k4_tarski(esk10_0,esk11_0),esk12_0),esk13_0)),k2_zfmisc_1(k2_zfmisc_1(esk14_0,esk15_0),esk16_0))
    | r2_hidden(esk10_0,esk14_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk12_0,esk16_0)
    | r2_hidden(k4_mcart_1(esk10_0,esk11_0,esk12_0,esk13_0),k4_zfmisc_1(esk14_0,esk15_0,esk16_0,esk17_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_39,plain,(
    ! [X9,X10,X11,X12,X15,X16,X17,X18,X19,X20,X22,X23] :
      ( ( r2_hidden(esk1_4(X9,X10,X11,X12),X9)
        | ~ r2_hidden(X12,X11)
        | X11 != k2_zfmisc_1(X9,X10) )
      & ( r2_hidden(esk2_4(X9,X10,X11,X12),X10)
        | ~ r2_hidden(X12,X11)
        | X11 != k2_zfmisc_1(X9,X10) )
      & ( X12 = k4_tarski(esk1_4(X9,X10,X11,X12),esk2_4(X9,X10,X11,X12))
        | ~ r2_hidden(X12,X11)
        | X11 != k2_zfmisc_1(X9,X10) )
      & ( ~ r2_hidden(X16,X9)
        | ~ r2_hidden(X17,X10)
        | X15 != k4_tarski(X16,X17)
        | r2_hidden(X15,X11)
        | X11 != k2_zfmisc_1(X9,X10) )
      & ( ~ r2_hidden(esk3_3(X18,X19,X20),X20)
        | ~ r2_hidden(X22,X18)
        | ~ r2_hidden(X23,X19)
        | esk3_3(X18,X19,X20) != k4_tarski(X22,X23)
        | X20 = k2_zfmisc_1(X18,X19) )
      & ( r2_hidden(esk4_3(X18,X19,X20),X18)
        | r2_hidden(esk3_3(X18,X19,X20),X20)
        | X20 = k2_zfmisc_1(X18,X19) )
      & ( r2_hidden(esk5_3(X18,X19,X20),X19)
        | r2_hidden(esk3_3(X18,X19,X20),X20)
        | X20 = k2_zfmisc_1(X18,X19) )
      & ( esk3_3(X18,X19,X20) = k4_tarski(esk4_3(X18,X19,X20),esk5_3(X18,X19,X20))
        | r2_hidden(esk3_3(X18,X19,X20),X20)
        | X20 = k2_zfmisc_1(X18,X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(k4_tarski(k4_tarski(esk10_0,esk11_0),esk12_0),k2_zfmisc_1(k2_zfmisc_1(esk14_0,esk15_0),esk16_0))
    | r2_hidden(esk11_0,esk15_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_32]),c_0_33])).

cnf(c_0_41,negated_conjecture,
    ( ~ r2_hidden(k4_mcart_1(esk10_0,esk11_0,esk12_0,esk13_0),k4_zfmisc_1(esk14_0,esk15_0,esk16_0,esk17_0))
    | ~ r2_hidden(esk10_0,esk14_0)
    | ~ r2_hidden(esk11_0,esk15_0)
    | ~ r2_hidden(esk12_0,esk16_0)
    | ~ r2_hidden(esk13_0,esk17_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(k2_mcart_1(k4_tarski(k4_tarski(k4_tarski(esk10_0,esk11_0),esk12_0),esk13_0)),esk17_0)
    | r2_hidden(esk13_0,esk17_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_43,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(er,[status(thm)],[c_0_36])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(k4_tarski(k4_tarski(esk10_0,esk11_0),esk12_0),k2_zfmisc_1(k2_zfmisc_1(esk14_0,esk15_0),esk16_0))
    | r2_hidden(esk10_0,esk14_0) ),
    inference(rw,[status(thm)],[c_0_37,c_0_33])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk12_0,esk16_0)
    | r2_hidden(k4_tarski(k4_tarski(k4_tarski(esk10_0,esk11_0),esk12_0),esk13_0),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk14_0,esk15_0),esk16_0),esk17_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_24]),c_0_25])).

cnf(c_0_46,plain,
    ( r2_hidden(X5,X6)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4)
    | X5 != k4_tarski(X1,X3)
    | X6 != k2_zfmisc_1(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(k4_tarski(esk10_0,esk11_0),k2_zfmisc_1(esk14_0,esk15_0))
    | r2_hidden(esk11_0,esk15_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_40]),c_0_33])).

cnf(c_0_48,negated_conjecture,
    ( ~ r2_hidden(esk10_0,esk14_0)
    | ~ r2_hidden(esk11_0,esk15_0)
    | ~ r2_hidden(esk12_0,esk16_0)
    | ~ r2_hidden(esk13_0,esk17_0)
    | ~ r2_hidden(k4_tarski(k4_tarski(k4_tarski(esk10_0,esk11_0),esk12_0),esk13_0),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk14_0,esk15_0),esk16_0),esk17_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_24]),c_0_25])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk13_0,esk17_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_43])])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(k4_tarski(esk10_0,esk11_0),k2_zfmisc_1(esk14_0,esk15_0))
    | r2_hidden(esk10_0,esk14_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_44]),c_0_33])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(k4_tarski(k4_tarski(esk10_0,esk11_0),esk12_0),k2_zfmisc_1(k2_zfmisc_1(esk14_0,esk15_0),esk16_0))
    | r2_hidden(esk12_0,esk16_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_45]),c_0_33])).

cnf(c_0_52,plain,
    ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    | ~ r2_hidden(X2,X4)
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_46])])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(esk11_0,esk15_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_47]),c_0_43])])).

cnf(c_0_54,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(k4_tarski(k4_tarski(esk10_0,esk11_0),esk12_0),esk13_0),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk14_0,esk15_0),esk16_0),esk17_0))
    | ~ r2_hidden(esk10_0,esk14_0)
    | ~ r2_hidden(esk11_0,esk15_0)
    | ~ r2_hidden(esk12_0,esk16_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_49])])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(esk10_0,esk14_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_50]),c_0_33])])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk12_0,esk16_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_51]),c_0_43])])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk11_0),k2_zfmisc_1(X2,esk15_0))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_58,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(k4_tarski(k4_tarski(esk10_0,esk11_0),esk12_0),esk13_0),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk14_0,esk15_0),esk16_0),esk17_0))
    | ~ r2_hidden(esk11_0,esk15_0)
    | ~ r2_hidden(esk12_0,esk16_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_55])])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk12_0),k2_zfmisc_1(X2,esk16_0))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_52,c_0_56])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(k4_tarski(esk10_0,esk11_0),k2_zfmisc_1(esk14_0,esk15_0)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_55])).

cnf(c_0_61,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(k4_tarski(k4_tarski(esk10_0,esk11_0),esk12_0),esk13_0),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk14_0,esk15_0),esk16_0),esk17_0))
    | ~ r2_hidden(esk12_0,esk16_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_53])])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk13_0),k2_zfmisc_1(X2,esk17_0))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_52,c_0_49])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(k4_tarski(k4_tarski(esk10_0,esk11_0),esk12_0),k2_zfmisc_1(k2_zfmisc_1(esk14_0,esk15_0),esk16_0)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_64,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(k4_tarski(k4_tarski(esk10_0,esk11_0),esk12_0),esk13_0),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk14_0,esk15_0),esk16_0),esk17_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_56])])).

cnf(c_0_65,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:48:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_S2mI
% 0.13/0.40  # and selection function SelectCQArNTNpEqFirst.
% 0.13/0.40  #
% 0.13/0.40  # Preprocessing time       : 0.028 s
% 0.13/0.40  # Presaturation interreduction done
% 0.13/0.40  
% 0.13/0.40  # Proof found!
% 0.13/0.40  # SZS status Theorem
% 0.13/0.40  # SZS output start CNFRefutation
% 0.13/0.40  fof(t84_mcart_1, conjecture, ![X1, X2, X3, X4, X5, X6, X7, X8]:(r2_hidden(k4_mcart_1(X1,X2,X3,X4),k4_zfmisc_1(X5,X6,X7,X8))<=>(((r2_hidden(X1,X5)&r2_hidden(X2,X6))&r2_hidden(X3,X7))&r2_hidden(X4,X8))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_mcart_1)).
% 0.13/0.40  fof(d4_mcart_1, axiom, ![X1, X2, X3, X4]:k4_mcart_1(X1,X2,X3,X4)=k4_tarski(k3_mcart_1(X1,X2,X3),X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_mcart_1)).
% 0.13/0.40  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 0.13/0.40  fof(d4_zfmisc_1, axiom, ![X1, X2, X3, X4]:k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 0.13/0.40  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 0.13/0.40  fof(d1_mcart_1, axiom, ![X1]:(?[X2, X3]:X1=k4_tarski(X2,X3)=>![X2]:(X2=k1_mcart_1(X1)<=>![X3, X4]:(X1=k4_tarski(X3,X4)=>X2=X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_mcart_1)).
% 0.13/0.40  fof(d2_mcart_1, axiom, ![X1]:(?[X2, X3]:X1=k4_tarski(X2,X3)=>![X2]:(X2=k2_mcart_1(X1)<=>![X3, X4]:(X1=k4_tarski(X3,X4)=>X2=X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_mcart_1)).
% 0.13/0.40  fof(t10_mcart_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(X2,X3))=>(r2_hidden(k1_mcart_1(X1),X2)&r2_hidden(k2_mcart_1(X1),X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 0.13/0.40  fof(d2_zfmisc_1, axiom, ![X1, X2, X3]:(X3=k2_zfmisc_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5, X6]:((r2_hidden(X5,X1)&r2_hidden(X6,X2))&X4=k4_tarski(X5,X6)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 0.13/0.40  fof(c_0_9, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6, X7, X8]:(r2_hidden(k4_mcart_1(X1,X2,X3,X4),k4_zfmisc_1(X5,X6,X7,X8))<=>(((r2_hidden(X1,X5)&r2_hidden(X2,X6))&r2_hidden(X3,X7))&r2_hidden(X4,X8)))), inference(assume_negation,[status(cth)],[t84_mcart_1])).
% 0.13/0.40  fof(c_0_10, plain, ![X50, X51, X52, X53]:k4_mcart_1(X50,X51,X52,X53)=k4_tarski(k3_mcart_1(X50,X51,X52),X53), inference(variable_rename,[status(thm)],[d4_mcart_1])).
% 0.13/0.40  fof(c_0_11, plain, ![X44, X45, X46]:k3_mcart_1(X44,X45,X46)=k4_tarski(k4_tarski(X44,X45),X46), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 0.13/0.40  fof(c_0_12, plain, ![X54, X55, X56, X57]:k4_zfmisc_1(X54,X55,X56,X57)=k2_zfmisc_1(k3_zfmisc_1(X54,X55,X56),X57), inference(variable_rename,[status(thm)],[d4_zfmisc_1])).
% 0.13/0.40  fof(c_0_13, plain, ![X47, X48, X49]:k3_zfmisc_1(X47,X48,X49)=k2_zfmisc_1(k2_zfmisc_1(X47,X48),X49), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 0.13/0.40  fof(c_0_14, plain, ![X26, X27, X28, X29, X30, X31, X32]:((X29!=k1_mcart_1(X26)|(X26!=k4_tarski(X30,X31)|X29=X30)|X26!=k4_tarski(X27,X28))&((X26=k4_tarski(esk6_2(X26,X32),esk7_2(X26,X32))|X32=k1_mcart_1(X26)|X26!=k4_tarski(X27,X28))&(X32!=esk6_2(X26,X32)|X32=k1_mcart_1(X26)|X26!=k4_tarski(X27,X28)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_mcart_1])])])])])])).
% 0.13/0.40  fof(c_0_15, negated_conjecture, ((~r2_hidden(k4_mcart_1(esk10_0,esk11_0,esk12_0,esk13_0),k4_zfmisc_1(esk14_0,esk15_0,esk16_0,esk17_0))|(~r2_hidden(esk10_0,esk14_0)|~r2_hidden(esk11_0,esk15_0)|~r2_hidden(esk12_0,esk16_0)|~r2_hidden(esk13_0,esk17_0)))&((((r2_hidden(esk10_0,esk14_0)|r2_hidden(k4_mcart_1(esk10_0,esk11_0,esk12_0,esk13_0),k4_zfmisc_1(esk14_0,esk15_0,esk16_0,esk17_0)))&(r2_hidden(esk11_0,esk15_0)|r2_hidden(k4_mcart_1(esk10_0,esk11_0,esk12_0,esk13_0),k4_zfmisc_1(esk14_0,esk15_0,esk16_0,esk17_0))))&(r2_hidden(esk12_0,esk16_0)|r2_hidden(k4_mcart_1(esk10_0,esk11_0,esk12_0,esk13_0),k4_zfmisc_1(esk14_0,esk15_0,esk16_0,esk17_0))))&(r2_hidden(esk13_0,esk17_0)|r2_hidden(k4_mcart_1(esk10_0,esk11_0,esk12_0,esk13_0),k4_zfmisc_1(esk14_0,esk15_0,esk16_0,esk17_0))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])])).
% 0.13/0.40  cnf(c_0_16, plain, (k4_mcart_1(X1,X2,X3,X4)=k4_tarski(k3_mcart_1(X1,X2,X3),X4)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.40  cnf(c_0_17, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.40  cnf(c_0_18, plain, (k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.40  cnf(c_0_19, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.40  cnf(c_0_20, plain, (X1=X3|X1!=k1_mcart_1(X2)|X2!=k4_tarski(X3,X4)|X2!=k4_tarski(X5,X6)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.40  fof(c_0_21, plain, ![X35, X36, X37, X38, X39, X40, X41]:((X38!=k2_mcart_1(X35)|(X35!=k4_tarski(X39,X40)|X38=X40)|X35!=k4_tarski(X36,X37))&((X35=k4_tarski(esk8_2(X35,X41),esk9_2(X35,X41))|X41=k2_mcart_1(X35)|X35!=k4_tarski(X36,X37))&(X41!=esk9_2(X35,X41)|X41=k2_mcart_1(X35)|X35!=k4_tarski(X36,X37)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_mcart_1])])])])])])).
% 0.13/0.40  fof(c_0_22, plain, ![X58, X59, X60]:((r2_hidden(k1_mcart_1(X58),X59)|~r2_hidden(X58,k2_zfmisc_1(X59,X60)))&(r2_hidden(k2_mcart_1(X58),X60)|~r2_hidden(X58,k2_zfmisc_1(X59,X60)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).
% 0.13/0.40  cnf(c_0_23, negated_conjecture, (r2_hidden(esk10_0,esk14_0)|r2_hidden(k4_mcart_1(esk10_0,esk11_0,esk12_0,esk13_0),k4_zfmisc_1(esk14_0,esk15_0,esk16_0,esk17_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.40  cnf(c_0_24, plain, (k4_mcart_1(X1,X2,X3,X4)=k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4)), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 0.13/0.40  cnf(c_0_25, plain, (k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)), inference(rw,[status(thm)],[c_0_18, c_0_19])).
% 0.13/0.40  cnf(c_0_26, negated_conjecture, (r2_hidden(esk11_0,esk15_0)|r2_hidden(k4_mcart_1(esk10_0,esk11_0,esk12_0,esk13_0),k4_zfmisc_1(esk14_0,esk15_0,esk16_0,esk17_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.40  cnf(c_0_27, plain, (k1_mcart_1(k4_tarski(X1,X2))=X3|k4_tarski(X1,X2)!=k4_tarski(X3,X4)), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_20])])).
% 0.13/0.40  cnf(c_0_28, negated_conjecture, (r2_hidden(esk13_0,esk17_0)|r2_hidden(k4_mcart_1(esk10_0,esk11_0,esk12_0,esk13_0),k4_zfmisc_1(esk14_0,esk15_0,esk16_0,esk17_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.40  cnf(c_0_29, plain, (X1=X4|X1!=k2_mcart_1(X2)|X2!=k4_tarski(X3,X4)|X2!=k4_tarski(X5,X6)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.40  cnf(c_0_30, plain, (r2_hidden(k1_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.40  cnf(c_0_31, negated_conjecture, (r2_hidden(esk10_0,esk14_0)|r2_hidden(k4_tarski(k4_tarski(k4_tarski(esk10_0,esk11_0),esk12_0),esk13_0),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk14_0,esk15_0),esk16_0),esk17_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_24]), c_0_25])).
% 0.13/0.40  cnf(c_0_32, negated_conjecture, (r2_hidden(esk11_0,esk15_0)|r2_hidden(k4_tarski(k4_tarski(k4_tarski(esk10_0,esk11_0),esk12_0),esk13_0),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk14_0,esk15_0),esk16_0),esk17_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_24]), c_0_25])).
% 0.13/0.40  cnf(c_0_33, plain, (k1_mcart_1(k4_tarski(X1,X2))=X1), inference(er,[status(thm)],[c_0_27])).
% 0.13/0.40  cnf(c_0_34, plain, (r2_hidden(k2_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.40  cnf(c_0_35, negated_conjecture, (r2_hidden(esk13_0,esk17_0)|r2_hidden(k4_tarski(k4_tarski(k4_tarski(esk10_0,esk11_0),esk12_0),esk13_0),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk14_0,esk15_0),esk16_0),esk17_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_24]), c_0_25])).
% 0.13/0.40  cnf(c_0_36, plain, (k2_mcart_1(k4_tarski(X1,X2))=X3|k4_tarski(X1,X2)!=k4_tarski(X4,X3)), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_29])])).
% 0.13/0.40  cnf(c_0_37, negated_conjecture, (r2_hidden(k1_mcart_1(k4_tarski(k4_tarski(k4_tarski(esk10_0,esk11_0),esk12_0),esk13_0)),k2_zfmisc_1(k2_zfmisc_1(esk14_0,esk15_0),esk16_0))|r2_hidden(esk10_0,esk14_0)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.13/0.40  cnf(c_0_38, negated_conjecture, (r2_hidden(esk12_0,esk16_0)|r2_hidden(k4_mcart_1(esk10_0,esk11_0,esk12_0,esk13_0),k4_zfmisc_1(esk14_0,esk15_0,esk16_0,esk17_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.40  fof(c_0_39, plain, ![X9, X10, X11, X12, X15, X16, X17, X18, X19, X20, X22, X23]:(((((r2_hidden(esk1_4(X9,X10,X11,X12),X9)|~r2_hidden(X12,X11)|X11!=k2_zfmisc_1(X9,X10))&(r2_hidden(esk2_4(X9,X10,X11,X12),X10)|~r2_hidden(X12,X11)|X11!=k2_zfmisc_1(X9,X10)))&(X12=k4_tarski(esk1_4(X9,X10,X11,X12),esk2_4(X9,X10,X11,X12))|~r2_hidden(X12,X11)|X11!=k2_zfmisc_1(X9,X10)))&(~r2_hidden(X16,X9)|~r2_hidden(X17,X10)|X15!=k4_tarski(X16,X17)|r2_hidden(X15,X11)|X11!=k2_zfmisc_1(X9,X10)))&((~r2_hidden(esk3_3(X18,X19,X20),X20)|(~r2_hidden(X22,X18)|~r2_hidden(X23,X19)|esk3_3(X18,X19,X20)!=k4_tarski(X22,X23))|X20=k2_zfmisc_1(X18,X19))&(((r2_hidden(esk4_3(X18,X19,X20),X18)|r2_hidden(esk3_3(X18,X19,X20),X20)|X20=k2_zfmisc_1(X18,X19))&(r2_hidden(esk5_3(X18,X19,X20),X19)|r2_hidden(esk3_3(X18,X19,X20),X20)|X20=k2_zfmisc_1(X18,X19)))&(esk3_3(X18,X19,X20)=k4_tarski(esk4_3(X18,X19,X20),esk5_3(X18,X19,X20))|r2_hidden(esk3_3(X18,X19,X20),X20)|X20=k2_zfmisc_1(X18,X19))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).
% 0.13/0.40  cnf(c_0_40, negated_conjecture, (r2_hidden(k4_tarski(k4_tarski(esk10_0,esk11_0),esk12_0),k2_zfmisc_1(k2_zfmisc_1(esk14_0,esk15_0),esk16_0))|r2_hidden(esk11_0,esk15_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_32]), c_0_33])).
% 0.13/0.40  cnf(c_0_41, negated_conjecture, (~r2_hidden(k4_mcart_1(esk10_0,esk11_0,esk12_0,esk13_0),k4_zfmisc_1(esk14_0,esk15_0,esk16_0,esk17_0))|~r2_hidden(esk10_0,esk14_0)|~r2_hidden(esk11_0,esk15_0)|~r2_hidden(esk12_0,esk16_0)|~r2_hidden(esk13_0,esk17_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.40  cnf(c_0_42, negated_conjecture, (r2_hidden(k2_mcart_1(k4_tarski(k4_tarski(k4_tarski(esk10_0,esk11_0),esk12_0),esk13_0)),esk17_0)|r2_hidden(esk13_0,esk17_0)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.13/0.40  cnf(c_0_43, plain, (k2_mcart_1(k4_tarski(X1,X2))=X2), inference(er,[status(thm)],[c_0_36])).
% 0.13/0.40  cnf(c_0_44, negated_conjecture, (r2_hidden(k4_tarski(k4_tarski(esk10_0,esk11_0),esk12_0),k2_zfmisc_1(k2_zfmisc_1(esk14_0,esk15_0),esk16_0))|r2_hidden(esk10_0,esk14_0)), inference(rw,[status(thm)],[c_0_37, c_0_33])).
% 0.13/0.40  cnf(c_0_45, negated_conjecture, (r2_hidden(esk12_0,esk16_0)|r2_hidden(k4_tarski(k4_tarski(k4_tarski(esk10_0,esk11_0),esk12_0),esk13_0),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk14_0,esk15_0),esk16_0),esk17_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_24]), c_0_25])).
% 0.13/0.40  cnf(c_0_46, plain, (r2_hidden(X5,X6)|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)|X5!=k4_tarski(X1,X3)|X6!=k2_zfmisc_1(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.13/0.40  cnf(c_0_47, negated_conjecture, (r2_hidden(k4_tarski(esk10_0,esk11_0),k2_zfmisc_1(esk14_0,esk15_0))|r2_hidden(esk11_0,esk15_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_40]), c_0_33])).
% 0.13/0.40  cnf(c_0_48, negated_conjecture, (~r2_hidden(esk10_0,esk14_0)|~r2_hidden(esk11_0,esk15_0)|~r2_hidden(esk12_0,esk16_0)|~r2_hidden(esk13_0,esk17_0)|~r2_hidden(k4_tarski(k4_tarski(k4_tarski(esk10_0,esk11_0),esk12_0),esk13_0),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk14_0,esk15_0),esk16_0),esk17_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_24]), c_0_25])).
% 0.13/0.40  cnf(c_0_49, negated_conjecture, (r2_hidden(esk13_0,esk17_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_43])])).
% 0.13/0.40  cnf(c_0_50, negated_conjecture, (r2_hidden(k4_tarski(esk10_0,esk11_0),k2_zfmisc_1(esk14_0,esk15_0))|r2_hidden(esk10_0,esk14_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_44]), c_0_33])).
% 0.13/0.40  cnf(c_0_51, negated_conjecture, (r2_hidden(k4_tarski(k4_tarski(esk10_0,esk11_0),esk12_0),k2_zfmisc_1(k2_zfmisc_1(esk14_0,esk15_0),esk16_0))|r2_hidden(esk12_0,esk16_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_45]), c_0_33])).
% 0.13/0.40  cnf(c_0_52, plain, (r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))|~r2_hidden(X2,X4)|~r2_hidden(X1,X3)), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_46])])).
% 0.13/0.40  cnf(c_0_53, negated_conjecture, (r2_hidden(esk11_0,esk15_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_47]), c_0_43])])).
% 0.13/0.40  cnf(c_0_54, negated_conjecture, (~r2_hidden(k4_tarski(k4_tarski(k4_tarski(esk10_0,esk11_0),esk12_0),esk13_0),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk14_0,esk15_0),esk16_0),esk17_0))|~r2_hidden(esk10_0,esk14_0)|~r2_hidden(esk11_0,esk15_0)|~r2_hidden(esk12_0,esk16_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_49])])).
% 0.13/0.40  cnf(c_0_55, negated_conjecture, (r2_hidden(esk10_0,esk14_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_50]), c_0_33])])).
% 0.13/0.40  cnf(c_0_56, negated_conjecture, (r2_hidden(esk12_0,esk16_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_51]), c_0_43])])).
% 0.13/0.40  cnf(c_0_57, negated_conjecture, (r2_hidden(k4_tarski(X1,esk11_0),k2_zfmisc_1(X2,esk15_0))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.13/0.40  cnf(c_0_58, negated_conjecture, (~r2_hidden(k4_tarski(k4_tarski(k4_tarski(esk10_0,esk11_0),esk12_0),esk13_0),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk14_0,esk15_0),esk16_0),esk17_0))|~r2_hidden(esk11_0,esk15_0)|~r2_hidden(esk12_0,esk16_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_55])])).
% 0.13/0.40  cnf(c_0_59, negated_conjecture, (r2_hidden(k4_tarski(X1,esk12_0),k2_zfmisc_1(X2,esk16_0))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_52, c_0_56])).
% 0.13/0.40  cnf(c_0_60, negated_conjecture, (r2_hidden(k4_tarski(esk10_0,esk11_0),k2_zfmisc_1(esk14_0,esk15_0))), inference(spm,[status(thm)],[c_0_57, c_0_55])).
% 0.13/0.40  cnf(c_0_61, negated_conjecture, (~r2_hidden(k4_tarski(k4_tarski(k4_tarski(esk10_0,esk11_0),esk12_0),esk13_0),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk14_0,esk15_0),esk16_0),esk17_0))|~r2_hidden(esk12_0,esk16_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_53])])).
% 0.13/0.40  cnf(c_0_62, negated_conjecture, (r2_hidden(k4_tarski(X1,esk13_0),k2_zfmisc_1(X2,esk17_0))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_52, c_0_49])).
% 0.13/0.40  cnf(c_0_63, negated_conjecture, (r2_hidden(k4_tarski(k4_tarski(esk10_0,esk11_0),esk12_0),k2_zfmisc_1(k2_zfmisc_1(esk14_0,esk15_0),esk16_0))), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.13/0.40  cnf(c_0_64, negated_conjecture, (~r2_hidden(k4_tarski(k4_tarski(k4_tarski(esk10_0,esk11_0),esk12_0),esk13_0),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk14_0,esk15_0),esk16_0),esk17_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_56])])).
% 0.13/0.40  cnf(c_0_65, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_64]), ['proof']).
% 0.13/0.40  # SZS output end CNFRefutation
% 0.13/0.40  # Proof object total steps             : 66
% 0.13/0.40  # Proof object clause steps            : 47
% 0.13/0.40  # Proof object formula steps           : 19
% 0.13/0.40  # Proof object conjectures             : 34
% 0.13/0.40  # Proof object clause conjectures      : 31
% 0.13/0.40  # Proof object formula conjectures     : 3
% 0.13/0.40  # Proof object initial clauses used    : 14
% 0.13/0.40  # Proof object initial formulas used   : 9
% 0.13/0.40  # Proof object generating inferences   : 17
% 0.13/0.40  # Proof object simplifying inferences  : 40
% 0.13/0.40  # Training examples: 0 positive, 0 negative
% 0.13/0.40  # Parsed axioms                        : 9
% 0.13/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.40  # Initial clauses                      : 25
% 0.13/0.40  # Removed in clause preprocessing      : 4
% 0.13/0.40  # Initial clauses in saturation        : 21
% 0.13/0.40  # Processed clauses                    : 191
% 0.13/0.40  # ...of these trivial                  : 3
% 0.13/0.40  # ...subsumed                          : 8
% 0.13/0.40  # ...remaining for further processing  : 180
% 0.13/0.40  # Other redundant clauses eliminated   : 13
% 0.13/0.40  # Clauses deleted for lack of memory   : 0
% 0.13/0.40  # Backward-subsumed                    : 0
% 0.13/0.40  # Backward-rewritten                   : 25
% 0.13/0.40  # Generated clauses                    : 2191
% 0.13/0.40  # ...of the previous two non-trivial   : 2045
% 0.13/0.40  # Contextual simplify-reflections      : 0
% 0.13/0.40  # Paramodulations                      : 2173
% 0.13/0.40  # Factorizations                       : 0
% 0.13/0.40  # Equation resolutions                 : 21
% 0.13/0.40  # Propositional unsat checks           : 0
% 0.13/0.40  #    Propositional check models        : 0
% 0.13/0.40  #    Propositional check unsatisfiable : 0
% 0.13/0.40  #    Propositional clauses             : 0
% 0.13/0.40  #    Propositional clauses after purity: 0
% 0.13/0.40  #    Propositional unsat core size     : 0
% 0.13/0.40  #    Propositional preprocessing time  : 0.000
% 0.13/0.40  #    Propositional encoding time       : 0.000
% 0.13/0.40  #    Propositional solver time         : 0.000
% 0.13/0.40  #    Success case prop preproc time    : 0.000
% 0.13/0.40  #    Success case prop encoding time   : 0.000
% 0.13/0.40  #    Success case prop solver time     : 0.000
% 0.13/0.40  # Current number of processed clauses  : 124
% 0.13/0.40  #    Positive orientable unit clauses  : 71
% 0.13/0.40  #    Positive unorientable unit clauses: 0
% 0.13/0.40  #    Negative unit clauses             : 1
% 0.13/0.40  #    Non-unit-clauses                  : 52
% 0.13/0.40  # Current number of unprocessed clauses: 1859
% 0.13/0.40  # ...number of literals in the above   : 3009
% 0.13/0.40  # Current number of archived formulas  : 0
% 0.13/0.40  # Current number of archived clauses   : 50
% 0.13/0.40  # Clause-clause subsumption calls (NU) : 512
% 0.13/0.40  # Rec. Clause-clause subsumption calls : 441
% 0.13/0.40  # Non-unit clause-clause subsumptions  : 8
% 0.13/0.40  # Unit Clause-clause subsumption calls : 20
% 0.13/0.40  # Rewrite failures with RHS unbound    : 0
% 0.13/0.40  # BW rewrite match attempts            : 299
% 0.13/0.40  # BW rewrite match successes           : 10
% 0.13/0.40  # Condensation attempts                : 0
% 0.13/0.40  # Condensation successes               : 0
% 0.13/0.40  # Termbank termtop insertions          : 43939
% 0.13/0.40  
% 0.13/0.40  # -------------------------------------------------
% 0.13/0.40  # User time                : 0.053 s
% 0.13/0.40  # System time              : 0.008 s
% 0.13/0.40  # Total time               : 0.061 s
% 0.13/0.40  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
