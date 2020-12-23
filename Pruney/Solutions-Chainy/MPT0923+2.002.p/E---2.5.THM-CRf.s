%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:31 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 364 expanded)
%              Number of clauses        :   55 ( 170 expanded)
%              Number of leaves         :   13 (  90 expanded)
%              Depth                    :   14
%              Number of atoms          :  299 (1090 expanded)
%              Number of equality atoms :  159 ( 392 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal clause size      :   30 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t83_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5] :
      ~ ( r2_hidden(X1,k4_zfmisc_1(X2,X3,X4,X5))
        & ! [X6,X7,X8,X9] :
            ~ ( r2_hidden(X6,X2)
              & r2_hidden(X7,X3)
              & r2_hidden(X8,X4)
              & r2_hidden(X9,X5)
              & X1 = k4_mcart_1(X6,X7,X8,X9) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_mcart_1)).

fof(t53_mcart_1,axiom,(
    ! [X1,X2,X3,X4] : k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_mcart_1)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

fof(l68_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & X4 != k1_xboole_0
        & ? [X5] :
            ( m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))
            & ! [X6] :
                ( m1_subset_1(X6,X1)
               => ! [X7] :
                    ( m1_subset_1(X7,X2)
                   => ! [X8] :
                        ( m1_subset_1(X8,X3)
                       => ! [X9] :
                            ( m1_subset_1(X9,X4)
                           => X5 != k4_mcart_1(X6,X7,X8,X9) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l68_mcart_1)).

fof(fc4_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => v1_xboole_0(k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_zfmisc_1)).

fof(t31_mcart_1,axiom,(
    ! [X1,X2,X3,X4] : k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_mcart_1)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(fc3_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X2)
     => v1_xboole_0(k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_zfmisc_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(t69_xboole_1,axiom,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ~ ( r1_tarski(X2,X1)
          & r1_xboole_0(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5] :
        ~ ( r2_hidden(X1,k4_zfmisc_1(X2,X3,X4,X5))
          & ! [X6,X7,X8,X9] :
              ~ ( r2_hidden(X6,X2)
                & r2_hidden(X7,X3)
                & r2_hidden(X8,X4)
                & r2_hidden(X9,X5)
                & X1 = k4_mcart_1(X6,X7,X8,X9) ) ) ),
    inference(assume_negation,[status(cth)],[t83_mcart_1])).

fof(c_0_14,negated_conjecture,(
    ! [X55,X56,X57,X58] :
      ( r2_hidden(esk6_0,k4_zfmisc_1(esk7_0,esk8_0,esk9_0,esk10_0))
      & ( ~ r2_hidden(X55,esk7_0)
        | ~ r2_hidden(X56,esk8_0)
        | ~ r2_hidden(X57,esk9_0)
        | ~ r2_hidden(X58,esk10_0)
        | esk6_0 != k4_mcart_1(X55,X56,X57,X58) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])])).

fof(c_0_15,plain,(
    ! [X46,X47,X48,X49] : k4_zfmisc_1(X46,X47,X48,X49) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X46,X47),X48),X49) ),
    inference(variable_rename,[status(thm)],[t53_mcart_1])).

fof(c_0_16,plain,(
    ! [X23,X24] :
      ( ~ r2_hidden(X23,X24)
      | ~ v1_xboole_0(X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_17,negated_conjecture,
    ( r2_hidden(esk6_0,k4_zfmisc_1(esk7_0,esk8_0,esk9_0,esk10_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_19,plain,(
    ! [X33,X34,X35,X36,X37] :
      ( ( m1_subset_1(esk2_5(X33,X34,X35,X36,X37),X33)
        | ~ m1_subset_1(X37,k4_zfmisc_1(X33,X34,X35,X36))
        | X33 = k1_xboole_0
        | X34 = k1_xboole_0
        | X35 = k1_xboole_0
        | X36 = k1_xboole_0 )
      & ( m1_subset_1(esk3_5(X33,X34,X35,X36,X37),X34)
        | ~ m1_subset_1(X37,k4_zfmisc_1(X33,X34,X35,X36))
        | X33 = k1_xboole_0
        | X34 = k1_xboole_0
        | X35 = k1_xboole_0
        | X36 = k1_xboole_0 )
      & ( m1_subset_1(esk4_5(X33,X34,X35,X36,X37),X35)
        | ~ m1_subset_1(X37,k4_zfmisc_1(X33,X34,X35,X36))
        | X33 = k1_xboole_0
        | X34 = k1_xboole_0
        | X35 = k1_xboole_0
        | X36 = k1_xboole_0 )
      & ( m1_subset_1(esk5_5(X33,X34,X35,X36,X37),X36)
        | ~ m1_subset_1(X37,k4_zfmisc_1(X33,X34,X35,X36))
        | X33 = k1_xboole_0
        | X34 = k1_xboole_0
        | X35 = k1_xboole_0
        | X36 = k1_xboole_0 )
      & ( X37 = k4_mcart_1(esk2_5(X33,X34,X35,X36,X37),esk3_5(X33,X34,X35,X36,X37),esk4_5(X33,X34,X35,X36,X37),esk5_5(X33,X34,X35,X36,X37))
        | ~ m1_subset_1(X37,k4_zfmisc_1(X33,X34,X35,X36))
        | X33 = k1_xboole_0
        | X34 = k1_xboole_0
        | X35 = k1_xboole_0
        | X36 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l68_mcart_1])])])])])).

cnf(c_0_20,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(esk6_0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),esk9_0),esk10_0)) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

fof(c_0_22,plain,(
    ! [X27,X28] :
      ( ~ v1_xboole_0(X27)
      | v1_xboole_0(k2_zfmisc_1(X27,X28)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc4_zfmisc_1])])).

fof(c_0_23,plain,(
    ! [X42,X43,X44,X45] : k4_mcart_1(X42,X43,X44,X45) = k4_tarski(k4_tarski(k4_tarski(X42,X43),X44),X45) ),
    inference(variable_rename,[status(thm)],[t31_mcart_1])).

cnf(c_0_24,plain,
    ( m1_subset_1(esk2_5(X1,X2,X3,X4,X5),X1)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_25,plain,(
    ! [X29,X30] :
      ( ~ r2_hidden(X29,X30)
      | m1_subset_1(X29,X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_26,negated_conjecture,
    ( ~ v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),esk9_0),esk10_0)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_27,plain,
    ( v1_xboole_0(k2_zfmisc_1(X1,X2))
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( m1_subset_1(esk3_5(X1,X2,X3,X4,X5),X2)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,plain,
    ( m1_subset_1(esk4_5(X1,X2,X3,X4,X5),X3)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,plain,
    ( m1_subset_1(esk5_5(X1,X2,X3,X4,X5),X4)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_31,plain,
    ( X1 = k4_mcart_1(esk2_5(X2,X3,X4,X5,X1),esk3_5(X2,X3,X4,X5,X1),esk4_5(X2,X3,X4,X5,X1),esk5_5(X2,X3,X4,X5,X1))
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X5 = k1_xboole_0
    | ~ m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_32,plain,
    ( k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,plain,
    ( X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | m1_subset_1(esk2_5(X1,X2,X3,X4,X5),X1)
    | ~ m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)) ),
    inference(rw,[status(thm)],[c_0_24,c_0_18])).

cnf(c_0_34,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,negated_conjecture,
    ( ~ v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),esk9_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_36,plain,
    ( X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | m1_subset_1(esk3_5(X1,X2,X3,X4,X5),X2)
    | ~ m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)) ),
    inference(rw,[status(thm)],[c_0_28,c_0_18])).

fof(c_0_37,plain,(
    ! [X25,X26] :
      ( ~ v1_xboole_0(X26)
      | v1_xboole_0(k2_zfmisc_1(X25,X26)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc3_zfmisc_1])])).

cnf(c_0_38,plain,
    ( X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | m1_subset_1(esk4_5(X1,X2,X3,X4,X5),X3)
    | ~ m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)) ),
    inference(rw,[status(thm)],[c_0_29,c_0_18])).

cnf(c_0_39,plain,
    ( X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | m1_subset_1(esk5_5(X1,X2,X3,X4,X5),X4)
    | ~ m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)) ),
    inference(rw,[status(thm)],[c_0_30,c_0_18])).

fof(c_0_40,plain,(
    ! [X19,X20] :
      ( ( r1_tarski(X19,X20)
        | X19 != X20 )
      & ( r1_tarski(X20,X19)
        | X19 != X20 )
      & ( ~ r1_tarski(X19,X20)
        | ~ r1_tarski(X20,X19)
        | X19 = X20 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_41,plain,
    ( X5 = k1_xboole_0
    | X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k4_tarski(k4_tarski(k4_tarski(esk2_5(X2,X3,X4,X5,X1),esk3_5(X2,X3,X4,X5,X1)),esk4_5(X2,X3,X4,X5,X1)),esk5_5(X2,X3,X4,X5,X1))
    | ~ m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4),X5)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_18]),c_0_32])).

fof(c_0_42,plain,(
    ! [X31,X32] :
      ( ~ m1_subset_1(X31,X32)
      | v1_xboole_0(X32)
      | r2_hidden(X31,X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_43,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | m1_subset_1(esk2_5(X1,X2,X3,X4,X5),X1)
    | ~ r2_hidden(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_44,negated_conjecture,
    ( ~ v1_xboole_0(k2_zfmisc_1(esk7_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_27])).

cnf(c_0_45,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | m1_subset_1(esk3_5(X1,X2,X3,X4,X5),X2)
    | ~ r2_hidden(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_34])).

cnf(c_0_46,plain,
    ( v1_xboole_0(k2_zfmisc_1(X2,X1))
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_47,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | m1_subset_1(esk4_5(X1,X2,X3,X4,X5),X3)
    | ~ r2_hidden(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_34])).

cnf(c_0_48,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | m1_subset_1(esk5_5(X1,X2,X3,X4,X5),X4)
    | ~ r2_hidden(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_34])).

fof(c_0_49,plain,(
    ! [X21,X22] :
      ( v1_xboole_0(X22)
      | ~ r1_tarski(X22,X21)
      | ~ r1_xboole_0(X22,X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_xboole_1])])])).

cnf(c_0_50,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_51,plain,(
    ! [X10,X11] :
      ( ( ~ r1_xboole_0(X10,X11)
        | k3_xboole_0(X10,X11) = k1_xboole_0 )
      & ( k3_xboole_0(X10,X11) != k1_xboole_0
        | r1_xboole_0(X10,X11) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

fof(c_0_52,plain,(
    ! [X12] : k3_xboole_0(X12,X12) = X12 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

cnf(c_0_53,negated_conjecture,
    ( ~ r2_hidden(X1,esk7_0)
    | ~ r2_hidden(X2,esk8_0)
    | ~ r2_hidden(X3,esk9_0)
    | ~ r2_hidden(X4,esk10_0)
    | esk6_0 != k4_mcart_1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_54,plain,
    ( k4_tarski(k4_tarski(k4_tarski(esk2_5(X1,X2,X3,X4,X5),esk3_5(X1,X2,X3,X4,X5)),esk4_5(X1,X2,X3,X4,X5)),esk5_5(X1,X2,X3,X4,X5)) = X5
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | ~ r2_hidden(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_34])).

cnf(c_0_55,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_56,negated_conjecture,
    ( esk10_0 = k1_xboole_0
    | esk9_0 = k1_xboole_0
    | esk8_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | m1_subset_1(esk2_5(esk7_0,esk8_0,esk9_0,esk10_0,esk6_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_21])).

cnf(c_0_57,negated_conjecture,
    ( ~ v1_xboole_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_27])).

cnf(c_0_58,negated_conjecture,
    ( esk10_0 = k1_xboole_0
    | esk9_0 = k1_xboole_0
    | esk8_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | m1_subset_1(esk3_5(esk7_0,esk8_0,esk9_0,esk10_0,esk6_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_21])).

cnf(c_0_59,negated_conjecture,
    ( ~ v1_xboole_0(esk8_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_46])).

cnf(c_0_60,negated_conjecture,
    ( esk10_0 = k1_xboole_0
    | esk9_0 = k1_xboole_0
    | esk8_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | m1_subset_1(esk4_5(esk7_0,esk8_0,esk9_0,esk10_0,esk6_0),esk9_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_21])).

cnf(c_0_61,negated_conjecture,
    ( ~ v1_xboole_0(esk9_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_46])).

cnf(c_0_62,negated_conjecture,
    ( esk10_0 = k1_xboole_0
    | esk9_0 = k1_xboole_0
    | esk8_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | m1_subset_1(esk5_5(esk7_0,esk8_0,esk9_0,esk10_0,esk6_0),esk10_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_21])).

cnf(c_0_63,negated_conjecture,
    ( ~ v1_xboole_0(esk10_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_46])).

cnf(c_0_64,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_65,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_50])).

cnf(c_0_66,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_67,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_68,negated_conjecture,
    ( esk6_0 != k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4)
    | ~ r2_hidden(X4,esk10_0)
    | ~ r2_hidden(X3,esk9_0)
    | ~ r2_hidden(X2,esk8_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(rw,[status(thm)],[c_0_53,c_0_32])).

cnf(c_0_69,negated_conjecture,
    ( k4_tarski(k4_tarski(k4_tarski(esk2_5(esk7_0,esk8_0,esk9_0,esk10_0,esk6_0),esk3_5(esk7_0,esk8_0,esk9_0,esk10_0,esk6_0)),esk4_5(esk7_0,esk8_0,esk9_0,esk10_0,esk6_0)),esk5_5(esk7_0,esk8_0,esk9_0,esk10_0,esk6_0)) = esk6_0
    | esk10_0 = k1_xboole_0
    | esk9_0 = k1_xboole_0
    | esk8_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_54,c_0_21])).

cnf(c_0_70,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | esk8_0 = k1_xboole_0
    | esk9_0 = k1_xboole_0
    | esk10_0 = k1_xboole_0
    | r2_hidden(esk2_5(esk7_0,esk8_0,esk9_0,esk10_0,esk6_0),esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57])).

cnf(c_0_71,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | esk8_0 = k1_xboole_0
    | esk9_0 = k1_xboole_0
    | esk10_0 = k1_xboole_0
    | r2_hidden(esk3_5(esk7_0,esk8_0,esk9_0,esk10_0,esk6_0),esk8_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_58]),c_0_59])).

cnf(c_0_72,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | esk8_0 = k1_xboole_0
    | esk9_0 = k1_xboole_0
    | esk10_0 = k1_xboole_0
    | r2_hidden(esk4_5(esk7_0,esk8_0,esk9_0,esk10_0,esk6_0),esk9_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_60]),c_0_61])).

cnf(c_0_73,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | esk8_0 = k1_xboole_0
    | esk9_0 = k1_xboole_0
    | esk10_0 = k1_xboole_0
    | r2_hidden(esk5_5(esk7_0,esk8_0,esk9_0,esk10_0,esk6_0),esk10_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_62]),c_0_63])).

cnf(c_0_74,plain,
    ( v1_xboole_0(X1)
    | ~ r1_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_75,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67])])).

cnf(c_0_76,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | esk8_0 = k1_xboole_0
    | esk9_0 = k1_xboole_0
    | esk10_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_70]),c_0_71]),c_0_72]),c_0_73])).

cnf(c_0_77,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_78,negated_conjecture,
    ( esk9_0 = k1_xboole_0
    | esk8_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_76]),c_0_77])])).

cnf(c_0_79,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | esk8_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_78]),c_0_77])])).

cnf(c_0_80,negated_conjecture,
    ( esk7_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_79]),c_0_77])])).

cnf(c_0_81,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_80]),c_0_77])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:38:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.39  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.39  #
% 0.20/0.39  # Preprocessing time       : 0.029 s
% 0.20/0.39  # Presaturation interreduction done
% 0.20/0.39  
% 0.20/0.39  # Proof found!
% 0.20/0.39  # SZS status Theorem
% 0.20/0.39  # SZS output start CNFRefutation
% 0.20/0.39  fof(t83_mcart_1, conjecture, ![X1, X2, X3, X4, X5]:~((r2_hidden(X1,k4_zfmisc_1(X2,X3,X4,X5))&![X6, X7, X8, X9]:~(((((r2_hidden(X6,X2)&r2_hidden(X7,X3))&r2_hidden(X8,X4))&r2_hidden(X9,X5))&X1=k4_mcart_1(X6,X7,X8,X9))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_mcart_1)).
% 0.20/0.39  fof(t53_mcart_1, axiom, ![X1, X2, X3, X4]:k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_mcart_1)).
% 0.20/0.39  fof(t7_boole, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&v1_xboole_0(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_boole)).
% 0.20/0.39  fof(l68_mcart_1, axiom, ![X1, X2, X3, X4]:~(((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&X4!=k1_xboole_0)&?[X5]:(m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))&![X6]:(m1_subset_1(X6,X1)=>![X7]:(m1_subset_1(X7,X2)=>![X8]:(m1_subset_1(X8,X3)=>![X9]:(m1_subset_1(X9,X4)=>X5!=k4_mcart_1(X6,X7,X8,X9)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l68_mcart_1)).
% 0.20/0.39  fof(fc4_zfmisc_1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>v1_xboole_0(k2_zfmisc_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_zfmisc_1)).
% 0.20/0.39  fof(t31_mcart_1, axiom, ![X1, X2, X3, X4]:k4_mcart_1(X1,X2,X3,X4)=k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_mcart_1)).
% 0.20/0.39  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 0.20/0.39  fof(fc3_zfmisc_1, axiom, ![X1, X2]:(v1_xboole_0(X2)=>v1_xboole_0(k2_zfmisc_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_zfmisc_1)).
% 0.20/0.39  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.39  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 0.20/0.39  fof(t69_xboole_1, axiom, ![X1, X2]:(~(v1_xboole_0(X2))=>~((r1_tarski(X2,X1)&r1_xboole_0(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 0.20/0.39  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.20/0.39  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.20/0.39  fof(c_0_13, negated_conjecture, ~(![X1, X2, X3, X4, X5]:~((r2_hidden(X1,k4_zfmisc_1(X2,X3,X4,X5))&![X6, X7, X8, X9]:~(((((r2_hidden(X6,X2)&r2_hidden(X7,X3))&r2_hidden(X8,X4))&r2_hidden(X9,X5))&X1=k4_mcart_1(X6,X7,X8,X9)))))), inference(assume_negation,[status(cth)],[t83_mcart_1])).
% 0.20/0.39  fof(c_0_14, negated_conjecture, ![X55, X56, X57, X58]:(r2_hidden(esk6_0,k4_zfmisc_1(esk7_0,esk8_0,esk9_0,esk10_0))&(~r2_hidden(X55,esk7_0)|~r2_hidden(X56,esk8_0)|~r2_hidden(X57,esk9_0)|~r2_hidden(X58,esk10_0)|esk6_0!=k4_mcart_1(X55,X56,X57,X58))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])])).
% 0.20/0.39  fof(c_0_15, plain, ![X46, X47, X48, X49]:k4_zfmisc_1(X46,X47,X48,X49)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X46,X47),X48),X49), inference(variable_rename,[status(thm)],[t53_mcart_1])).
% 0.20/0.39  fof(c_0_16, plain, ![X23, X24]:(~r2_hidden(X23,X24)|~v1_xboole_0(X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).
% 0.20/0.39  cnf(c_0_17, negated_conjecture, (r2_hidden(esk6_0,k4_zfmisc_1(esk7_0,esk8_0,esk9_0,esk10_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.39  cnf(c_0_18, plain, (k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.39  fof(c_0_19, plain, ![X33, X34, X35, X36, X37]:((m1_subset_1(esk2_5(X33,X34,X35,X36,X37),X33)|~m1_subset_1(X37,k4_zfmisc_1(X33,X34,X35,X36))|(X33=k1_xboole_0|X34=k1_xboole_0|X35=k1_xboole_0|X36=k1_xboole_0))&((m1_subset_1(esk3_5(X33,X34,X35,X36,X37),X34)|~m1_subset_1(X37,k4_zfmisc_1(X33,X34,X35,X36))|(X33=k1_xboole_0|X34=k1_xboole_0|X35=k1_xboole_0|X36=k1_xboole_0))&((m1_subset_1(esk4_5(X33,X34,X35,X36,X37),X35)|~m1_subset_1(X37,k4_zfmisc_1(X33,X34,X35,X36))|(X33=k1_xboole_0|X34=k1_xboole_0|X35=k1_xboole_0|X36=k1_xboole_0))&((m1_subset_1(esk5_5(X33,X34,X35,X36,X37),X36)|~m1_subset_1(X37,k4_zfmisc_1(X33,X34,X35,X36))|(X33=k1_xboole_0|X34=k1_xboole_0|X35=k1_xboole_0|X36=k1_xboole_0))&(X37=k4_mcart_1(esk2_5(X33,X34,X35,X36,X37),esk3_5(X33,X34,X35,X36,X37),esk4_5(X33,X34,X35,X36,X37),esk5_5(X33,X34,X35,X36,X37))|~m1_subset_1(X37,k4_zfmisc_1(X33,X34,X35,X36))|(X33=k1_xboole_0|X34=k1_xboole_0|X35=k1_xboole_0|X36=k1_xboole_0)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l68_mcart_1])])])])])).
% 0.20/0.39  cnf(c_0_20, plain, (~r2_hidden(X1,X2)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.39  cnf(c_0_21, negated_conjecture, (r2_hidden(esk6_0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),esk9_0),esk10_0))), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 0.20/0.39  fof(c_0_22, plain, ![X27, X28]:(~v1_xboole_0(X27)|v1_xboole_0(k2_zfmisc_1(X27,X28))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc4_zfmisc_1])])).
% 0.20/0.39  fof(c_0_23, plain, ![X42, X43, X44, X45]:k4_mcart_1(X42,X43,X44,X45)=k4_tarski(k4_tarski(k4_tarski(X42,X43),X44),X45), inference(variable_rename,[status(thm)],[t31_mcart_1])).
% 0.20/0.39  cnf(c_0_24, plain, (m1_subset_1(esk2_5(X1,X2,X3,X4,X5),X1)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|~m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.39  fof(c_0_25, plain, ![X29, X30]:(~r2_hidden(X29,X30)|m1_subset_1(X29,X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.20/0.39  cnf(c_0_26, negated_conjecture, (~v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),esk9_0),esk10_0))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.20/0.39  cnf(c_0_27, plain, (v1_xboole_0(k2_zfmisc_1(X1,X2))|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.39  cnf(c_0_28, plain, (m1_subset_1(esk3_5(X1,X2,X3,X4,X5),X2)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|~m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.39  cnf(c_0_29, plain, (m1_subset_1(esk4_5(X1,X2,X3,X4,X5),X3)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|~m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.39  cnf(c_0_30, plain, (m1_subset_1(esk5_5(X1,X2,X3,X4,X5),X4)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|~m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.39  cnf(c_0_31, plain, (X1=k4_mcart_1(esk2_5(X2,X3,X4,X5,X1),esk3_5(X2,X3,X4,X5,X1),esk4_5(X2,X3,X4,X5,X1),esk5_5(X2,X3,X4,X5,X1))|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5=k1_xboole_0|~m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.39  cnf(c_0_32, plain, (k4_mcart_1(X1,X2,X3,X4)=k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.39  cnf(c_0_33, plain, (X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|m1_subset_1(esk2_5(X1,X2,X3,X4,X5),X1)|~m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))), inference(rw,[status(thm)],[c_0_24, c_0_18])).
% 0.20/0.39  cnf(c_0_34, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.39  cnf(c_0_35, negated_conjecture, (~v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),esk9_0))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.20/0.39  cnf(c_0_36, plain, (X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|m1_subset_1(esk3_5(X1,X2,X3,X4,X5),X2)|~m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))), inference(rw,[status(thm)],[c_0_28, c_0_18])).
% 0.20/0.39  fof(c_0_37, plain, ![X25, X26]:(~v1_xboole_0(X26)|v1_xboole_0(k2_zfmisc_1(X25,X26))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc3_zfmisc_1])])).
% 0.20/0.39  cnf(c_0_38, plain, (X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|m1_subset_1(esk4_5(X1,X2,X3,X4,X5),X3)|~m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))), inference(rw,[status(thm)],[c_0_29, c_0_18])).
% 0.20/0.39  cnf(c_0_39, plain, (X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|m1_subset_1(esk5_5(X1,X2,X3,X4,X5),X4)|~m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))), inference(rw,[status(thm)],[c_0_30, c_0_18])).
% 0.20/0.39  fof(c_0_40, plain, ![X19, X20]:(((r1_tarski(X19,X20)|X19!=X20)&(r1_tarski(X20,X19)|X19!=X20))&(~r1_tarski(X19,X20)|~r1_tarski(X20,X19)|X19=X20)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.39  cnf(c_0_41, plain, (X5=k1_xboole_0|X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k4_tarski(k4_tarski(k4_tarski(esk2_5(X2,X3,X4,X5,X1),esk3_5(X2,X3,X4,X5,X1)),esk4_5(X2,X3,X4,X5,X1)),esk5_5(X2,X3,X4,X5,X1))|~m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4),X5))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_18]), c_0_32])).
% 0.20/0.39  fof(c_0_42, plain, ![X31, X32]:(~m1_subset_1(X31,X32)|(v1_xboole_0(X32)|r2_hidden(X31,X32))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.20/0.39  cnf(c_0_43, plain, (X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|m1_subset_1(esk2_5(X1,X2,X3,X4,X5),X1)|~r2_hidden(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.20/0.39  cnf(c_0_44, negated_conjecture, (~v1_xboole_0(k2_zfmisc_1(esk7_0,esk8_0))), inference(spm,[status(thm)],[c_0_35, c_0_27])).
% 0.20/0.39  cnf(c_0_45, plain, (X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|m1_subset_1(esk3_5(X1,X2,X3,X4,X5),X2)|~r2_hidden(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))), inference(spm,[status(thm)],[c_0_36, c_0_34])).
% 0.20/0.39  cnf(c_0_46, plain, (v1_xboole_0(k2_zfmisc_1(X2,X1))|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.39  cnf(c_0_47, plain, (X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|m1_subset_1(esk4_5(X1,X2,X3,X4,X5),X3)|~r2_hidden(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))), inference(spm,[status(thm)],[c_0_38, c_0_34])).
% 0.20/0.39  cnf(c_0_48, plain, (X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|m1_subset_1(esk5_5(X1,X2,X3,X4,X5),X4)|~r2_hidden(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))), inference(spm,[status(thm)],[c_0_39, c_0_34])).
% 0.20/0.39  fof(c_0_49, plain, ![X21, X22]:(v1_xboole_0(X22)|(~r1_tarski(X22,X21)|~r1_xboole_0(X22,X21))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_xboole_1])])])).
% 0.20/0.39  cnf(c_0_50, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.39  fof(c_0_51, plain, ![X10, X11]:((~r1_xboole_0(X10,X11)|k3_xboole_0(X10,X11)=k1_xboole_0)&(k3_xboole_0(X10,X11)!=k1_xboole_0|r1_xboole_0(X10,X11))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.20/0.39  fof(c_0_52, plain, ![X12]:k3_xboole_0(X12,X12)=X12, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.20/0.39  cnf(c_0_53, negated_conjecture, (~r2_hidden(X1,esk7_0)|~r2_hidden(X2,esk8_0)|~r2_hidden(X3,esk9_0)|~r2_hidden(X4,esk10_0)|esk6_0!=k4_mcart_1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.39  cnf(c_0_54, plain, (k4_tarski(k4_tarski(k4_tarski(esk2_5(X1,X2,X3,X4,X5),esk3_5(X1,X2,X3,X4,X5)),esk4_5(X1,X2,X3,X4,X5)),esk5_5(X1,X2,X3,X4,X5))=X5|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|~r2_hidden(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))), inference(spm,[status(thm)],[c_0_41, c_0_34])).
% 0.20/0.39  cnf(c_0_55, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.39  cnf(c_0_56, negated_conjecture, (esk10_0=k1_xboole_0|esk9_0=k1_xboole_0|esk8_0=k1_xboole_0|esk7_0=k1_xboole_0|m1_subset_1(esk2_5(esk7_0,esk8_0,esk9_0,esk10_0,esk6_0),esk7_0)), inference(spm,[status(thm)],[c_0_43, c_0_21])).
% 0.20/0.39  cnf(c_0_57, negated_conjecture, (~v1_xboole_0(esk7_0)), inference(spm,[status(thm)],[c_0_44, c_0_27])).
% 0.20/0.39  cnf(c_0_58, negated_conjecture, (esk10_0=k1_xboole_0|esk9_0=k1_xboole_0|esk8_0=k1_xboole_0|esk7_0=k1_xboole_0|m1_subset_1(esk3_5(esk7_0,esk8_0,esk9_0,esk10_0,esk6_0),esk8_0)), inference(spm,[status(thm)],[c_0_45, c_0_21])).
% 0.20/0.39  cnf(c_0_59, negated_conjecture, (~v1_xboole_0(esk8_0)), inference(spm,[status(thm)],[c_0_44, c_0_46])).
% 0.20/0.39  cnf(c_0_60, negated_conjecture, (esk10_0=k1_xboole_0|esk9_0=k1_xboole_0|esk8_0=k1_xboole_0|esk7_0=k1_xboole_0|m1_subset_1(esk4_5(esk7_0,esk8_0,esk9_0,esk10_0,esk6_0),esk9_0)), inference(spm,[status(thm)],[c_0_47, c_0_21])).
% 0.20/0.39  cnf(c_0_61, negated_conjecture, (~v1_xboole_0(esk9_0)), inference(spm,[status(thm)],[c_0_35, c_0_46])).
% 0.20/0.39  cnf(c_0_62, negated_conjecture, (esk10_0=k1_xboole_0|esk9_0=k1_xboole_0|esk8_0=k1_xboole_0|esk7_0=k1_xboole_0|m1_subset_1(esk5_5(esk7_0,esk8_0,esk9_0,esk10_0,esk6_0),esk10_0)), inference(spm,[status(thm)],[c_0_48, c_0_21])).
% 0.20/0.39  cnf(c_0_63, negated_conjecture, (~v1_xboole_0(esk10_0)), inference(spm,[status(thm)],[c_0_26, c_0_46])).
% 0.20/0.39  cnf(c_0_64, plain, (v1_xboole_0(X1)|~r1_tarski(X1,X2)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.20/0.39  cnf(c_0_65, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_50])).
% 0.20/0.39  cnf(c_0_66, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.20/0.39  cnf(c_0_67, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.20/0.39  cnf(c_0_68, negated_conjecture, (esk6_0!=k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4)|~r2_hidden(X4,esk10_0)|~r2_hidden(X3,esk9_0)|~r2_hidden(X2,esk8_0)|~r2_hidden(X1,esk7_0)), inference(rw,[status(thm)],[c_0_53, c_0_32])).
% 0.20/0.39  cnf(c_0_69, negated_conjecture, (k4_tarski(k4_tarski(k4_tarski(esk2_5(esk7_0,esk8_0,esk9_0,esk10_0,esk6_0),esk3_5(esk7_0,esk8_0,esk9_0,esk10_0,esk6_0)),esk4_5(esk7_0,esk8_0,esk9_0,esk10_0,esk6_0)),esk5_5(esk7_0,esk8_0,esk9_0,esk10_0,esk6_0))=esk6_0|esk10_0=k1_xboole_0|esk9_0=k1_xboole_0|esk8_0=k1_xboole_0|esk7_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_54, c_0_21])).
% 0.20/0.39  cnf(c_0_70, negated_conjecture, (esk7_0=k1_xboole_0|esk8_0=k1_xboole_0|esk9_0=k1_xboole_0|esk10_0=k1_xboole_0|r2_hidden(esk2_5(esk7_0,esk8_0,esk9_0,esk10_0,esk6_0),esk7_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_57])).
% 0.20/0.39  cnf(c_0_71, negated_conjecture, (esk7_0=k1_xboole_0|esk8_0=k1_xboole_0|esk9_0=k1_xboole_0|esk10_0=k1_xboole_0|r2_hidden(esk3_5(esk7_0,esk8_0,esk9_0,esk10_0,esk6_0),esk8_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_58]), c_0_59])).
% 0.20/0.39  cnf(c_0_72, negated_conjecture, (esk7_0=k1_xboole_0|esk8_0=k1_xboole_0|esk9_0=k1_xboole_0|esk10_0=k1_xboole_0|r2_hidden(esk4_5(esk7_0,esk8_0,esk9_0,esk10_0,esk6_0),esk9_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_60]), c_0_61])).
% 0.20/0.39  cnf(c_0_73, negated_conjecture, (esk7_0=k1_xboole_0|esk8_0=k1_xboole_0|esk9_0=k1_xboole_0|esk10_0=k1_xboole_0|r2_hidden(esk5_5(esk7_0,esk8_0,esk9_0,esk10_0,esk6_0),esk10_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_62]), c_0_63])).
% 0.20/0.39  cnf(c_0_74, plain, (v1_xboole_0(X1)|~r1_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.20/0.39  cnf(c_0_75, plain, (r1_xboole_0(k1_xboole_0,k1_xboole_0)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67])])).
% 0.20/0.39  cnf(c_0_76, negated_conjecture, (esk7_0=k1_xboole_0|esk8_0=k1_xboole_0|esk9_0=k1_xboole_0|esk10_0=k1_xboole_0), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_70]), c_0_71]), c_0_72]), c_0_73])).
% 0.20/0.39  cnf(c_0_77, plain, (v1_xboole_0(k1_xboole_0)), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 0.20/0.39  cnf(c_0_78, negated_conjecture, (esk9_0=k1_xboole_0|esk8_0=k1_xboole_0|esk7_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_76]), c_0_77])])).
% 0.20/0.39  cnf(c_0_79, negated_conjecture, (esk7_0=k1_xboole_0|esk8_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_78]), c_0_77])])).
% 0.20/0.39  cnf(c_0_80, negated_conjecture, (esk7_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_79]), c_0_77])])).
% 0.20/0.39  cnf(c_0_81, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_80]), c_0_77])]), ['proof']).
% 0.20/0.39  # SZS output end CNFRefutation
% 0.20/0.39  # Proof object total steps             : 82
% 0.20/0.39  # Proof object clause steps            : 55
% 0.20/0.39  # Proof object formula steps           : 27
% 0.20/0.39  # Proof object conjectures             : 28
% 0.20/0.39  # Proof object clause conjectures      : 25
% 0.20/0.39  # Proof object formula conjectures     : 3
% 0.20/0.39  # Proof object initial clauses used    : 18
% 0.20/0.39  # Proof object initial formulas used   : 13
% 0.20/0.39  # Proof object generating inferences   : 28
% 0.20/0.39  # Proof object simplifying inferences  : 27
% 0.20/0.39  # Training examples: 0 positive, 0 negative
% 0.20/0.39  # Parsed axioms                        : 14
% 0.20/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.39  # Initial clauses                      : 24
% 0.20/0.39  # Removed in clause preprocessing      : 2
% 0.20/0.39  # Initial clauses in saturation        : 22
% 0.20/0.39  # Processed clauses                    : 352
% 0.20/0.39  # ...of these trivial                  : 0
% 0.20/0.39  # ...subsumed                          : 222
% 0.20/0.39  # ...remaining for further processing  : 130
% 0.20/0.39  # Other redundant clauses eliminated   : 3
% 0.20/0.39  # Clauses deleted for lack of memory   : 0
% 0.20/0.39  # Backward-subsumed                    : 15
% 0.20/0.39  # Backward-rewritten                   : 9
% 0.20/0.39  # Generated clauses                    : 412
% 0.20/0.39  # ...of the previous two non-trivial   : 386
% 0.20/0.39  # Contextual simplify-reflections      : 4
% 0.20/0.39  # Paramodulations                      : 409
% 0.20/0.39  # Factorizations                       : 0
% 0.20/0.39  # Equation resolutions                 : 3
% 0.20/0.39  # Propositional unsat checks           : 0
% 0.20/0.39  #    Propositional check models        : 0
% 0.20/0.39  #    Propositional check unsatisfiable : 0
% 0.20/0.39  #    Propositional clauses             : 0
% 0.20/0.39  #    Propositional clauses after purity: 0
% 0.20/0.39  #    Propositional unsat core size     : 0
% 0.20/0.39  #    Propositional preprocessing time  : 0.000
% 0.20/0.39  #    Propositional encoding time       : 0.000
% 0.20/0.39  #    Propositional solver time         : 0.000
% 0.20/0.39  #    Success case prop preproc time    : 0.000
% 0.20/0.39  #    Success case prop encoding time   : 0.000
% 0.20/0.39  #    Success case prop solver time     : 0.000
% 0.20/0.39  # Current number of processed clauses  : 83
% 0.20/0.39  #    Positive orientable unit clauses  : 6
% 0.20/0.39  #    Positive unorientable unit clauses: 0
% 0.20/0.39  #    Negative unit clauses             : 4
% 0.20/0.39  #    Non-unit-clauses                  : 73
% 0.20/0.39  # Current number of unprocessed clauses: 77
% 0.20/0.39  # ...number of literals in the above   : 633
% 0.20/0.39  # Current number of archived formulas  : 0
% 0.20/0.39  # Current number of archived clauses   : 47
% 0.20/0.39  # Clause-clause subsumption calls (NU) : 2311
% 0.20/0.39  # Rec. Clause-clause subsumption calls : 942
% 0.20/0.39  # Non-unit clause-clause subsumptions  : 212
% 0.20/0.39  # Unit Clause-clause subsumption calls : 58
% 0.20/0.39  # Rewrite failures with RHS unbound    : 0
% 0.20/0.39  # BW rewrite match attempts            : 2
% 0.20/0.39  # BW rewrite match successes           : 2
% 0.20/0.39  # Condensation attempts                : 0
% 0.20/0.39  # Condensation successes               : 0
% 0.20/0.39  # Termbank termtop insertions          : 9535
% 0.20/0.39  
% 0.20/0.39  # -------------------------------------------------
% 0.20/0.39  # User time                : 0.047 s
% 0.20/0.39  # System time              : 0.004 s
% 0.20/0.39  # Total time               : 0.051 s
% 0.20/0.39  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
