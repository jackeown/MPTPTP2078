%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:04 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 391 expanded)
%              Number of clauses        :   52 ( 154 expanded)
%              Number of leaves         :   14 (  98 expanded)
%              Depth                    :   13
%              Number of atoms          :  277 (1830 expanded)
%              Number of equality atoms :  221 (1553 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   24 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t62_mcart_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & X4 != k1_xboole_0
        & ~ ! [X5] :
              ( m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))
             => ( X5 != k8_mcart_1(X1,X2,X3,X4,X5)
                & X5 != k9_mcart_1(X1,X2,X3,X4,X5)
                & X5 != k10_mcart_1(X1,X2,X3,X4,X5)
                & X5 != k11_mcart_1(X1,X2,X3,X4,X5) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_mcart_1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(t49_zfmisc_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(t61_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & X4 != k1_xboole_0
        & ~ ! [X5] :
              ( m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))
             => ( k8_mcart_1(X1,X2,X3,X4,X5) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X5)))
                & k9_mcart_1(X1,X2,X3,X4,X5) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X5)))
                & k10_mcart_1(X1,X2,X3,X4,X5) = k2_mcart_1(k1_mcart_1(X5))
                & k11_mcart_1(X1,X2,X3,X4,X5) = k2_mcart_1(X5) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_mcart_1)).

fof(t53_mcart_1,axiom,(
    ! [X1,X2,X3,X4] : k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_mcart_1)).

fof(t29_mcart_1,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] :
            ~ ( r2_hidden(X2,X1)
              & ! [X3,X4,X5] :
                  ~ ( ( r2_hidden(X3,X1)
                      | r2_hidden(X4,X1) )
                    & X2 = k3_mcart_1(X3,X4,X5) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(t60_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & X4 != k1_xboole_0
        & ~ ! [X5] :
              ( m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))
             => X5 = k4_mcart_1(k8_mcart_1(X1,X2,X3,X4,X5),k9_mcart_1(X1,X2,X3,X4,X5),k10_mcart_1(X1,X2,X3,X4,X5),k11_mcart_1(X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_mcart_1)).

fof(t31_mcart_1,axiom,(
    ! [X1,X2,X3,X4] : k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_mcart_1)).

fof(t34_mcart_1,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] :
            ~ ( r2_hidden(X2,X1)
              & ! [X3,X4,X5,X6] :
                  ~ ( ( r2_hidden(X3,X1)
                      | r2_hidden(X4,X1) )
                    & X2 = k4_mcart_1(X3,X4,X5,X6) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_mcart_1)).

fof(t26_mcart_1,axiom,(
    ! [X1,X2] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & ~ ! [X3] :
              ( m1_subset_1(X3,k2_zfmisc_1(X1,X2))
             => ( X3 != k1_mcart_1(X3)
                & X3 != k2_mcart_1(X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_mcart_1)).

fof(t55_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & X4 != k1_xboole_0 )
    <=> k4_zfmisc_1(X1,X2,X3,X4) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_mcart_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ~ ( X1 != k1_xboole_0
          & X2 != k1_xboole_0
          & X3 != k1_xboole_0
          & X4 != k1_xboole_0
          & ~ ! [X5] :
                ( m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))
               => ( X5 != k8_mcart_1(X1,X2,X3,X4,X5)
                  & X5 != k9_mcart_1(X1,X2,X3,X4,X5)
                  & X5 != k10_mcart_1(X1,X2,X3,X4,X5)
                  & X5 != k11_mcart_1(X1,X2,X3,X4,X5) ) ) ) ),
    inference(assume_negation,[status(cth)],[t62_mcart_1])).

fof(c_0_15,plain,(
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

fof(c_0_16,plain,(
    ! [X22,X23] : k2_xboole_0(k1_tarski(X22),X23) != k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t49_zfmisc_1])).

fof(c_0_17,plain,(
    ! [X7] : k2_xboole_0(X7,X7) = X7 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

fof(c_0_18,plain,(
    ! [X58,X59,X60,X61,X62] :
      ( ( k8_mcart_1(X58,X59,X60,X61,X62) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X62)))
        | ~ m1_subset_1(X62,k4_zfmisc_1(X58,X59,X60,X61))
        | X58 = k1_xboole_0
        | X59 = k1_xboole_0
        | X60 = k1_xboole_0
        | X61 = k1_xboole_0 )
      & ( k9_mcart_1(X58,X59,X60,X61,X62) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X62)))
        | ~ m1_subset_1(X62,k4_zfmisc_1(X58,X59,X60,X61))
        | X58 = k1_xboole_0
        | X59 = k1_xboole_0
        | X60 = k1_xboole_0
        | X61 = k1_xboole_0 )
      & ( k10_mcart_1(X58,X59,X60,X61,X62) = k2_mcart_1(k1_mcart_1(X62))
        | ~ m1_subset_1(X62,k4_zfmisc_1(X58,X59,X60,X61))
        | X58 = k1_xboole_0
        | X59 = k1_xboole_0
        | X60 = k1_xboole_0
        | X61 = k1_xboole_0 )
      & ( k11_mcart_1(X58,X59,X60,X61,X62) = k2_mcart_1(X62)
        | ~ m1_subset_1(X62,k4_zfmisc_1(X58,X59,X60,X61))
        | X58 = k1_xboole_0
        | X59 = k1_xboole_0
        | X60 = k1_xboole_0
        | X61 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_mcart_1])])])])).

fof(c_0_19,plain,(
    ! [X45,X46,X47,X48] : k4_zfmisc_1(X45,X46,X47,X48) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X45,X46),X47),X48) ),
    inference(variable_rename,[status(thm)],[t53_mcart_1])).

fof(c_0_20,negated_conjecture,
    ( esk4_0 != k1_xboole_0
    & esk5_0 != k1_xboole_0
    & esk6_0 != k1_xboole_0
    & esk7_0 != k1_xboole_0
    & m1_subset_1(esk8_0,k4_zfmisc_1(esk4_0,esk5_0,esk6_0,esk7_0))
    & ( esk8_0 = k8_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0)
      | esk8_0 = k9_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0)
      | esk8_0 = k10_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0)
      | esk8_0 = k11_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

fof(c_0_21,plain,(
    ! [X30,X32,X33,X34] :
      ( ( r2_hidden(esk2_1(X30),X30)
        | X30 = k1_xboole_0 )
      & ( ~ r2_hidden(X32,X30)
        | esk2_1(X30) != k3_mcart_1(X32,X33,X34)
        | X30 = k1_xboole_0 )
      & ( ~ r2_hidden(X33,X30)
        | esk2_1(X30) != k3_mcart_1(X32,X33,X34)
        | X30 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_mcart_1])])])])])])).

fof(c_0_22,plain,(
    ! [X24,X25,X26] : k3_mcart_1(X24,X25,X26) = k4_tarski(k4_tarski(X24,X25),X26) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

cnf(c_0_23,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_26,plain,(
    ! [X53,X54,X55,X56,X57] :
      ( X53 = k1_xboole_0
      | X54 = k1_xboole_0
      | X55 = k1_xboole_0
      | X56 = k1_xboole_0
      | ~ m1_subset_1(X57,k4_zfmisc_1(X53,X54,X55,X56))
      | X57 = k4_mcart_1(k8_mcart_1(X53,X54,X55,X56,X57),k9_mcart_1(X53,X54,X55,X56,X57),k10_mcart_1(X53,X54,X55,X56,X57),k11_mcart_1(X53,X54,X55,X56,X57)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_mcart_1])])])).

fof(c_0_27,plain,(
    ! [X35,X36,X37,X38] : k4_mcart_1(X35,X36,X37,X38) = k4_tarski(k4_tarski(k4_tarski(X35,X36),X37),X38) ),
    inference(variable_rename,[status(thm)],[t31_mcart_1])).

cnf(c_0_28,plain,
    ( k11_mcart_1(X1,X2,X3,X4,X5) = k2_mcart_1(X5)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,plain,
    ( k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk8_0,k4_zfmisc_1(esk4_0,esk5_0,esk6_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_31,plain,(
    ! [X39,X41,X42,X43,X44] :
      ( ( r2_hidden(esk3_1(X39),X39)
        | X39 = k1_xboole_0 )
      & ( ~ r2_hidden(X41,X39)
        | esk3_1(X39) != k4_mcart_1(X41,X42,X43,X44)
        | X39 = k1_xboole_0 )
      & ( ~ r2_hidden(X42,X39)
        | esk3_1(X39) != k4_mcart_1(X41,X42,X43,X44)
        | X39 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_mcart_1])])])])])])).

cnf(c_0_32,plain,
    ( X2 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | esk2_1(X2) != k3_mcart_1(X3,X1,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_33,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_34,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k1_tarski(X2)) ),
    inference(er,[status(thm)],[c_0_23])).

cnf(c_0_35,plain,
    ( r2_hidden(esk2_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_36,plain,
    ( k1_tarski(X1) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_37,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X5 = k4_mcart_1(k8_mcart_1(X1,X2,X3,X4,X5),k9_mcart_1(X1,X2,X3,X4,X5),k10_mcart_1(X1,X2,X3,X4,X5),k11_mcart_1(X1,X2,X3,X4,X5))
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_38,plain,
    ( k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_39,plain,
    ( X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k11_mcart_1(X1,X2,X3,X4,X5) = k2_mcart_1(X5)
    | ~ m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)) ),
    inference(rw,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(esk8_0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0),esk7_0)) ),
    inference(rw,[status(thm)],[c_0_30,c_0_29])).

cnf(c_0_41,negated_conjecture,
    ( esk7_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_42,negated_conjecture,
    ( esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_43,negated_conjecture,
    ( esk5_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_44,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_45,plain,
    ( X2 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | esk3_1(X2) != k4_mcart_1(X3,X1,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_46,plain,
    ( r2_hidden(esk3_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_47,plain,
    ( X2 = k1_xboole_0
    | esk2_1(X2) != k4_tarski(k4_tarski(X3,X1),X4)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_48,plain,
    ( esk2_1(k1_tarski(X1)) = X1 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])).

cnf(c_0_49,plain,
    ( X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | X5 = k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(X1,X2,X3,X4,X5),k9_mcart_1(X1,X2,X3,X4,X5)),k10_mcart_1(X1,X2,X3,X4,X5)),k11_mcart_1(X1,X2,X3,X4,X5))
    | ~ m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_38]),c_0_29])).

cnf(c_0_50,negated_conjecture,
    ( k11_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0) = k2_mcart_1(esk8_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41]),c_0_42]),c_0_43]),c_0_44])).

cnf(c_0_51,plain,
    ( X2 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | esk3_1(X2) != k4_mcart_1(X1,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_52,plain,
    ( X2 = k1_xboole_0
    | esk3_1(X2) != k4_tarski(k4_tarski(k4_tarski(X3,X1),X4),X5)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_45,c_0_38])).

cnf(c_0_53,plain,
    ( esk3_1(k1_tarski(X1)) = X1 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_46]),c_0_36])).

cnf(c_0_54,plain,
    ( ~ r2_hidden(X1,k1_tarski(k4_tarski(k4_tarski(X2,X1),X3))) ),
    inference(er,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_36])])).

cnf(c_0_55,negated_conjecture,
    ( k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k9_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0)),k10_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0)),k2_mcart_1(esk8_0)) = esk8_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_40]),c_0_50]),c_0_41]),c_0_42]),c_0_43]),c_0_44])).

cnf(c_0_56,negated_conjecture,
    ( esk8_0 = k8_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0)
    | esk8_0 = k9_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0)
    | esk8_0 = k10_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0)
    | esk8_0 = k11_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_57,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_58,plain,
    ( X2 = k1_xboole_0
    | esk3_1(X2) != k4_tarski(k4_tarski(k4_tarski(X1,X3),X4),X5)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_51,c_0_38])).

cnf(c_0_59,plain,
    ( ~ r2_hidden(X1,k1_tarski(k4_tarski(k4_tarski(k4_tarski(X2,X1),X3),X4))) ),
    inference(er,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_36])])).

cnf(c_0_60,negated_conjecture,
    ( ~ r2_hidden(k10_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k1_tarski(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_61,negated_conjecture,
    ( k10_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0) = esk8_0
    | k9_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0) = esk8_0
    | k8_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0) = esk8_0
    | k2_mcart_1(esk8_0) = esk8_0 ),
    inference(spm,[status(thm)],[c_0_56,c_0_50])).

cnf(c_0_62,plain,
    ( r2_hidden(X1,k1_tarski(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_57])])).

fof(c_0_63,plain,(
    ! [X27,X28,X29] :
      ( ( X29 != k1_mcart_1(X29)
        | ~ m1_subset_1(X29,k2_zfmisc_1(X27,X28))
        | X27 = k1_xboole_0
        | X28 = k1_xboole_0 )
      & ( X29 != k2_mcart_1(X29)
        | ~ m1_subset_1(X29,k2_zfmisc_1(X27,X28))
        | X27 = k1_xboole_0
        | X28 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_mcart_1])])])])).

cnf(c_0_64,plain,
    ( ~ r2_hidden(X1,k1_tarski(k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4))) ),
    inference(er,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_53]),c_0_36])])).

cnf(c_0_65,negated_conjecture,
    ( ~ r2_hidden(k9_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k1_tarski(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_55])).

cnf(c_0_66,negated_conjecture,
    ( k8_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0) = esk8_0
    | k9_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0) = esk8_0
    | k2_mcart_1(esk8_0) = esk8_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_62])])).

fof(c_0_67,plain,(
    ! [X49,X50,X51,X52] :
      ( ( X49 = k1_xboole_0
        | X50 = k1_xboole_0
        | X51 = k1_xboole_0
        | X52 = k1_xboole_0
        | k4_zfmisc_1(X49,X50,X51,X52) != k1_xboole_0 )
      & ( X49 != k1_xboole_0
        | k4_zfmisc_1(X49,X50,X51,X52) = k1_xboole_0 )
      & ( X50 != k1_xboole_0
        | k4_zfmisc_1(X49,X50,X51,X52) = k1_xboole_0 )
      & ( X51 != k1_xboole_0
        | k4_zfmisc_1(X49,X50,X51,X52) = k1_xboole_0 )
      & ( X52 != k1_xboole_0
        | k4_zfmisc_1(X49,X50,X51,X52) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_mcart_1])])])).

cnf(c_0_68,plain,
    ( X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X1 != k2_mcart_1(X1)
    | ~ m1_subset_1(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_69,negated_conjecture,
    ( ~ r2_hidden(k8_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k1_tarski(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_55])).

cnf(c_0_70,negated_conjecture,
    ( k8_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0) = esk8_0
    | k2_mcart_1(esk8_0) = esk8_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_62])])).

fof(c_0_71,plain,(
    ! [X18,X19] :
      ( ( k2_zfmisc_1(X18,X19) != k1_xboole_0
        | X18 = k1_xboole_0
        | X19 = k1_xboole_0 )
      & ( X18 != k1_xboole_0
        | k2_zfmisc_1(X18,X19) = k1_xboole_0 )
      & ( X19 != k1_xboole_0
        | k2_zfmisc_1(X18,X19) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_72,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | k4_zfmisc_1(X1,X2,X3,X4) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_73,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0) = k1_xboole_0
    | k2_mcart_1(esk8_0) != esk8_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_40]),c_0_41])).

cnf(c_0_74,negated_conjecture,
    ( k2_mcart_1(esk8_0) = esk8_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_62])])).

cnf(c_0_75,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_76,plain,
    ( X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_72,c_0_29])).

cnf(c_0_77,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_74])])).

cnf(c_0_78,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_75])).

cnf(c_0_79,negated_conjecture,
    ( X1 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_78])]),c_0_42]),c_0_43]),c_0_44])).

cnf(c_0_80,plain,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_79])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:09:44 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.38  #
% 0.19/0.38  # Preprocessing time       : 0.029 s
% 0.19/0.38  # Presaturation interreduction done
% 0.19/0.38  
% 0.19/0.38  # Proof found!
% 0.19/0.38  # SZS status Theorem
% 0.19/0.38  # SZS output start CNFRefutation
% 0.19/0.38  fof(t62_mcart_1, conjecture, ![X1, X2, X3, X4]:~(((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&X4!=k1_xboole_0)&~(![X5]:(m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))=>(((X5!=k8_mcart_1(X1,X2,X3,X4,X5)&X5!=k9_mcart_1(X1,X2,X3,X4,X5))&X5!=k10_mcart_1(X1,X2,X3,X4,X5))&X5!=k11_mcart_1(X1,X2,X3,X4,X5)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_mcart_1)).
% 0.19/0.38  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 0.19/0.38  fof(t49_zfmisc_1, axiom, ![X1, X2]:k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 0.19/0.38  fof(idempotence_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 0.19/0.38  fof(t61_mcart_1, axiom, ![X1, X2, X3, X4]:~(((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&X4!=k1_xboole_0)&~(![X5]:(m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))=>(((k8_mcart_1(X1,X2,X3,X4,X5)=k1_mcart_1(k1_mcart_1(k1_mcart_1(X5)))&k9_mcart_1(X1,X2,X3,X4,X5)=k2_mcart_1(k1_mcart_1(k1_mcart_1(X5))))&k10_mcart_1(X1,X2,X3,X4,X5)=k2_mcart_1(k1_mcart_1(X5)))&k11_mcart_1(X1,X2,X3,X4,X5)=k2_mcart_1(X5)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_mcart_1)).
% 0.19/0.38  fof(t53_mcart_1, axiom, ![X1, X2, X3, X4]:k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_mcart_1)).
% 0.19/0.38  fof(t29_mcart_1, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&![X3, X4, X5]:~(((r2_hidden(X3,X1)|r2_hidden(X4,X1))&X2=k3_mcart_1(X3,X4,X5))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_mcart_1)).
% 0.19/0.38  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 0.19/0.38  fof(t60_mcart_1, axiom, ![X1, X2, X3, X4]:~(((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&X4!=k1_xboole_0)&~(![X5]:(m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))=>X5=k4_mcart_1(k8_mcart_1(X1,X2,X3,X4,X5),k9_mcart_1(X1,X2,X3,X4,X5),k10_mcart_1(X1,X2,X3,X4,X5),k11_mcart_1(X1,X2,X3,X4,X5)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_mcart_1)).
% 0.19/0.38  fof(t31_mcart_1, axiom, ![X1, X2, X3, X4]:k4_mcart_1(X1,X2,X3,X4)=k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_mcart_1)).
% 0.19/0.38  fof(t34_mcart_1, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&![X3, X4, X5, X6]:~(((r2_hidden(X3,X1)|r2_hidden(X4,X1))&X2=k4_mcart_1(X3,X4,X5,X6))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_mcart_1)).
% 0.19/0.38  fof(t26_mcart_1, axiom, ![X1, X2]:~(((X1!=k1_xboole_0&X2!=k1_xboole_0)&~(![X3]:(m1_subset_1(X3,k2_zfmisc_1(X1,X2))=>(X3!=k1_mcart_1(X3)&X3!=k2_mcart_1(X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_mcart_1)).
% 0.19/0.38  fof(t55_mcart_1, axiom, ![X1, X2, X3, X4]:((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&X4!=k1_xboole_0)<=>k4_zfmisc_1(X1,X2,X3,X4)!=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_mcart_1)).
% 0.19/0.38  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.19/0.38  fof(c_0_14, negated_conjecture, ~(![X1, X2, X3, X4]:~(((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&X4!=k1_xboole_0)&~(![X5]:(m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))=>(((X5!=k8_mcart_1(X1,X2,X3,X4,X5)&X5!=k9_mcart_1(X1,X2,X3,X4,X5))&X5!=k10_mcart_1(X1,X2,X3,X4,X5))&X5!=k11_mcart_1(X1,X2,X3,X4,X5))))))), inference(assume_negation,[status(cth)],[t62_mcart_1])).
% 0.19/0.38  fof(c_0_15, plain, ![X9, X10, X11, X12, X13, X14]:(((~r2_hidden(X11,X10)|X11=X9|X10!=k1_tarski(X9))&(X12!=X9|r2_hidden(X12,X10)|X10!=k1_tarski(X9)))&((~r2_hidden(esk1_2(X13,X14),X14)|esk1_2(X13,X14)!=X13|X14=k1_tarski(X13))&(r2_hidden(esk1_2(X13,X14),X14)|esk1_2(X13,X14)=X13|X14=k1_tarski(X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.19/0.38  fof(c_0_16, plain, ![X22, X23]:k2_xboole_0(k1_tarski(X22),X23)!=k1_xboole_0, inference(variable_rename,[status(thm)],[t49_zfmisc_1])).
% 0.19/0.38  fof(c_0_17, plain, ![X7]:k2_xboole_0(X7,X7)=X7, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).
% 0.19/0.38  fof(c_0_18, plain, ![X58, X59, X60, X61, X62]:((((k8_mcart_1(X58,X59,X60,X61,X62)=k1_mcart_1(k1_mcart_1(k1_mcart_1(X62)))|~m1_subset_1(X62,k4_zfmisc_1(X58,X59,X60,X61))|(X58=k1_xboole_0|X59=k1_xboole_0|X60=k1_xboole_0|X61=k1_xboole_0))&(k9_mcart_1(X58,X59,X60,X61,X62)=k2_mcart_1(k1_mcart_1(k1_mcart_1(X62)))|~m1_subset_1(X62,k4_zfmisc_1(X58,X59,X60,X61))|(X58=k1_xboole_0|X59=k1_xboole_0|X60=k1_xboole_0|X61=k1_xboole_0)))&(k10_mcart_1(X58,X59,X60,X61,X62)=k2_mcart_1(k1_mcart_1(X62))|~m1_subset_1(X62,k4_zfmisc_1(X58,X59,X60,X61))|(X58=k1_xboole_0|X59=k1_xboole_0|X60=k1_xboole_0|X61=k1_xboole_0)))&(k11_mcart_1(X58,X59,X60,X61,X62)=k2_mcart_1(X62)|~m1_subset_1(X62,k4_zfmisc_1(X58,X59,X60,X61))|(X58=k1_xboole_0|X59=k1_xboole_0|X60=k1_xboole_0|X61=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_mcart_1])])])])).
% 0.19/0.38  fof(c_0_19, plain, ![X45, X46, X47, X48]:k4_zfmisc_1(X45,X46,X47,X48)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X45,X46),X47),X48), inference(variable_rename,[status(thm)],[t53_mcart_1])).
% 0.19/0.38  fof(c_0_20, negated_conjecture, ((((esk4_0!=k1_xboole_0&esk5_0!=k1_xboole_0)&esk6_0!=k1_xboole_0)&esk7_0!=k1_xboole_0)&(m1_subset_1(esk8_0,k4_zfmisc_1(esk4_0,esk5_0,esk6_0,esk7_0))&(esk8_0=k8_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0)|esk8_0=k9_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0)|esk8_0=k10_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0)|esk8_0=k11_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.19/0.38  fof(c_0_21, plain, ![X30, X32, X33, X34]:((r2_hidden(esk2_1(X30),X30)|X30=k1_xboole_0)&((~r2_hidden(X32,X30)|esk2_1(X30)!=k3_mcart_1(X32,X33,X34)|X30=k1_xboole_0)&(~r2_hidden(X33,X30)|esk2_1(X30)!=k3_mcart_1(X32,X33,X34)|X30=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_mcart_1])])])])])])).
% 0.19/0.38  fof(c_0_22, plain, ![X24, X25, X26]:k3_mcart_1(X24,X25,X26)=k4_tarski(k4_tarski(X24,X25),X26), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 0.19/0.38  cnf(c_0_23, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_24, plain, (k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.38  cnf(c_0_25, plain, (k2_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.38  fof(c_0_26, plain, ![X53, X54, X55, X56, X57]:(X53=k1_xboole_0|X54=k1_xboole_0|X55=k1_xboole_0|X56=k1_xboole_0|(~m1_subset_1(X57,k4_zfmisc_1(X53,X54,X55,X56))|X57=k4_mcart_1(k8_mcart_1(X53,X54,X55,X56,X57),k9_mcart_1(X53,X54,X55,X56,X57),k10_mcart_1(X53,X54,X55,X56,X57),k11_mcart_1(X53,X54,X55,X56,X57)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_mcart_1])])])).
% 0.19/0.38  fof(c_0_27, plain, ![X35, X36, X37, X38]:k4_mcart_1(X35,X36,X37,X38)=k4_tarski(k4_tarski(k4_tarski(X35,X36),X37),X38), inference(variable_rename,[status(thm)],[t31_mcart_1])).
% 0.19/0.38  cnf(c_0_28, plain, (k11_mcart_1(X1,X2,X3,X4,X5)=k2_mcart_1(X5)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|~m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.38  cnf(c_0_29, plain, (k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.38  cnf(c_0_30, negated_conjecture, (m1_subset_1(esk8_0,k4_zfmisc_1(esk4_0,esk5_0,esk6_0,esk7_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.38  fof(c_0_31, plain, ![X39, X41, X42, X43, X44]:((r2_hidden(esk3_1(X39),X39)|X39=k1_xboole_0)&((~r2_hidden(X41,X39)|esk3_1(X39)!=k4_mcart_1(X41,X42,X43,X44)|X39=k1_xboole_0)&(~r2_hidden(X42,X39)|esk3_1(X39)!=k4_mcart_1(X41,X42,X43,X44)|X39=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_mcart_1])])])])])])).
% 0.19/0.38  cnf(c_0_32, plain, (X2=k1_xboole_0|~r2_hidden(X1,X2)|esk2_1(X2)!=k3_mcart_1(X3,X1,X4)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.38  cnf(c_0_33, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.38  cnf(c_0_34, plain, (X1=X2|~r2_hidden(X1,k1_tarski(X2))), inference(er,[status(thm)],[c_0_23])).
% 0.19/0.38  cnf(c_0_35, plain, (r2_hidden(esk2_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.38  cnf(c_0_36, plain, (k1_tarski(X1)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.19/0.38  cnf(c_0_37, plain, (X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5=k4_mcart_1(k8_mcart_1(X1,X2,X3,X4,X5),k9_mcart_1(X1,X2,X3,X4,X5),k10_mcart_1(X1,X2,X3,X4,X5),k11_mcart_1(X1,X2,X3,X4,X5))|~m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.38  cnf(c_0_38, plain, (k4_mcart_1(X1,X2,X3,X4)=k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.38  cnf(c_0_39, plain, (X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k11_mcart_1(X1,X2,X3,X4,X5)=k2_mcart_1(X5)|~m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))), inference(rw,[status(thm)],[c_0_28, c_0_29])).
% 0.19/0.38  cnf(c_0_40, negated_conjecture, (m1_subset_1(esk8_0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0),esk7_0))), inference(rw,[status(thm)],[c_0_30, c_0_29])).
% 0.19/0.38  cnf(c_0_41, negated_conjecture, (esk7_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.38  cnf(c_0_42, negated_conjecture, (esk6_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.38  cnf(c_0_43, negated_conjecture, (esk5_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.38  cnf(c_0_44, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.38  cnf(c_0_45, plain, (X2=k1_xboole_0|~r2_hidden(X1,X2)|esk3_1(X2)!=k4_mcart_1(X3,X1,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.38  cnf(c_0_46, plain, (r2_hidden(esk3_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.38  cnf(c_0_47, plain, (X2=k1_xboole_0|esk2_1(X2)!=k4_tarski(k4_tarski(X3,X1),X4)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_32, c_0_33])).
% 0.19/0.38  cnf(c_0_48, plain, (esk2_1(k1_tarski(X1))=X1), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36])).
% 0.19/0.38  cnf(c_0_49, plain, (X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|X5=k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(X1,X2,X3,X4,X5),k9_mcart_1(X1,X2,X3,X4,X5)),k10_mcart_1(X1,X2,X3,X4,X5)),k11_mcart_1(X1,X2,X3,X4,X5))|~m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_38]), c_0_29])).
% 0.19/0.38  cnf(c_0_50, negated_conjecture, (k11_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0)=k2_mcart_1(esk8_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41]), c_0_42]), c_0_43]), c_0_44])).
% 0.19/0.38  cnf(c_0_51, plain, (X2=k1_xboole_0|~r2_hidden(X1,X2)|esk3_1(X2)!=k4_mcart_1(X1,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.38  cnf(c_0_52, plain, (X2=k1_xboole_0|esk3_1(X2)!=k4_tarski(k4_tarski(k4_tarski(X3,X1),X4),X5)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_45, c_0_38])).
% 0.19/0.38  cnf(c_0_53, plain, (esk3_1(k1_tarski(X1))=X1), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_46]), c_0_36])).
% 0.19/0.38  cnf(c_0_54, plain, (~r2_hidden(X1,k1_tarski(k4_tarski(k4_tarski(X2,X1),X3)))), inference(er,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_36])])).
% 0.19/0.38  cnf(c_0_55, negated_conjecture, (k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k9_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0)),k10_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0)),k2_mcart_1(esk8_0))=esk8_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_40]), c_0_50]), c_0_41]), c_0_42]), c_0_43]), c_0_44])).
% 0.19/0.38  cnf(c_0_56, negated_conjecture, (esk8_0=k8_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0)|esk8_0=k9_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0)|esk8_0=k10_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0)|esk8_0=k11_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.38  cnf(c_0_57, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_58, plain, (X2=k1_xboole_0|esk3_1(X2)!=k4_tarski(k4_tarski(k4_tarski(X1,X3),X4),X5)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_51, c_0_38])).
% 0.19/0.38  cnf(c_0_59, plain, (~r2_hidden(X1,k1_tarski(k4_tarski(k4_tarski(k4_tarski(X2,X1),X3),X4)))), inference(er,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_36])])).
% 0.19/0.38  cnf(c_0_60, negated_conjecture, (~r2_hidden(k10_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k1_tarski(esk8_0))), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.19/0.38  cnf(c_0_61, negated_conjecture, (k10_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0)=esk8_0|k9_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0)=esk8_0|k8_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0)=esk8_0|k2_mcart_1(esk8_0)=esk8_0), inference(spm,[status(thm)],[c_0_56, c_0_50])).
% 0.19/0.38  cnf(c_0_62, plain, (r2_hidden(X1,k1_tarski(X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_57])])).
% 0.19/0.38  fof(c_0_63, plain, ![X27, X28, X29]:((X29!=k1_mcart_1(X29)|~m1_subset_1(X29,k2_zfmisc_1(X27,X28))|(X27=k1_xboole_0|X28=k1_xboole_0))&(X29!=k2_mcart_1(X29)|~m1_subset_1(X29,k2_zfmisc_1(X27,X28))|(X27=k1_xboole_0|X28=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_mcart_1])])])])).
% 0.19/0.38  cnf(c_0_64, plain, (~r2_hidden(X1,k1_tarski(k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4)))), inference(er,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_53]), c_0_36])])).
% 0.19/0.38  cnf(c_0_65, negated_conjecture, (~r2_hidden(k9_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k1_tarski(esk8_0))), inference(spm,[status(thm)],[c_0_59, c_0_55])).
% 0.19/0.38  cnf(c_0_66, negated_conjecture, (k8_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0)=esk8_0|k9_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0)=esk8_0|k2_mcart_1(esk8_0)=esk8_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_62])])).
% 0.19/0.38  fof(c_0_67, plain, ![X49, X50, X51, X52]:((X49=k1_xboole_0|X50=k1_xboole_0|X51=k1_xboole_0|X52=k1_xboole_0|k4_zfmisc_1(X49,X50,X51,X52)!=k1_xboole_0)&((((X49!=k1_xboole_0|k4_zfmisc_1(X49,X50,X51,X52)=k1_xboole_0)&(X50!=k1_xboole_0|k4_zfmisc_1(X49,X50,X51,X52)=k1_xboole_0))&(X51!=k1_xboole_0|k4_zfmisc_1(X49,X50,X51,X52)=k1_xboole_0))&(X52!=k1_xboole_0|k4_zfmisc_1(X49,X50,X51,X52)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_mcart_1])])])).
% 0.19/0.38  cnf(c_0_68, plain, (X2=k1_xboole_0|X3=k1_xboole_0|X1!=k2_mcart_1(X1)|~m1_subset_1(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.19/0.38  cnf(c_0_69, negated_conjecture, (~r2_hidden(k8_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k1_tarski(esk8_0))), inference(spm,[status(thm)],[c_0_64, c_0_55])).
% 0.19/0.38  cnf(c_0_70, negated_conjecture, (k8_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0)=esk8_0|k2_mcart_1(esk8_0)=esk8_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_62])])).
% 0.19/0.38  fof(c_0_71, plain, ![X18, X19]:((k2_zfmisc_1(X18,X19)!=k1_xboole_0|(X18=k1_xboole_0|X19=k1_xboole_0))&((X18!=k1_xboole_0|k2_zfmisc_1(X18,X19)=k1_xboole_0)&(X19!=k1_xboole_0|k2_zfmisc_1(X18,X19)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.19/0.38  cnf(c_0_72, plain, (X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|k4_zfmisc_1(X1,X2,X3,X4)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.19/0.38  cnf(c_0_73, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0)=k1_xboole_0|k2_mcart_1(esk8_0)!=esk8_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_40]), c_0_41])).
% 0.19/0.38  cnf(c_0_74, negated_conjecture, (k2_mcart_1(esk8_0)=esk8_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_62])])).
% 0.19/0.38  cnf(c_0_75, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.19/0.38  cnf(c_0_76, plain, (X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_72, c_0_29])).
% 0.19/0.38  cnf(c_0_77, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_73, c_0_74])])).
% 0.19/0.38  cnf(c_0_78, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_75])).
% 0.19/0.38  cnf(c_0_79, negated_conjecture, (X1=k1_xboole_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_78])]), c_0_42]), c_0_43]), c_0_44])).
% 0.19/0.38  cnf(c_0_80, plain, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_79])]), ['proof']).
% 0.19/0.38  # SZS output end CNFRefutation
% 0.19/0.38  # Proof object total steps             : 81
% 0.19/0.38  # Proof object clause steps            : 52
% 0.19/0.38  # Proof object formula steps           : 29
% 0.19/0.38  # Proof object conjectures             : 22
% 0.19/0.38  # Proof object clause conjectures      : 19
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 23
% 0.19/0.38  # Proof object initial formulas used   : 14
% 0.19/0.38  # Proof object generating inferences   : 17
% 0.19/0.38  # Proof object simplifying inferences  : 45
% 0.19/0.38  # Training examples: 0 positive, 0 negative
% 0.19/0.38  # Parsed axioms                        : 17
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 39
% 0.19/0.38  # Removed in clause preprocessing      : 3
% 0.19/0.38  # Initial clauses in saturation        : 36
% 0.19/0.38  # Processed clauses                    : 108
% 0.19/0.38  # ...of these trivial                  : 0
% 0.19/0.38  # ...subsumed                          : 5
% 0.19/0.38  # ...remaining for further processing  : 103
% 0.19/0.38  # Other redundant clauses eliminated   : 16
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 4
% 0.19/0.38  # Backward-rewritten                   : 56
% 0.19/0.38  # Generated clauses                    : 104
% 0.19/0.38  # ...of the previous two non-trivial   : 83
% 0.19/0.38  # Contextual simplify-reflections      : 0
% 0.19/0.38  # Paramodulations                      : 87
% 0.19/0.38  # Factorizations                       : 2
% 0.19/0.38  # Equation resolutions                 : 16
% 0.19/0.38  # Propositional unsat checks           : 0
% 0.19/0.38  #    Propositional check models        : 0
% 0.19/0.38  #    Propositional check unsatisfiable : 0
% 0.19/0.38  #    Propositional clauses             : 0
% 0.19/0.38  #    Propositional clauses after purity: 0
% 0.19/0.38  #    Propositional unsat core size     : 0
% 0.19/0.38  #    Propositional preprocessing time  : 0.000
% 0.19/0.38  #    Propositional encoding time       : 0.000
% 0.19/0.38  #    Propositional solver time         : 0.000
% 0.19/0.38  #    Success case prop preproc time    : 0.000
% 0.19/0.38  #    Success case prop encoding time   : 0.000
% 0.19/0.38  #    Success case prop solver time     : 0.000
% 0.19/0.38  # Current number of processed clauses  : 3
% 0.19/0.38  #    Positive orientable unit clauses  : 1
% 0.19/0.38  #    Positive unorientable unit clauses: 1
% 0.19/0.38  #    Negative unit clauses             : 1
% 0.19/0.38  #    Non-unit-clauses                  : 0
% 0.19/0.38  # Current number of unprocessed clauses: 34
% 0.19/0.38  # ...number of literals in the above   : 95
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 95
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 266
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 62
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 6
% 0.19/0.38  # Unit Clause-clause subsumption calls : 21
% 0.19/0.38  # Rewrite failures with RHS unbound    : 5
% 0.19/0.38  # BW rewrite match attempts            : 78
% 0.19/0.38  # BW rewrite match successes           : 74
% 0.19/0.38  # Condensation attempts                : 0
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 4598
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.034 s
% 0.19/0.38  # System time              : 0.005 s
% 0.19/0.38  # Total time               : 0.039 s
% 0.19/0.38  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
