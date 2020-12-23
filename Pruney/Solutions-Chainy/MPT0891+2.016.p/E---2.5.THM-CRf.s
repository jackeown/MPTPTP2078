%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:59:54 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 418 expanded)
%              Number of clauses        :   48 ( 169 expanded)
%              Number of leaves         :   11 ( 102 expanded)
%              Depth                    :   12
%              Number of atoms          :  209 (1710 expanded)
%              Number of equality atoms :  160 (1391 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   15 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t152_zfmisc_1,axiom,(
    ! [X1,X2] : ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(t51_mcart_1,conjecture,(
    ! [X1,X2,X3] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & ~ ! [X4] :
              ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
             => ( X4 != k5_mcart_1(X1,X2,X3,X4)
                & X4 != k6_mcart_1(X1,X2,X3,X4)
                & X4 != k7_mcart_1(X1,X2,X3,X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_mcart_1)).

fof(t29_mcart_1,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] :
            ~ ( r2_hidden(X2,X1)
              & ! [X3,X4,X5] :
                  ~ ( ( r2_hidden(X3,X1)
                      | r2_hidden(X4,X1) )
                    & X2 = k3_mcart_1(X3,X4,X5) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(t50_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & ~ ! [X4] :
              ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
             => ( k5_mcart_1(X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(X4))
                & k6_mcart_1(X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
                & k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(t20_mcart_1,axiom,(
    ! [X1] :
      ( ? [X2,X3] : X1 = k4_tarski(X2,X3)
     => ( X1 != k1_mcart_1(X1)
        & X1 != k2_mcart_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

fof(t48_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & ~ ! [X4] :
              ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
             => X4 = k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_mcart_1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(t7_mcart_1,axiom,(
    ! [X1,X2] :
      ( k1_mcart_1(k4_tarski(X1,X2)) = X1
      & k2_mcart_1(k4_tarski(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(c_0_11,plain,(
    ! [X13,X14] :
      ( ( k2_zfmisc_1(X13,X14) != k1_xboole_0
        | X13 = k1_xboole_0
        | X14 = k1_xboole_0 )
      & ( X13 != k1_xboole_0
        | k2_zfmisc_1(X13,X14) = k1_xboole_0 )
      & ( X14 != k1_xboole_0
        | k2_zfmisc_1(X13,X14) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_12,plain,(
    ! [X15,X16] : ~ r2_hidden(X15,k2_zfmisc_1(X15,X16)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).

cnf(c_0_13,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( X1 != k1_xboole_0
          & X2 != k1_xboole_0
          & X3 != k1_xboole_0
          & ~ ! [X4] :
                ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
               => ( X4 != k5_mcart_1(X1,X2,X3,X4)
                  & X4 != k6_mcart_1(X1,X2,X3,X4)
                  & X4 != k7_mcart_1(X1,X2,X3,X4) ) ) ) ),
    inference(assume_negation,[status(cth)],[t51_mcart_1])).

cnf(c_0_15,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_13])).

fof(c_0_17,plain,(
    ! [X26,X28,X29,X30] :
      ( ( r2_hidden(esk2_1(X26),X26)
        | X26 = k1_xboole_0 )
      & ( ~ r2_hidden(X28,X26)
        | esk2_1(X26) != k3_mcart_1(X28,X29,X30)
        | X26 = k1_xboole_0 )
      & ( ~ r2_hidden(X29,X26)
        | esk2_1(X26) != k3_mcart_1(X28,X29,X30)
        | X26 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_mcart_1])])])])])])).

fof(c_0_18,plain,(
    ! [X6,X7,X8,X9,X10,X11] :
      ( ( ~ r2_hidden(X8,X7)
        | X8 = X6
        | X7 != k1_tarski(X6) )
      & ( X9 != X6
        | r2_hidden(X9,X7)
        | X7 != k1_tarski(X6) )
      & ( ~ r2_hidden(esk1_2(X10,X11),X11)
        | esk1_2(X10,X11) != X10
        | X11 = k1_tarski(X10) )
      & ( r2_hidden(esk1_2(X10,X11),X11)
        | esk1_2(X10,X11) = X10
        | X11 = k1_tarski(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_19,plain,(
    ! [X35,X36,X37,X38] :
      ( ( k5_mcart_1(X35,X36,X37,X38) = k1_mcart_1(k1_mcart_1(X38))
        | ~ m1_subset_1(X38,k3_zfmisc_1(X35,X36,X37))
        | X35 = k1_xboole_0
        | X36 = k1_xboole_0
        | X37 = k1_xboole_0 )
      & ( k6_mcart_1(X35,X36,X37,X38) = k2_mcart_1(k1_mcart_1(X38))
        | ~ m1_subset_1(X38,k3_zfmisc_1(X35,X36,X37))
        | X35 = k1_xboole_0
        | X36 = k1_xboole_0
        | X37 = k1_xboole_0 )
      & ( k7_mcart_1(X35,X36,X37,X38) = k2_mcart_1(X38)
        | ~ m1_subset_1(X38,k3_zfmisc_1(X35,X36,X37))
        | X35 = k1_xboole_0
        | X36 = k1_xboole_0
        | X37 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_mcart_1])])])])).

fof(c_0_20,plain,(
    ! [X20,X21,X22] : k3_zfmisc_1(X20,X21,X22) = k2_zfmisc_1(k2_zfmisc_1(X20,X21),X22) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_21,negated_conjecture,
    ( esk3_0 != k1_xboole_0
    & esk4_0 != k1_xboole_0
    & esk5_0 != k1_xboole_0
    & m1_subset_1(esk6_0,k3_zfmisc_1(esk3_0,esk4_0,esk5_0))
    & ( esk6_0 = k5_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)
      | esk6_0 = k6_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)
      | esk6_0 = k7_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

cnf(c_0_22,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_23,plain,
    ( r2_hidden(esk2_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk6_0,k3_zfmisc_1(esk3_0,esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_28,plain,(
    ! [X23,X24,X25] :
      ( ( X23 != k1_mcart_1(X23)
        | X23 != k4_tarski(X24,X25) )
      & ( X23 != k2_mcart_1(X23)
        | X23 != k4_tarski(X24,X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_mcart_1])])])])).

fof(c_0_29,plain,(
    ! [X31,X32,X33,X34] :
      ( X31 = k1_xboole_0
      | X32 = k1_xboole_0
      | X33 = k1_xboole_0
      | ~ m1_subset_1(X34,k3_zfmisc_1(X31,X32,X33))
      | X34 = k3_mcart_1(k5_mcart_1(X31,X32,X33,X34),k6_mcart_1(X31,X32,X33,X34),k7_mcart_1(X31,X32,X33,X34)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_mcart_1])])])).

fof(c_0_30,plain,(
    ! [X17,X18,X19] : k3_mcart_1(X17,X18,X19) = k4_tarski(k4_tarski(X17,X18),X19) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

cnf(c_0_31,plain,
    ( k5_mcart_1(X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(X4))
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_32,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_33,plain,
    ( r2_hidden(esk2_1(X1),X1)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,k1_tarski(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_24])])).

cnf(c_0_35,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4)
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(esk6_0,k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0)) ),
    inference(rw,[status(thm)],[c_0_27,c_0_26])).

cnf(c_0_37,negated_conjecture,
    ( esk5_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_38,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_39,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_40,plain,
    ( X1 != k2_mcart_1(X1)
    | X1 != k4_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_41,plain,(
    ! [X39,X40] :
      ( k1_mcart_1(k4_tarski(X39,X40)) = X39
      & k2_mcart_1(k4_tarski(X39,X40)) = X40 ) ),
    inference(variable_rename,[status(thm)],[t7_mcart_1])).

cnf(c_0_42,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4))
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_43,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_44,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k5_mcart_1(X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(X4))
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_31,c_0_26])).

cnf(c_0_45,plain,
    ( X2 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | esk2_1(X2) != k3_mcart_1(X3,X1,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_46,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k1_tarski(X2)) ),
    inference(er,[status(thm)],[c_0_32])).

cnf(c_0_47,plain,
    ( r2_hidden(esk2_1(k1_tarski(X1)),k1_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_48,negated_conjecture,
    ( esk6_0 = k5_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)
    | esk6_0 = k6_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)
    | esk6_0 = k7_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_49,negated_conjecture,
    ( k7_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0) = k2_mcart_1(esk6_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37]),c_0_38]),c_0_39])).

cnf(c_0_50,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) != k4_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_40])).

cnf(c_0_51,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_52,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | X4 = k4_tarski(k4_tarski(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4)),k7_mcart_1(X1,X2,X3,X4))
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_43]),c_0_26])).

cnf(c_0_53,negated_conjecture,
    ( k5_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0) = k1_mcart_1(k1_mcart_1(esk6_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_36]),c_0_37]),c_0_38]),c_0_39])).

cnf(c_0_54,plain,
    ( X2 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | esk2_1(X2) != k3_mcart_1(X1,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_55,plain,
    ( X2 = k1_xboole_0
    | esk2_1(X2) != k4_tarski(k4_tarski(X3,X1),X4)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_45,c_0_43])).

cnf(c_0_56,plain,
    ( esk2_1(k1_tarski(X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_57,negated_conjecture,
    ( k6_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0) = esk6_0
    | k5_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0) = esk6_0
    | k2_mcart_1(esk6_0) = esk6_0 ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_58,plain,
    ( k4_tarski(X1,X2) != X2 ),
    inference(rw,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_59,negated_conjecture,
    ( k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(esk6_0)),k6_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)),k2_mcart_1(esk6_0)) = esk6_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_36]),c_0_53]),c_0_49]),c_0_37]),c_0_38]),c_0_39])).

cnf(c_0_60,plain,
    ( X2 = k1_xboole_0
    | esk2_1(X2) != k4_tarski(k4_tarski(X1,X3),X4)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_54,c_0_43])).

cnf(c_0_61,plain,
    ( k1_tarski(k4_tarski(k4_tarski(X1,X2),X3)) = k1_xboole_0
    | ~ r2_hidden(X2,k1_tarski(k4_tarski(k4_tarski(X1,X2),X3))) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56])])).

cnf(c_0_62,negated_conjecture,
    ( k6_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0) = esk6_0
    | k1_mcart_1(k1_mcart_1(esk6_0)) = esk6_0
    | k2_mcart_1(esk6_0) = esk6_0 ),
    inference(rw,[status(thm)],[c_0_57,c_0_53])).

cnf(c_0_63,negated_conjecture,
    ( k2_mcart_1(esk6_0) != esk6_0 ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_64,plain,
    ( k1_tarski(k4_tarski(k4_tarski(X1,X2),X3)) = k1_xboole_0
    | ~ r2_hidden(X1,k1_tarski(k4_tarski(k4_tarski(X1,X2),X3))) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_56])])).

cnf(c_0_65,negated_conjecture,
    ( k1_tarski(esk6_0) = k1_xboole_0
    | ~ r2_hidden(k6_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0),k1_tarski(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_59])).

cnf(c_0_66,negated_conjecture,
    ( k6_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0) = esk6_0
    | k1_mcart_1(k1_mcart_1(esk6_0)) = esk6_0 ),
    inference(sr,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_67,negated_conjecture,
    ( k1_tarski(esk6_0) = k1_xboole_0
    | ~ r2_hidden(k1_mcart_1(k1_mcart_1(esk6_0)),k1_tarski(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_59])).

cnf(c_0_68,negated_conjecture,
    ( k1_mcart_1(k1_mcart_1(esk6_0)) = esk6_0
    | k1_tarski(esk6_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_34])])).

cnf(c_0_69,negated_conjecture,
    ( k1_tarski(esk6_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_34])])).

cnf(c_0_70,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_69]),c_0_22]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 20:29:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  # Version: 2.5pre002
% 0.15/0.35  # No SInE strategy applied
% 0.15/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.46  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.21/0.46  # and selection function SelectNegativeLiterals.
% 0.21/0.46  #
% 0.21/0.46  # Preprocessing time       : 0.028 s
% 0.21/0.46  # Presaturation interreduction done
% 0.21/0.46  
% 0.21/0.46  # Proof found!
% 0.21/0.46  # SZS status Theorem
% 0.21/0.46  # SZS output start CNFRefutation
% 0.21/0.46  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.21/0.46  fof(t152_zfmisc_1, axiom, ![X1, X2]:~(r2_hidden(X1,k2_zfmisc_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 0.21/0.46  fof(t51_mcart_1, conjecture, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>((X4!=k5_mcart_1(X1,X2,X3,X4)&X4!=k6_mcart_1(X1,X2,X3,X4))&X4!=k7_mcart_1(X1,X2,X3,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_mcart_1)).
% 0.21/0.46  fof(t29_mcart_1, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&![X3, X4, X5]:~(((r2_hidden(X3,X1)|r2_hidden(X4,X1))&X2=k3_mcart_1(X3,X4,X5))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_mcart_1)).
% 0.21/0.46  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 0.21/0.46  fof(t50_mcart_1, axiom, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>((k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))&k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4)))&k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_mcart_1)).
% 0.21/0.46  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 0.21/0.46  fof(t20_mcart_1, axiom, ![X1]:(?[X2, X3]:X1=k4_tarski(X2,X3)=>(X1!=k1_mcart_1(X1)&X1!=k2_mcart_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_mcart_1)).
% 0.21/0.46  fof(t48_mcart_1, axiom, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>X4=k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_mcart_1)).
% 0.21/0.46  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 0.21/0.46  fof(t7_mcart_1, axiom, ![X1, X2]:(k1_mcart_1(k4_tarski(X1,X2))=X1&k2_mcart_1(k4_tarski(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 0.21/0.46  fof(c_0_11, plain, ![X13, X14]:((k2_zfmisc_1(X13,X14)!=k1_xboole_0|(X13=k1_xboole_0|X14=k1_xboole_0))&((X13!=k1_xboole_0|k2_zfmisc_1(X13,X14)=k1_xboole_0)&(X14!=k1_xboole_0|k2_zfmisc_1(X13,X14)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.21/0.46  fof(c_0_12, plain, ![X15, X16]:~r2_hidden(X15,k2_zfmisc_1(X15,X16)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).
% 0.21/0.46  cnf(c_0_13, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.46  fof(c_0_14, negated_conjecture, ~(![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>((X4!=k5_mcart_1(X1,X2,X3,X4)&X4!=k6_mcart_1(X1,X2,X3,X4))&X4!=k7_mcart_1(X1,X2,X3,X4))))))), inference(assume_negation,[status(cth)],[t51_mcart_1])).
% 0.21/0.46  cnf(c_0_15, plain, (~r2_hidden(X1,k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.46  cnf(c_0_16, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_13])).
% 0.21/0.46  fof(c_0_17, plain, ![X26, X28, X29, X30]:((r2_hidden(esk2_1(X26),X26)|X26=k1_xboole_0)&((~r2_hidden(X28,X26)|esk2_1(X26)!=k3_mcart_1(X28,X29,X30)|X26=k1_xboole_0)&(~r2_hidden(X29,X26)|esk2_1(X26)!=k3_mcart_1(X28,X29,X30)|X26=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_mcart_1])])])])])])).
% 0.21/0.46  fof(c_0_18, plain, ![X6, X7, X8, X9, X10, X11]:(((~r2_hidden(X8,X7)|X8=X6|X7!=k1_tarski(X6))&(X9!=X6|r2_hidden(X9,X7)|X7!=k1_tarski(X6)))&((~r2_hidden(esk1_2(X10,X11),X11)|esk1_2(X10,X11)!=X10|X11=k1_tarski(X10))&(r2_hidden(esk1_2(X10,X11),X11)|esk1_2(X10,X11)=X10|X11=k1_tarski(X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.21/0.46  fof(c_0_19, plain, ![X35, X36, X37, X38]:(((k5_mcart_1(X35,X36,X37,X38)=k1_mcart_1(k1_mcart_1(X38))|~m1_subset_1(X38,k3_zfmisc_1(X35,X36,X37))|(X35=k1_xboole_0|X36=k1_xboole_0|X37=k1_xboole_0))&(k6_mcart_1(X35,X36,X37,X38)=k2_mcart_1(k1_mcart_1(X38))|~m1_subset_1(X38,k3_zfmisc_1(X35,X36,X37))|(X35=k1_xboole_0|X36=k1_xboole_0|X37=k1_xboole_0)))&(k7_mcart_1(X35,X36,X37,X38)=k2_mcart_1(X38)|~m1_subset_1(X38,k3_zfmisc_1(X35,X36,X37))|(X35=k1_xboole_0|X36=k1_xboole_0|X37=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_mcart_1])])])])).
% 0.21/0.46  fof(c_0_20, plain, ![X20, X21, X22]:k3_zfmisc_1(X20,X21,X22)=k2_zfmisc_1(k2_zfmisc_1(X20,X21),X22), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 0.21/0.46  fof(c_0_21, negated_conjecture, (((esk3_0!=k1_xboole_0&esk4_0!=k1_xboole_0)&esk5_0!=k1_xboole_0)&(m1_subset_1(esk6_0,k3_zfmisc_1(esk3_0,esk4_0,esk5_0))&(esk6_0=k5_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)|esk6_0=k6_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)|esk6_0=k7_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.21/0.46  cnf(c_0_22, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.21/0.46  cnf(c_0_23, plain, (r2_hidden(esk2_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.46  cnf(c_0_24, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.46  cnf(c_0_25, plain, (k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.46  cnf(c_0_26, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.46  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk6_0,k3_zfmisc_1(esk3_0,esk4_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.46  fof(c_0_28, plain, ![X23, X24, X25]:((X23!=k1_mcart_1(X23)|X23!=k4_tarski(X24,X25))&(X23!=k2_mcart_1(X23)|X23!=k4_tarski(X24,X25))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_mcart_1])])])])).
% 0.21/0.46  fof(c_0_29, plain, ![X31, X32, X33, X34]:(X31=k1_xboole_0|X32=k1_xboole_0|X33=k1_xboole_0|(~m1_subset_1(X34,k3_zfmisc_1(X31,X32,X33))|X34=k3_mcart_1(k5_mcart_1(X31,X32,X33,X34),k6_mcart_1(X31,X32,X33,X34),k7_mcart_1(X31,X32,X33,X34)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_mcart_1])])])).
% 0.21/0.46  fof(c_0_30, plain, ![X17, X18, X19]:k3_mcart_1(X17,X18,X19)=k4_tarski(k4_tarski(X17,X18),X19), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 0.21/0.46  cnf(c_0_31, plain, (k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.46  cnf(c_0_32, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.46  cnf(c_0_33, plain, (r2_hidden(esk2_1(X1),X1)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.21/0.46  cnf(c_0_34, plain, (r2_hidden(X1,k1_tarski(X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_24])])).
% 0.21/0.46  cnf(c_0_35, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_25, c_0_26])).
% 0.21/0.46  cnf(c_0_36, negated_conjecture, (m1_subset_1(esk6_0,k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0))), inference(rw,[status(thm)],[c_0_27, c_0_26])).
% 0.21/0.46  cnf(c_0_37, negated_conjecture, (esk5_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.46  cnf(c_0_38, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.46  cnf(c_0_39, negated_conjecture, (esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.46  cnf(c_0_40, plain, (X1!=k2_mcart_1(X1)|X1!=k4_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.21/0.46  fof(c_0_41, plain, ![X39, X40]:(k1_mcart_1(k4_tarski(X39,X40))=X39&k2_mcart_1(k4_tarski(X39,X40))=X40), inference(variable_rename,[status(thm)],[t7_mcart_1])).
% 0.21/0.46  cnf(c_0_42, plain, (X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4))|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.21/0.46  cnf(c_0_43, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.21/0.46  cnf(c_0_44, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_31, c_0_26])).
% 0.21/0.46  cnf(c_0_45, plain, (X2=k1_xboole_0|~r2_hidden(X1,X2)|esk2_1(X2)!=k3_mcart_1(X3,X1,X4)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.46  cnf(c_0_46, plain, (X1=X2|~r2_hidden(X1,k1_tarski(X2))), inference(er,[status(thm)],[c_0_32])).
% 0.21/0.46  cnf(c_0_47, plain, (r2_hidden(esk2_1(k1_tarski(X1)),k1_tarski(X1))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.21/0.46  cnf(c_0_48, negated_conjecture, (esk6_0=k5_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)|esk6_0=k6_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)|esk6_0=k7_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.46  cnf(c_0_49, negated_conjecture, (k7_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)=k2_mcart_1(esk6_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37]), c_0_38]), c_0_39])).
% 0.21/0.46  cnf(c_0_50, plain, (k2_mcart_1(k4_tarski(X1,X2))!=k4_tarski(X1,X2)), inference(er,[status(thm)],[c_0_40])).
% 0.21/0.46  cnf(c_0_51, plain, (k2_mcart_1(k4_tarski(X1,X2))=X2), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.21/0.46  cnf(c_0_52, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|X4=k4_tarski(k4_tarski(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4)),k7_mcart_1(X1,X2,X3,X4))|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_43]), c_0_26])).
% 0.21/0.46  cnf(c_0_53, negated_conjecture, (k5_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)=k1_mcart_1(k1_mcart_1(esk6_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_36]), c_0_37]), c_0_38]), c_0_39])).
% 0.21/0.46  cnf(c_0_54, plain, (X2=k1_xboole_0|~r2_hidden(X1,X2)|esk2_1(X2)!=k3_mcart_1(X1,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.46  cnf(c_0_55, plain, (X2=k1_xboole_0|esk2_1(X2)!=k4_tarski(k4_tarski(X3,X1),X4)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_45, c_0_43])).
% 0.21/0.46  cnf(c_0_56, plain, (esk2_1(k1_tarski(X1))=X1), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.21/0.46  cnf(c_0_57, negated_conjecture, (k6_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)=esk6_0|k5_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)=esk6_0|k2_mcart_1(esk6_0)=esk6_0), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.21/0.46  cnf(c_0_58, plain, (k4_tarski(X1,X2)!=X2), inference(rw,[status(thm)],[c_0_50, c_0_51])).
% 0.21/0.46  cnf(c_0_59, negated_conjecture, (k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(esk6_0)),k6_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)),k2_mcart_1(esk6_0))=esk6_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_36]), c_0_53]), c_0_49]), c_0_37]), c_0_38]), c_0_39])).
% 0.21/0.46  cnf(c_0_60, plain, (X2=k1_xboole_0|esk2_1(X2)!=k4_tarski(k4_tarski(X1,X3),X4)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_54, c_0_43])).
% 0.21/0.46  cnf(c_0_61, plain, (k1_tarski(k4_tarski(k4_tarski(X1,X2),X3))=k1_xboole_0|~r2_hidden(X2,k1_tarski(k4_tarski(k4_tarski(X1,X2),X3)))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56])])).
% 0.21/0.46  cnf(c_0_62, negated_conjecture, (k6_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)=esk6_0|k1_mcart_1(k1_mcart_1(esk6_0))=esk6_0|k2_mcart_1(esk6_0)=esk6_0), inference(rw,[status(thm)],[c_0_57, c_0_53])).
% 0.21/0.46  cnf(c_0_63, negated_conjecture, (k2_mcart_1(esk6_0)!=esk6_0), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.21/0.46  cnf(c_0_64, plain, (k1_tarski(k4_tarski(k4_tarski(X1,X2),X3))=k1_xboole_0|~r2_hidden(X1,k1_tarski(k4_tarski(k4_tarski(X1,X2),X3)))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_56])])).
% 0.21/0.46  cnf(c_0_65, negated_conjecture, (k1_tarski(esk6_0)=k1_xboole_0|~r2_hidden(k6_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0),k1_tarski(esk6_0))), inference(spm,[status(thm)],[c_0_61, c_0_59])).
% 0.21/0.46  cnf(c_0_66, negated_conjecture, (k6_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0)=esk6_0|k1_mcart_1(k1_mcart_1(esk6_0))=esk6_0), inference(sr,[status(thm)],[c_0_62, c_0_63])).
% 0.21/0.46  cnf(c_0_67, negated_conjecture, (k1_tarski(esk6_0)=k1_xboole_0|~r2_hidden(k1_mcart_1(k1_mcart_1(esk6_0)),k1_tarski(esk6_0))), inference(spm,[status(thm)],[c_0_64, c_0_59])).
% 0.21/0.46  cnf(c_0_68, negated_conjecture, (k1_mcart_1(k1_mcart_1(esk6_0))=esk6_0|k1_tarski(esk6_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_34])])).
% 0.21/0.46  cnf(c_0_69, negated_conjecture, (k1_tarski(esk6_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_34])])).
% 0.21/0.46  cnf(c_0_70, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_69]), c_0_22]), ['proof']).
% 0.21/0.46  # SZS output end CNFRefutation
% 0.21/0.46  # Proof object total steps             : 71
% 0.21/0.46  # Proof object clause steps            : 48
% 0.21/0.46  # Proof object formula steps           : 23
% 0.21/0.46  # Proof object conjectures             : 21
% 0.21/0.46  # Proof object clause conjectures      : 18
% 0.21/0.46  # Proof object formula conjectures     : 3
% 0.21/0.46  # Proof object initial clauses used    : 19
% 0.21/0.46  # Proof object initial formulas used   : 11
% 0.21/0.46  # Proof object generating inferences   : 16
% 0.21/0.46  # Proof object simplifying inferences  : 33
% 0.21/0.46  # Training examples: 0 positive, 0 negative
% 0.21/0.46  # Parsed axioms                        : 11
% 0.21/0.46  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.46  # Initial clauses                      : 26
% 0.21/0.46  # Removed in clause preprocessing      : 2
% 0.21/0.46  # Initial clauses in saturation        : 24
% 0.21/0.46  # Processed clauses                    : 748
% 0.21/0.46  # ...of these trivial                  : 92
% 0.21/0.46  # ...subsumed                          : 462
% 0.21/0.46  # ...remaining for further processing  : 194
% 0.21/0.46  # Other redundant clauses eliminated   : 107
% 0.21/0.46  # Clauses deleted for lack of memory   : 0
% 0.21/0.46  # Backward-subsumed                    : 3
% 0.21/0.46  # Backward-rewritten                   : 22
% 0.21/0.46  # Generated clauses                    : 7358
% 0.21/0.46  # ...of the previous two non-trivial   : 5700
% 0.21/0.46  # Contextual simplify-reflections      : 0
% 0.21/0.46  # Paramodulations                      : 7243
% 0.21/0.46  # Factorizations                       : 8
% 0.21/0.46  # Equation resolutions                 : 107
% 0.21/0.46  # Propositional unsat checks           : 0
% 0.21/0.46  #    Propositional check models        : 0
% 0.21/0.46  #    Propositional check unsatisfiable : 0
% 0.21/0.46  #    Propositional clauses             : 0
% 0.21/0.46  #    Propositional clauses after purity: 0
% 0.21/0.46  #    Propositional unsat core size     : 0
% 0.21/0.46  #    Propositional preprocessing time  : 0.000
% 0.21/0.46  #    Propositional encoding time       : 0.000
% 0.21/0.46  #    Propositional solver time         : 0.000
% 0.21/0.46  #    Success case prop preproc time    : 0.000
% 0.21/0.46  #    Success case prop encoding time   : 0.000
% 0.21/0.46  #    Success case prop solver time     : 0.000
% 0.21/0.46  # Current number of processed clauses  : 138
% 0.21/0.46  #    Positive orientable unit clauses  : 26
% 0.21/0.46  #    Positive unorientable unit clauses: 0
% 0.21/0.46  #    Negative unit clauses             : 9
% 0.21/0.46  #    Non-unit-clauses                  : 103
% 0.21/0.46  # Current number of unprocessed clauses: 4973
% 0.21/0.46  # ...number of literals in the above   : 16324
% 0.21/0.46  # Current number of archived formulas  : 0
% 0.21/0.46  # Current number of archived clauses   : 52
% 0.21/0.46  # Clause-clause subsumption calls (NU) : 4095
% 0.21/0.46  # Rec. Clause-clause subsumption calls : 3639
% 0.21/0.46  # Non-unit clause-clause subsumptions  : 451
% 0.21/0.46  # Unit Clause-clause subsumption calls : 112
% 0.21/0.46  # Rewrite failures with RHS unbound    : 0
% 0.21/0.46  # BW rewrite match attempts            : 18
% 0.21/0.46  # BW rewrite match successes           : 16
% 0.21/0.46  # Condensation attempts                : 0
% 0.21/0.46  # Condensation successes               : 0
% 0.21/0.46  # Termbank termtop insertions          : 117418
% 0.21/0.46  
% 0.21/0.46  # -------------------------------------------------
% 0.21/0.46  # User time                : 0.105 s
% 0.21/0.46  # System time              : 0.007 s
% 0.21/0.46  # Total time               : 0.112 s
% 0.21/0.46  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
