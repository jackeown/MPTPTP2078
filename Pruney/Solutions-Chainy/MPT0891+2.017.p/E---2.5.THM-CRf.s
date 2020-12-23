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
% DateTime   : Thu Dec  3 10:59:55 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 312 expanded)
%              Number of clauses        :   46 ( 131 expanded)
%              Number of leaves         :   10 (  76 expanded)
%              Depth                    :   14
%              Number of atoms          :  208 (1254 expanded)
%              Number of equality atoms :  157 ( 994 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   15 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

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

fof(t9_mcart_1,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] :
            ~ ( r2_hidden(X2,X1)
              & ! [X3,X4] :
                  ~ ( ( r2_hidden(X3,X1)
                      | r2_hidden(X4,X1) )
                    & X2 = k4_tarski(X3,X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

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

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t152_zfmisc_1,axiom,(
    ! [X1,X2] : ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(c_0_10,negated_conjecture,(
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

fof(c_0_11,plain,(
    ! [X32,X33,X34,X35] :
      ( ( k5_mcart_1(X32,X33,X34,X35) = k1_mcart_1(k1_mcart_1(X35))
        | ~ m1_subset_1(X35,k3_zfmisc_1(X32,X33,X34))
        | X32 = k1_xboole_0
        | X33 = k1_xboole_0
        | X34 = k1_xboole_0 )
      & ( k6_mcart_1(X32,X33,X34,X35) = k2_mcart_1(k1_mcart_1(X35))
        | ~ m1_subset_1(X35,k3_zfmisc_1(X32,X33,X34))
        | X32 = k1_xboole_0
        | X33 = k1_xboole_0
        | X34 = k1_xboole_0 )
      & ( k7_mcart_1(X32,X33,X34,X35) = k2_mcart_1(X35)
        | ~ m1_subset_1(X35,k3_zfmisc_1(X32,X33,X34))
        | X32 = k1_xboole_0
        | X33 = k1_xboole_0
        | X34 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_mcart_1])])])])).

fof(c_0_12,plain,(
    ! [X20,X21,X22] : k3_zfmisc_1(X20,X21,X22) = k2_zfmisc_1(k2_zfmisc_1(X20,X21),X22) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_13,negated_conjecture,
    ( esk4_0 != k1_xboole_0
    & esk5_0 != k1_xboole_0
    & esk6_0 != k1_xboole_0
    & m1_subset_1(esk7_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0))
    & ( esk7_0 = k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)
      | esk7_0 = k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)
      | esk7_0 = k7_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

fof(c_0_14,plain,(
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

fof(c_0_15,plain,(
    ! [X28,X29,X30,X31] :
      ( X28 = k1_xboole_0
      | X29 = k1_xboole_0
      | X30 = k1_xboole_0
      | ~ m1_subset_1(X31,k3_zfmisc_1(X28,X29,X30))
      | X31 = k3_mcart_1(k5_mcart_1(X28,X29,X30,X31),k6_mcart_1(X28,X29,X30,X31),k7_mcart_1(X28,X29,X30,X31)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_mcart_1])])])).

fof(c_0_16,plain,(
    ! [X17,X18,X19] : k3_mcart_1(X17,X18,X19) = k4_tarski(k4_tarski(X17,X18),X19) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

cnf(c_0_17,plain,
    ( k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk7_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_20,plain,(
    ! [X36,X38,X39] :
      ( ( r2_hidden(esk3_1(X36),X36)
        | X36 = k1_xboole_0 )
      & ( ~ r2_hidden(X38,X36)
        | esk3_1(X36) != k4_tarski(X38,X39)
        | X36 = k1_xboole_0 )
      & ( ~ r2_hidden(X39,X36)
        | esk3_1(X36) != k4_tarski(X38,X39)
        | X36 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_mcart_1])])])])])).

cnf(c_0_21,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_22,plain,(
    ! [X23,X25,X26,X27] :
      ( ( r2_hidden(esk2_1(X23),X23)
        | X23 = k1_xboole_0 )
      & ( ~ r2_hidden(X25,X23)
        | esk2_1(X23) != k3_mcart_1(X25,X26,X27)
        | X23 = k1_xboole_0 )
      & ( ~ r2_hidden(X26,X23)
        | esk2_1(X23) != k3_mcart_1(X25,X26,X27)
        | X23 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_mcart_1])])])])])])).

cnf(c_0_23,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4))
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4)
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk7_0,k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0)) ),
    inference(rw,[status(thm)],[c_0_19,c_0_18])).

cnf(c_0_27,negated_conjecture,
    ( esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_28,negated_conjecture,
    ( esk5_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_29,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_30,plain,
    ( X2 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | esk3_1(X2) != k4_tarski(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,plain,
    ( r2_hidden(esk3_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_32,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k1_tarski(X2)) ),
    inference(er,[status(thm)],[c_0_21])).

fof(c_0_33,plain,(
    ! [X13,X14] :
      ( ( k2_zfmisc_1(X13,X14) != k1_xboole_0
        | X13 = k1_xboole_0
        | X14 = k1_xboole_0 )
      & ( X13 != k1_xboole_0
        | k2_zfmisc_1(X13,X14) = k1_xboole_0 )
      & ( X14 != k1_xboole_0
        | k2_zfmisc_1(X13,X14) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_34,plain,
    ( X2 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | esk2_1(X2) != k3_mcart_1(X3,X1,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_35,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | X4 = k4_tarski(k4_tarski(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4)),k7_mcart_1(X1,X2,X3,X4))
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_24]),c_0_18])).

cnf(c_0_36,negated_conjecture,
    ( k7_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) = k2_mcart_1(esk7_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_28]),c_0_29])).

cnf(c_0_37,plain,
    ( X1 = k1_xboole_0
    | k4_tarski(X2,esk3_1(X1)) != esk3_1(X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_38,plain,
    ( esk3_1(k1_tarski(X1)) = X1
    | k1_tarski(X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_32,c_0_31])).

fof(c_0_39,plain,(
    ! [X15,X16] : ~ r2_hidden(X15,k2_zfmisc_1(X15,X16)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).

cnf(c_0_40,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,plain,
    ( X2 = k1_xboole_0
    | esk2_1(X2) != k4_tarski(k4_tarski(X3,X1),X4)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_34,c_0_24])).

cnf(c_0_42,negated_conjecture,
    ( k4_tarski(k4_tarski(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0),k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)),k2_mcart_1(esk7_0)) = esk7_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_26]),c_0_36]),c_0_27]),c_0_28]),c_0_29])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_44,plain,
    ( k1_tarski(X1) = k1_xboole_0
    | k4_tarski(X2,X1) != X1 ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_45,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_46,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_40])).

cnf(c_0_47,negated_conjecture,
    ( X1 = k1_xboole_0
    | esk2_1(X1) != esk7_0
    | ~ r2_hidden(k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0),X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,k1_tarski(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_43])])).

cnf(c_0_49,plain,
    ( r2_hidden(esk2_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_50,negated_conjecture,
    ( esk7_0 = k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)
    | esk7_0 = k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)
    | esk7_0 = k7_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_51,negated_conjecture,
    ( k1_tarski(k2_mcart_1(esk7_0)) = k1_xboole_0
    | k2_mcart_1(esk7_0) != esk7_0 ),
    inference(spm,[status(thm)],[c_0_44,c_0_42])).

cnf(c_0_52,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_53,negated_conjecture,
    ( k1_tarski(k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)) = k1_xboole_0
    | esk2_1(k1_tarski(k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0))) != esk7_0 ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_54,plain,
    ( esk2_1(k1_tarski(X1)) = X1
    | k1_tarski(X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_32,c_0_49])).

cnf(c_0_55,plain,
    ( X2 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | esk2_1(X2) != k3_mcart_1(X1,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_56,negated_conjecture,
    ( k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) = esk7_0
    | k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) = esk7_0
    | k2_mcart_1(esk7_0) = esk7_0 ),
    inference(spm,[status(thm)],[c_0_50,c_0_36])).

cnf(c_0_57,negated_conjecture,
    ( k2_mcart_1(esk7_0) != esk7_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_51]),c_0_52])).

cnf(c_0_58,negated_conjecture,
    ( k1_tarski(k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)) = k1_xboole_0
    | k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) != esk7_0 ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_59,plain,
    ( X2 = k1_xboole_0
    | esk2_1(X2) != k4_tarski(k4_tarski(X1,X3),X4)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_55,c_0_24])).

cnf(c_0_60,negated_conjecture,
    ( k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) = esk7_0
    | k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) = esk7_0 ),
    inference(sr,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_61,negated_conjecture,
    ( k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) != esk7_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_58]),c_0_52])).

cnf(c_0_62,negated_conjecture,
    ( X1 = k1_xboole_0
    | esk2_1(X1) != esk7_0
    | ~ r2_hidden(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0),X1) ),
    inference(spm,[status(thm)],[c_0_59,c_0_42])).

cnf(c_0_63,negated_conjecture,
    ( k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) = esk7_0 ),
    inference(sr,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_64,negated_conjecture,
    ( X1 = k1_xboole_0
    | esk2_1(X1) != esk7_0
    | ~ r2_hidden(esk7_0,X1) ),
    inference(rw,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_65,negated_conjecture,
    ( k1_tarski(esk7_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_54])]),c_0_48])])).

cnf(c_0_66,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_65]),c_0_52]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:56:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.028 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t51_mcart_1, conjecture, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>((X4!=k5_mcart_1(X1,X2,X3,X4)&X4!=k6_mcart_1(X1,X2,X3,X4))&X4!=k7_mcart_1(X1,X2,X3,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_mcart_1)).
% 0.13/0.38  fof(t50_mcart_1, axiom, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>((k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))&k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4)))&k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_mcart_1)).
% 0.13/0.38  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 0.13/0.38  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 0.13/0.38  fof(t48_mcart_1, axiom, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>X4=k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_mcart_1)).
% 0.13/0.38  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 0.13/0.38  fof(t9_mcart_1, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&![X3, X4]:~(((r2_hidden(X3,X1)|r2_hidden(X4,X1))&X2=k4_tarski(X3,X4))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_mcart_1)).
% 0.13/0.38  fof(t29_mcart_1, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&![X3, X4, X5]:~(((r2_hidden(X3,X1)|r2_hidden(X4,X1))&X2=k3_mcart_1(X3,X4,X5))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_mcart_1)).
% 0.13/0.38  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.13/0.38  fof(t152_zfmisc_1, axiom, ![X1, X2]:~(r2_hidden(X1,k2_zfmisc_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 0.13/0.38  fof(c_0_10, negated_conjecture, ~(![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>((X4!=k5_mcart_1(X1,X2,X3,X4)&X4!=k6_mcart_1(X1,X2,X3,X4))&X4!=k7_mcart_1(X1,X2,X3,X4))))))), inference(assume_negation,[status(cth)],[t51_mcart_1])).
% 0.13/0.38  fof(c_0_11, plain, ![X32, X33, X34, X35]:(((k5_mcart_1(X32,X33,X34,X35)=k1_mcart_1(k1_mcart_1(X35))|~m1_subset_1(X35,k3_zfmisc_1(X32,X33,X34))|(X32=k1_xboole_0|X33=k1_xboole_0|X34=k1_xboole_0))&(k6_mcart_1(X32,X33,X34,X35)=k2_mcart_1(k1_mcart_1(X35))|~m1_subset_1(X35,k3_zfmisc_1(X32,X33,X34))|(X32=k1_xboole_0|X33=k1_xboole_0|X34=k1_xboole_0)))&(k7_mcart_1(X32,X33,X34,X35)=k2_mcart_1(X35)|~m1_subset_1(X35,k3_zfmisc_1(X32,X33,X34))|(X32=k1_xboole_0|X33=k1_xboole_0|X34=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_mcart_1])])])])).
% 0.13/0.38  fof(c_0_12, plain, ![X20, X21, X22]:k3_zfmisc_1(X20,X21,X22)=k2_zfmisc_1(k2_zfmisc_1(X20,X21),X22), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 0.13/0.38  fof(c_0_13, negated_conjecture, (((esk4_0!=k1_xboole_0&esk5_0!=k1_xboole_0)&esk6_0!=k1_xboole_0)&(m1_subset_1(esk7_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0))&(esk7_0=k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)|esk7_0=k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)|esk7_0=k7_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).
% 0.13/0.38  fof(c_0_14, plain, ![X6, X7, X8, X9, X10, X11]:(((~r2_hidden(X8,X7)|X8=X6|X7!=k1_tarski(X6))&(X9!=X6|r2_hidden(X9,X7)|X7!=k1_tarski(X6)))&((~r2_hidden(esk1_2(X10,X11),X11)|esk1_2(X10,X11)!=X10|X11=k1_tarski(X10))&(r2_hidden(esk1_2(X10,X11),X11)|esk1_2(X10,X11)=X10|X11=k1_tarski(X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.13/0.38  fof(c_0_15, plain, ![X28, X29, X30, X31]:(X28=k1_xboole_0|X29=k1_xboole_0|X30=k1_xboole_0|(~m1_subset_1(X31,k3_zfmisc_1(X28,X29,X30))|X31=k3_mcart_1(k5_mcart_1(X28,X29,X30,X31),k6_mcart_1(X28,X29,X30,X31),k7_mcart_1(X28,X29,X30,X31)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_mcart_1])])])).
% 0.13/0.38  fof(c_0_16, plain, ![X17, X18, X19]:k3_mcart_1(X17,X18,X19)=k4_tarski(k4_tarski(X17,X18),X19), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 0.13/0.38  cnf(c_0_17, plain, (k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  cnf(c_0_18, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_19, negated_conjecture, (m1_subset_1(esk7_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  fof(c_0_20, plain, ![X36, X38, X39]:((r2_hidden(esk3_1(X36),X36)|X36=k1_xboole_0)&((~r2_hidden(X38,X36)|esk3_1(X36)!=k4_tarski(X38,X39)|X36=k1_xboole_0)&(~r2_hidden(X39,X36)|esk3_1(X36)!=k4_tarski(X38,X39)|X36=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_mcart_1])])])])])).
% 0.13/0.38  cnf(c_0_21, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.38  fof(c_0_22, plain, ![X23, X25, X26, X27]:((r2_hidden(esk2_1(X23),X23)|X23=k1_xboole_0)&((~r2_hidden(X25,X23)|esk2_1(X23)!=k3_mcart_1(X25,X26,X27)|X23=k1_xboole_0)&(~r2_hidden(X26,X23)|esk2_1(X23)!=k3_mcart_1(X25,X26,X27)|X23=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_mcart_1])])])])])])).
% 0.13/0.38  cnf(c_0_23, plain, (X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4))|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_24, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  cnf(c_0_25, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 0.13/0.38  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk7_0,k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0))), inference(rw,[status(thm)],[c_0_19, c_0_18])).
% 0.13/0.38  cnf(c_0_27, negated_conjecture, (esk6_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_28, negated_conjecture, (esk5_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_29, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_30, plain, (X2=k1_xboole_0|~r2_hidden(X1,X2)|esk3_1(X2)!=k4_tarski(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.38  cnf(c_0_31, plain, (r2_hidden(esk3_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.38  cnf(c_0_32, plain, (X1=X2|~r2_hidden(X1,k1_tarski(X2))), inference(er,[status(thm)],[c_0_21])).
% 0.13/0.38  fof(c_0_33, plain, ![X13, X14]:((k2_zfmisc_1(X13,X14)!=k1_xboole_0|(X13=k1_xboole_0|X14=k1_xboole_0))&((X13!=k1_xboole_0|k2_zfmisc_1(X13,X14)=k1_xboole_0)&(X14!=k1_xboole_0|k2_zfmisc_1(X13,X14)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.13/0.38  cnf(c_0_34, plain, (X2=k1_xboole_0|~r2_hidden(X1,X2)|esk2_1(X2)!=k3_mcart_1(X3,X1,X4)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.38  cnf(c_0_35, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|X4=k4_tarski(k4_tarski(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4)),k7_mcart_1(X1,X2,X3,X4))|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_24]), c_0_18])).
% 0.13/0.38  cnf(c_0_36, negated_conjecture, (k7_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)=k2_mcart_1(esk7_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27]), c_0_28]), c_0_29])).
% 0.13/0.38  cnf(c_0_37, plain, (X1=k1_xboole_0|k4_tarski(X2,esk3_1(X1))!=esk3_1(X1)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.13/0.38  cnf(c_0_38, plain, (esk3_1(k1_tarski(X1))=X1|k1_tarski(X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_32, c_0_31])).
% 0.13/0.38  fof(c_0_39, plain, ![X15, X16]:~r2_hidden(X15,k2_zfmisc_1(X15,X16)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).
% 0.13/0.38  cnf(c_0_40, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.13/0.38  cnf(c_0_41, plain, (X2=k1_xboole_0|esk2_1(X2)!=k4_tarski(k4_tarski(X3,X1),X4)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_34, c_0_24])).
% 0.13/0.38  cnf(c_0_42, negated_conjecture, (k4_tarski(k4_tarski(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0),k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)),k2_mcart_1(esk7_0))=esk7_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_26]), c_0_36]), c_0_27]), c_0_28]), c_0_29])).
% 0.13/0.38  cnf(c_0_43, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.38  cnf(c_0_44, plain, (k1_tarski(X1)=k1_xboole_0|k4_tarski(X2,X1)!=X1), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.13/0.38  cnf(c_0_45, plain, (~r2_hidden(X1,k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.13/0.38  cnf(c_0_46, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_40])).
% 0.13/0.38  cnf(c_0_47, negated_conjecture, (X1=k1_xboole_0|esk2_1(X1)!=esk7_0|~r2_hidden(k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0),X1)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.13/0.38  cnf(c_0_48, plain, (r2_hidden(X1,k1_tarski(X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_43])])).
% 0.13/0.38  cnf(c_0_49, plain, (r2_hidden(esk2_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.38  cnf(c_0_50, negated_conjecture, (esk7_0=k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)|esk7_0=k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)|esk7_0=k7_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_51, negated_conjecture, (k1_tarski(k2_mcart_1(esk7_0))=k1_xboole_0|k2_mcart_1(esk7_0)!=esk7_0), inference(spm,[status(thm)],[c_0_44, c_0_42])).
% 0.13/0.38  cnf(c_0_52, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.13/0.38  cnf(c_0_53, negated_conjecture, (k1_tarski(k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0))=k1_xboole_0|esk2_1(k1_tarski(k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)))!=esk7_0), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.13/0.38  cnf(c_0_54, plain, (esk2_1(k1_tarski(X1))=X1|k1_tarski(X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_32, c_0_49])).
% 0.13/0.38  cnf(c_0_55, plain, (X2=k1_xboole_0|~r2_hidden(X1,X2)|esk2_1(X2)!=k3_mcart_1(X1,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.38  cnf(c_0_56, negated_conjecture, (k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)=esk7_0|k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)=esk7_0|k2_mcart_1(esk7_0)=esk7_0), inference(spm,[status(thm)],[c_0_50, c_0_36])).
% 0.13/0.38  cnf(c_0_57, negated_conjecture, (k2_mcart_1(esk7_0)!=esk7_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_51]), c_0_52])).
% 0.13/0.38  cnf(c_0_58, negated_conjecture, (k1_tarski(k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0))=k1_xboole_0|k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)!=esk7_0), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.13/0.38  cnf(c_0_59, plain, (X2=k1_xboole_0|esk2_1(X2)!=k4_tarski(k4_tarski(X1,X3),X4)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_55, c_0_24])).
% 0.13/0.38  cnf(c_0_60, negated_conjecture, (k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)=esk7_0|k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)=esk7_0), inference(sr,[status(thm)],[c_0_56, c_0_57])).
% 0.13/0.38  cnf(c_0_61, negated_conjecture, (k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)!=esk7_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_58]), c_0_52])).
% 0.13/0.38  cnf(c_0_62, negated_conjecture, (X1=k1_xboole_0|esk2_1(X1)!=esk7_0|~r2_hidden(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0),X1)), inference(spm,[status(thm)],[c_0_59, c_0_42])).
% 0.13/0.38  cnf(c_0_63, negated_conjecture, (k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)=esk7_0), inference(sr,[status(thm)],[c_0_60, c_0_61])).
% 0.13/0.38  cnf(c_0_64, negated_conjecture, (X1=k1_xboole_0|esk2_1(X1)!=esk7_0|~r2_hidden(esk7_0,X1)), inference(rw,[status(thm)],[c_0_62, c_0_63])).
% 0.13/0.38  cnf(c_0_65, negated_conjecture, (k1_tarski(esk7_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_54])]), c_0_48])])).
% 0.13/0.38  cnf(c_0_66, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_65]), c_0_52]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 67
% 0.13/0.38  # Proof object clause steps            : 46
% 0.13/0.38  # Proof object formula steps           : 21
% 0.13/0.38  # Proof object conjectures             : 24
% 0.13/0.38  # Proof object clause conjectures      : 21
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 18
% 0.13/0.38  # Proof object initial formulas used   : 10
% 0.13/0.38  # Proof object generating inferences   : 17
% 0.13/0.38  # Proof object simplifying inferences  : 26
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 10
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 25
% 0.13/0.38  # Removed in clause preprocessing      : 2
% 0.13/0.38  # Initial clauses in saturation        : 23
% 0.13/0.38  # Processed clauses                    : 86
% 0.13/0.38  # ...of these trivial                  : 0
% 0.13/0.38  # ...subsumed                          : 3
% 0.13/0.38  # ...remaining for further processing  : 83
% 0.13/0.38  # Other redundant clauses eliminated   : 8
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 2
% 0.13/0.38  # Backward-rewritten                   : 4
% 0.13/0.38  # Generated clauses                    : 66
% 0.13/0.38  # ...of the previous two non-trivial   : 61
% 0.13/0.38  # Contextual simplify-reflections      : 1
% 0.13/0.38  # Paramodulations                      : 57
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 8
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 48
% 0.13/0.38  #    Positive orientable unit clauses  : 9
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 8
% 0.13/0.38  #    Non-unit-clauses                  : 31
% 0.13/0.38  # Current number of unprocessed clauses: 21
% 0.13/0.38  # ...number of literals in the above   : 52
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 33
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 223
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 166
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 2
% 0.13/0.38  # Unit Clause-clause subsumption calls : 26
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 3
% 0.13/0.38  # BW rewrite match successes           : 2
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 2757
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.031 s
% 0.13/0.38  # System time              : 0.004 s
% 0.13/0.38  # Total time               : 0.036 s
% 0.13/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
