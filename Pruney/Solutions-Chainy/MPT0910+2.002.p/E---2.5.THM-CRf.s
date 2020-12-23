%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:11 EST 2020

% Result     : Theorem 6.00s
% Output     : CNFRefutation 6.00s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 246 expanded)
%              Number of clauses        :   49 ( 102 expanded)
%              Number of leaves         :   11 (  61 expanded)
%              Depth                    :   15
%              Number of atoms          :  244 (1205 expanded)
%              Number of equality atoms :  131 ( 690 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   15 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t70_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5] :
      ( m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))
     => ( ! [X6] :
            ( m1_subset_1(X6,X1)
           => ! [X7] :
                ( m1_subset_1(X7,X2)
               => ! [X8] :
                    ( m1_subset_1(X8,X3)
                   => ( X5 = k3_mcart_1(X6,X7,X8)
                     => X4 = X7 ) ) ) )
       => ( X1 = k1_xboole_0
          | X2 = k1_xboole_0
          | X3 = k1_xboole_0
          | X4 = k6_mcart_1(X1,X2,X3,X5) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_mcart_1)).

fof(t10_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
     => ( r2_hidden(k1_mcart_1(X1),X2)
        & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

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

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(dt_k7_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
     => m1_subset_1(k7_mcart_1(X1,X2,X3,X4),X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_mcart_1)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5] :
        ( m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))
       => ( ! [X6] :
              ( m1_subset_1(X6,X1)
             => ! [X7] :
                  ( m1_subset_1(X7,X2)
                 => ! [X8] :
                      ( m1_subset_1(X8,X3)
                     => ( X5 = k3_mcart_1(X6,X7,X8)
                       => X4 = X7 ) ) ) )
         => ( X1 = k1_xboole_0
            | X2 = k1_xboole_0
            | X3 = k1_xboole_0
            | X4 = k6_mcart_1(X1,X2,X3,X5) ) ) ) ),
    inference(assume_negation,[status(cth)],[t70_mcart_1])).

fof(c_0_12,plain,(
    ! [X29,X30,X31] :
      ( ( r2_hidden(k1_mcart_1(X29),X30)
        | ~ r2_hidden(X29,k2_zfmisc_1(X30,X31)) )
      & ( r2_hidden(k2_mcart_1(X29),X31)
        | ~ r2_hidden(X29,k2_zfmisc_1(X30,X31)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).

fof(c_0_13,plain,(
    ! [X17,X18] :
      ( ( ~ m1_subset_1(X18,X17)
        | r2_hidden(X18,X17)
        | v1_xboole_0(X17) )
      & ( ~ r2_hidden(X18,X17)
        | m1_subset_1(X18,X17)
        | v1_xboole_0(X17) )
      & ( ~ m1_subset_1(X18,X17)
        | v1_xboole_0(X18)
        | ~ v1_xboole_0(X17) )
      & ( ~ v1_xboole_0(X18)
        | m1_subset_1(X18,X17)
        | ~ v1_xboole_0(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_14,negated_conjecture,(
    ! [X45,X46,X47] :
      ( m1_subset_1(esk7_0,k3_zfmisc_1(esk3_0,esk4_0,esk5_0))
      & ( ~ m1_subset_1(X45,esk3_0)
        | ~ m1_subset_1(X46,esk4_0)
        | ~ m1_subset_1(X47,esk5_0)
        | esk7_0 != k3_mcart_1(X45,X46,X47)
        | esk6_0 = X46 )
      & esk3_0 != k1_xboole_0
      & esk4_0 != k1_xboole_0
      & esk5_0 != k1_xboole_0
      & esk6_0 != k6_mcart_1(esk3_0,esk4_0,esk5_0,esk7_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])])).

fof(c_0_15,plain,(
    ! [X22,X23,X24] : k3_zfmisc_1(X22,X23,X24) = k2_zfmisc_1(k2_zfmisc_1(X22,X23),X24) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_16,plain,(
    ! [X9,X10,X11] :
      ( ( ~ v1_xboole_0(X9)
        | ~ r2_hidden(X10,X9) )
      & ( r2_hidden(esk1_1(X11),X11)
        | v1_xboole_0(X11) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_17,plain,(
    ! [X13] :
      ( X13 = k1_xboole_0
      | r2_hidden(esk2_1(X13),X13) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_18,plain,
    ( r2_hidden(k1_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk7_0,k3_zfmisc_1(esk3_0,esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_22,plain,(
    ! [X32,X33,X34,X35] :
      ( X32 = k1_xboole_0
      | X33 = k1_xboole_0
      | X34 = k1_xboole_0
      | ~ m1_subset_1(X35,k3_zfmisc_1(X32,X33,X34))
      | X35 = k3_mcart_1(k5_mcart_1(X32,X33,X34,X35),k6_mcart_1(X32,X33,X34,X35),k7_mcart_1(X32,X33,X34,X35)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_mcart_1])])])).

fof(c_0_23,plain,(
    ! [X19,X20,X21] : k3_mcart_1(X19,X20,X21) = k4_tarski(k4_tarski(X19,X20),X21) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

fof(c_0_24,plain,(
    ! [X36,X37,X38,X39] :
      ( ( k5_mcart_1(X36,X37,X38,X39) = k1_mcart_1(k1_mcart_1(X39))
        | ~ m1_subset_1(X39,k3_zfmisc_1(X36,X37,X38))
        | X36 = k1_xboole_0
        | X37 = k1_xboole_0
        | X38 = k1_xboole_0 )
      & ( k6_mcart_1(X36,X37,X38,X39) = k2_mcart_1(k1_mcart_1(X39))
        | ~ m1_subset_1(X39,k3_zfmisc_1(X36,X37,X38))
        | X36 = k1_xboole_0
        | X37 = k1_xboole_0
        | X38 = k1_xboole_0 )
      & ( k7_mcart_1(X36,X37,X38,X39) = k2_mcart_1(X39)
        | ~ m1_subset_1(X39,k3_zfmisc_1(X36,X37,X38))
        | X36 = k1_xboole_0
        | X37 = k1_xboole_0
        | X38 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_mcart_1])])])])).

cnf(c_0_25,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,plain,
    ( r2_hidden(k1_mcart_1(X1),X2)
    | v1_xboole_0(k2_zfmisc_1(X2,X3))
    | ~ m1_subset_1(X1,k2_zfmisc_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk7_0,k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0)) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_29,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4))
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_32,plain,(
    ! [X15,X16] :
      ( ( k2_zfmisc_1(X15,X16) != k1_xboole_0
        | X15 = k1_xboole_0
        | X16 = k1_xboole_0 )
      & ( X15 != k1_xboole_0
        | k2_zfmisc_1(X15,X16) = k1_xboole_0 )
      & ( X16 != k1_xboole_0
        | k2_zfmisc_1(X15,X16) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_33,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk7_0),k2_zfmisc_1(esk3_0,esk4_0))
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_35,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | X4 = k4_tarski(k4_tarski(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4)),k7_mcart_1(X1,X2,X3,X4))
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_30]),c_0_21])).

cnf(c_0_36,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4)
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_31,c_0_21])).

cnf(c_0_37,plain,
    ( k6_mcart_1(X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_38,plain,(
    ! [X25,X26,X27,X28] :
      ( ~ m1_subset_1(X28,k3_zfmisc_1(X25,X26,X27))
      | m1_subset_1(k7_mcart_1(X25,X26,X27,X28),X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_mcart_1])])).

cnf(c_0_39,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | k2_zfmisc_1(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0) = k1_xboole_0
    | r2_hidden(k1_mcart_1(esk7_0),k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_41,negated_conjecture,
    ( esk5_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_42,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4)),k2_mcart_1(X4)) = X4
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_43,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k6_mcart_1(X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_37,c_0_21])).

cnf(c_0_44,plain,
    ( k5_mcart_1(X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(X4))
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_45,plain,
    ( m1_subset_1(k7_mcart_1(X2,X3,X4,X1),X4)
    | ~ m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_46,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,esk4_0) = k1_xboole_0
    | r2_hidden(k1_mcart_1(esk7_0),k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41])).

cnf(c_0_47,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(X1,X2,X3,X4),k2_mcart_1(k1_mcart_1(X4))),k2_mcart_1(X4)) = X4
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_48,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k5_mcart_1(X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(X4))
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_44,c_0_21])).

cnf(c_0_49,plain,
    ( m1_subset_1(k7_mcart_1(X2,X3,X4,X1),X4)
    | ~ m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4)) ),
    inference(rw,[status(thm)],[c_0_45,c_0_21])).

cnf(c_0_50,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_51,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,esk4_0) = k1_xboole_0
    | r2_hidden(k1_mcart_1(k1_mcart_1(esk7_0)),esk3_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_46])).

cnf(c_0_52,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_53,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_54,negated_conjecture,
    ( esk6_0 = X2
    | ~ m1_subset_1(X1,esk3_0)
    | ~ m1_subset_1(X2,esk4_0)
    | ~ m1_subset_1(X3,esk5_0)
    | esk7_0 != k3_mcart_1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_55,plain,
    ( k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(X1)),k2_mcart_1(k1_mcart_1(X1))),k2_mcart_1(X1)) = X1
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | ~ m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_56,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | m1_subset_1(k2_mcart_1(X4),X3)
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_36])).

cnf(c_0_57,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[c_0_50,c_0_25])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(esk7_0)),esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_51]),c_0_52]),c_0_53])).

cnf(c_0_59,negated_conjecture,
    ( esk6_0 = X2
    | esk7_0 != k4_tarski(k4_tarski(X1,X2),X3)
    | ~ m1_subset_1(X3,esk5_0)
    | ~ m1_subset_1(X2,esk4_0)
    | ~ m1_subset_1(X1,esk3_0) ),
    inference(rw,[status(thm)],[c_0_54,c_0_30])).

cnf(c_0_60,negated_conjecture,
    ( k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(esk7_0)),k2_mcart_1(k1_mcart_1(esk7_0))),k2_mcart_1(esk7_0)) = esk7_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_28]),c_0_53]),c_0_52]),c_0_41])).

cnf(c_0_61,negated_conjecture,
    ( m1_subset_1(k2_mcart_1(esk7_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_28]),c_0_53]),c_0_52]),c_0_41])).

cnf(c_0_62,negated_conjecture,
    ( m1_subset_1(k1_mcart_1(k1_mcart_1(esk7_0)),esk3_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_63,plain,
    ( r2_hidden(k2_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_64,negated_conjecture,
    ( esk6_0 != k6_mcart_1(esk3_0,esk4_0,esk5_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_65,negated_conjecture,
    ( esk6_0 = k2_mcart_1(k1_mcart_1(esk7_0))
    | ~ m1_subset_1(k2_mcart_1(k1_mcart_1(esk7_0)),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61]),c_0_62])])).

cnf(c_0_66,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,esk4_0) = k1_xboole_0
    | r2_hidden(k2_mcart_1(k1_mcart_1(esk7_0)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_46])).

cnf(c_0_67,negated_conjecture,
    ( k6_mcart_1(esk3_0,esk4_0,esk5_0,esk7_0) != k2_mcart_1(k1_mcart_1(esk7_0))
    | ~ m1_subset_1(k2_mcart_1(k1_mcart_1(esk7_0)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_68,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,esk4_0) = k1_xboole_0
    | m1_subset_1(k2_mcart_1(k1_mcart_1(esk7_0)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_66])).

cnf(c_0_69,negated_conjecture,
    ( ~ m1_subset_1(k2_mcart_1(k1_mcart_1(esk7_0)),esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_43]),c_0_28])]),c_0_41]),c_0_52]),c_0_53])).

cnf(c_0_70,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,esk4_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_71,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_70]),c_0_52]),c_0_53]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:29:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 6.00/6.18  # AutoSched0-Mode selected heuristic G_E___208_B02_F1_AE_CS_SP_PS_S0Y
% 6.00/6.18  # and selection function SelectMaxLComplexAvoidPosPred.
% 6.00/6.18  #
% 6.00/6.18  # Preprocessing time       : 0.019 s
% 6.00/6.18  # Presaturation interreduction done
% 6.00/6.18  
% 6.00/6.18  # Proof found!
% 6.00/6.18  # SZS status Theorem
% 6.00/6.18  # SZS output start CNFRefutation
% 6.00/6.18  fof(t70_mcart_1, conjecture, ![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))=>(![X6]:(m1_subset_1(X6,X1)=>![X7]:(m1_subset_1(X7,X2)=>![X8]:(m1_subset_1(X8,X3)=>(X5=k3_mcart_1(X6,X7,X8)=>X4=X7))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k6_mcart_1(X1,X2,X3,X5)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_mcart_1)).
% 6.00/6.18  fof(t10_mcart_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(X2,X3))=>(r2_hidden(k1_mcart_1(X1),X2)&r2_hidden(k2_mcart_1(X1),X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 6.00/6.18  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 6.00/6.18  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 6.00/6.18  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 6.00/6.18  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 6.00/6.18  fof(t48_mcart_1, axiom, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>X4=k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_mcart_1)).
% 6.00/6.18  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 6.00/6.18  fof(t50_mcart_1, axiom, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>((k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))&k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4)))&k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_mcart_1)).
% 6.00/6.18  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 6.00/6.18  fof(dt_k7_mcart_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>m1_subset_1(k7_mcart_1(X1,X2,X3,X4),X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_mcart_1)).
% 6.00/6.18  fof(c_0_11, negated_conjecture, ~(![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))=>(![X6]:(m1_subset_1(X6,X1)=>![X7]:(m1_subset_1(X7,X2)=>![X8]:(m1_subset_1(X8,X3)=>(X5=k3_mcart_1(X6,X7,X8)=>X4=X7))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k6_mcart_1(X1,X2,X3,X5))))), inference(assume_negation,[status(cth)],[t70_mcart_1])).
% 6.00/6.18  fof(c_0_12, plain, ![X29, X30, X31]:((r2_hidden(k1_mcart_1(X29),X30)|~r2_hidden(X29,k2_zfmisc_1(X30,X31)))&(r2_hidden(k2_mcart_1(X29),X31)|~r2_hidden(X29,k2_zfmisc_1(X30,X31)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).
% 6.00/6.18  fof(c_0_13, plain, ![X17, X18]:(((~m1_subset_1(X18,X17)|r2_hidden(X18,X17)|v1_xboole_0(X17))&(~r2_hidden(X18,X17)|m1_subset_1(X18,X17)|v1_xboole_0(X17)))&((~m1_subset_1(X18,X17)|v1_xboole_0(X18)|~v1_xboole_0(X17))&(~v1_xboole_0(X18)|m1_subset_1(X18,X17)|~v1_xboole_0(X17)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 6.00/6.18  fof(c_0_14, negated_conjecture, ![X45, X46, X47]:(m1_subset_1(esk7_0,k3_zfmisc_1(esk3_0,esk4_0,esk5_0))&((~m1_subset_1(X45,esk3_0)|(~m1_subset_1(X46,esk4_0)|(~m1_subset_1(X47,esk5_0)|(esk7_0!=k3_mcart_1(X45,X46,X47)|esk6_0=X46))))&(((esk3_0!=k1_xboole_0&esk4_0!=k1_xboole_0)&esk5_0!=k1_xboole_0)&esk6_0!=k6_mcart_1(esk3_0,esk4_0,esk5_0,esk7_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])])).
% 6.00/6.18  fof(c_0_15, plain, ![X22, X23, X24]:k3_zfmisc_1(X22,X23,X24)=k2_zfmisc_1(k2_zfmisc_1(X22,X23),X24), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 6.00/6.18  fof(c_0_16, plain, ![X9, X10, X11]:((~v1_xboole_0(X9)|~r2_hidden(X10,X9))&(r2_hidden(esk1_1(X11),X11)|v1_xboole_0(X11))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 6.00/6.18  fof(c_0_17, plain, ![X13]:(X13=k1_xboole_0|r2_hidden(esk2_1(X13),X13)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 6.00/6.18  cnf(c_0_18, plain, (r2_hidden(k1_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 6.00/6.18  cnf(c_0_19, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 6.00/6.18  cnf(c_0_20, negated_conjecture, (m1_subset_1(esk7_0,k3_zfmisc_1(esk3_0,esk4_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 6.00/6.18  cnf(c_0_21, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 6.00/6.18  fof(c_0_22, plain, ![X32, X33, X34, X35]:(X32=k1_xboole_0|X33=k1_xboole_0|X34=k1_xboole_0|(~m1_subset_1(X35,k3_zfmisc_1(X32,X33,X34))|X35=k3_mcart_1(k5_mcart_1(X32,X33,X34,X35),k6_mcart_1(X32,X33,X34,X35),k7_mcart_1(X32,X33,X34,X35)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_mcart_1])])])).
% 6.00/6.18  fof(c_0_23, plain, ![X19, X20, X21]:k3_mcart_1(X19,X20,X21)=k4_tarski(k4_tarski(X19,X20),X21), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 6.00/6.18  fof(c_0_24, plain, ![X36, X37, X38, X39]:(((k5_mcart_1(X36,X37,X38,X39)=k1_mcart_1(k1_mcart_1(X39))|~m1_subset_1(X39,k3_zfmisc_1(X36,X37,X38))|(X36=k1_xboole_0|X37=k1_xboole_0|X38=k1_xboole_0))&(k6_mcart_1(X36,X37,X38,X39)=k2_mcart_1(k1_mcart_1(X39))|~m1_subset_1(X39,k3_zfmisc_1(X36,X37,X38))|(X36=k1_xboole_0|X37=k1_xboole_0|X38=k1_xboole_0)))&(k7_mcart_1(X36,X37,X38,X39)=k2_mcart_1(X39)|~m1_subset_1(X39,k3_zfmisc_1(X36,X37,X38))|(X36=k1_xboole_0|X37=k1_xboole_0|X38=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_mcart_1])])])])).
% 6.00/6.18  cnf(c_0_25, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 6.00/6.18  cnf(c_0_26, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 6.00/6.18  cnf(c_0_27, plain, (r2_hidden(k1_mcart_1(X1),X2)|v1_xboole_0(k2_zfmisc_1(X2,X3))|~m1_subset_1(X1,k2_zfmisc_1(X2,X3))), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 6.00/6.18  cnf(c_0_28, negated_conjecture, (m1_subset_1(esk7_0,k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0))), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 6.00/6.18  cnf(c_0_29, plain, (X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4))|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 6.00/6.18  cnf(c_0_30, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 6.00/6.18  cnf(c_0_31, plain, (k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 6.00/6.18  fof(c_0_32, plain, ![X15, X16]:((k2_zfmisc_1(X15,X16)!=k1_xboole_0|(X15=k1_xboole_0|X16=k1_xboole_0))&((X15!=k1_xboole_0|k2_zfmisc_1(X15,X16)=k1_xboole_0)&(X16!=k1_xboole_0|k2_zfmisc_1(X15,X16)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 6.00/6.18  cnf(c_0_33, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 6.00/6.18  cnf(c_0_34, negated_conjecture, (r2_hidden(k1_mcart_1(esk7_0),k2_zfmisc_1(esk3_0,esk4_0))|v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 6.00/6.18  cnf(c_0_35, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|X4=k4_tarski(k4_tarski(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4)),k7_mcart_1(X1,X2,X3,X4))|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_30]), c_0_21])).
% 6.00/6.18  cnf(c_0_36, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_31, c_0_21])).
% 6.00/6.18  cnf(c_0_37, plain, (k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4))|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 6.00/6.18  fof(c_0_38, plain, ![X25, X26, X27, X28]:(~m1_subset_1(X28,k3_zfmisc_1(X25,X26,X27))|m1_subset_1(k7_mcart_1(X25,X26,X27,X28),X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_mcart_1])])).
% 6.00/6.18  cnf(c_0_39, plain, (X1=k1_xboole_0|X2=k1_xboole_0|k2_zfmisc_1(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_32])).
% 6.00/6.18  cnf(c_0_40, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0)=k1_xboole_0|r2_hidden(k1_mcart_1(esk7_0),k2_zfmisc_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 6.00/6.18  cnf(c_0_41, negated_conjecture, (esk5_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 6.00/6.18  cnf(c_0_42, plain, (k4_tarski(k4_tarski(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4)),k2_mcart_1(X4))=X4|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 6.00/6.18  cnf(c_0_43, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4))|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_37, c_0_21])).
% 6.00/6.18  cnf(c_0_44, plain, (k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 6.00/6.18  cnf(c_0_45, plain, (m1_subset_1(k7_mcart_1(X2,X3,X4,X1),X4)|~m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 6.00/6.18  cnf(c_0_46, negated_conjecture, (k2_zfmisc_1(esk3_0,esk4_0)=k1_xboole_0|r2_hidden(k1_mcart_1(esk7_0),k2_zfmisc_1(esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41])).
% 6.00/6.18  cnf(c_0_47, plain, (k4_tarski(k4_tarski(k5_mcart_1(X1,X2,X3,X4),k2_mcart_1(k1_mcart_1(X4))),k2_mcart_1(X4))=X4|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 6.00/6.18  cnf(c_0_48, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_44, c_0_21])).
% 6.00/6.18  cnf(c_0_49, plain, (m1_subset_1(k7_mcart_1(X2,X3,X4,X1),X4)|~m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4))), inference(rw,[status(thm)],[c_0_45, c_0_21])).
% 6.00/6.18  cnf(c_0_50, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 6.00/6.18  cnf(c_0_51, negated_conjecture, (k2_zfmisc_1(esk3_0,esk4_0)=k1_xboole_0|r2_hidden(k1_mcart_1(k1_mcart_1(esk7_0)),esk3_0)), inference(spm,[status(thm)],[c_0_18, c_0_46])).
% 6.00/6.18  cnf(c_0_52, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 6.00/6.18  cnf(c_0_53, negated_conjecture, (esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 6.00/6.18  cnf(c_0_54, negated_conjecture, (esk6_0=X2|~m1_subset_1(X1,esk3_0)|~m1_subset_1(X2,esk4_0)|~m1_subset_1(X3,esk5_0)|esk7_0!=k3_mcart_1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 6.00/6.18  cnf(c_0_55, plain, (k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(X1)),k2_mcart_1(k1_mcart_1(X1))),k2_mcart_1(X1))=X1|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|~m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 6.00/6.18  cnf(c_0_56, plain, (X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|m1_subset_1(k2_mcart_1(X4),X3)|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(spm,[status(thm)],[c_0_49, c_0_36])).
% 6.00/6.18  cnf(c_0_57, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(csr,[status(thm)],[c_0_50, c_0_25])).
% 6.00/6.18  cnf(c_0_58, negated_conjecture, (r2_hidden(k1_mcart_1(k1_mcart_1(esk7_0)),esk3_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_51]), c_0_52]), c_0_53])).
% 6.00/6.18  cnf(c_0_59, negated_conjecture, (esk6_0=X2|esk7_0!=k4_tarski(k4_tarski(X1,X2),X3)|~m1_subset_1(X3,esk5_0)|~m1_subset_1(X2,esk4_0)|~m1_subset_1(X1,esk3_0)), inference(rw,[status(thm)],[c_0_54, c_0_30])).
% 6.00/6.18  cnf(c_0_60, negated_conjecture, (k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(esk7_0)),k2_mcart_1(k1_mcart_1(esk7_0))),k2_mcart_1(esk7_0))=esk7_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_28]), c_0_53]), c_0_52]), c_0_41])).
% 6.00/6.18  cnf(c_0_61, negated_conjecture, (m1_subset_1(k2_mcart_1(esk7_0),esk5_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_28]), c_0_53]), c_0_52]), c_0_41])).
% 6.00/6.18  cnf(c_0_62, negated_conjecture, (m1_subset_1(k1_mcart_1(k1_mcart_1(esk7_0)),esk3_0)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 6.00/6.18  cnf(c_0_63, plain, (r2_hidden(k2_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 6.00/6.18  cnf(c_0_64, negated_conjecture, (esk6_0!=k6_mcart_1(esk3_0,esk4_0,esk5_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 6.00/6.18  cnf(c_0_65, negated_conjecture, (esk6_0=k2_mcart_1(k1_mcart_1(esk7_0))|~m1_subset_1(k2_mcart_1(k1_mcart_1(esk7_0)),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_61]), c_0_62])])).
% 6.00/6.18  cnf(c_0_66, negated_conjecture, (k2_zfmisc_1(esk3_0,esk4_0)=k1_xboole_0|r2_hidden(k2_mcart_1(k1_mcart_1(esk7_0)),esk4_0)), inference(spm,[status(thm)],[c_0_63, c_0_46])).
% 6.00/6.18  cnf(c_0_67, negated_conjecture, (k6_mcart_1(esk3_0,esk4_0,esk5_0,esk7_0)!=k2_mcart_1(k1_mcart_1(esk7_0))|~m1_subset_1(k2_mcart_1(k1_mcart_1(esk7_0)),esk4_0)), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 6.00/6.18  cnf(c_0_68, negated_conjecture, (k2_zfmisc_1(esk3_0,esk4_0)=k1_xboole_0|m1_subset_1(k2_mcart_1(k1_mcart_1(esk7_0)),esk4_0)), inference(spm,[status(thm)],[c_0_57, c_0_66])).
% 6.00/6.18  cnf(c_0_69, negated_conjecture, (~m1_subset_1(k2_mcart_1(k1_mcart_1(esk7_0)),esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_43]), c_0_28])]), c_0_41]), c_0_52]), c_0_53])).
% 6.00/6.18  cnf(c_0_70, negated_conjecture, (k2_zfmisc_1(esk3_0,esk4_0)=k1_xboole_0), inference(sr,[status(thm)],[c_0_68, c_0_69])).
% 6.00/6.18  cnf(c_0_71, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_70]), c_0_52]), c_0_53]), ['proof']).
% 6.00/6.18  # SZS output end CNFRefutation
% 6.00/6.18  # Proof object total steps             : 72
% 6.00/6.18  # Proof object clause steps            : 49
% 6.00/6.18  # Proof object formula steps           : 23
% 6.00/6.18  # Proof object conjectures             : 26
% 6.00/6.18  # Proof object clause conjectures      : 23
% 6.00/6.18  # Proof object formula conjectures     : 3
% 6.00/6.18  # Proof object initial clauses used    : 20
% 6.00/6.18  # Proof object initial formulas used   : 11
% 6.00/6.18  # Proof object generating inferences   : 20
% 6.00/6.18  # Proof object simplifying inferences  : 29
% 6.00/6.18  # Training examples: 0 positive, 0 negative
% 6.00/6.18  # Parsed axioms                        : 11
% 6.00/6.18  # Removed by relevancy pruning/SinE    : 0
% 6.00/6.18  # Initial clauses                      : 25
% 6.00/6.18  # Removed in clause preprocessing      : 2
% 6.00/6.18  # Initial clauses in saturation        : 23
% 6.00/6.18  # Processed clauses                    : 128151
% 6.00/6.18  # ...of these trivial                  : 2
% 6.00/6.18  # ...subsumed                          : 121098
% 6.00/6.18  # ...remaining for further processing  : 7051
% 6.00/6.18  # Other redundant clauses eliminated   : 40
% 6.00/6.18  # Clauses deleted for lack of memory   : 0
% 6.00/6.18  # Backward-subsumed                    : 86
% 6.00/6.18  # Backward-rewritten                   : 3578
% 6.00/6.18  # Generated clauses                    : 698343
% 6.00/6.18  # ...of the previous two non-trivial   : 696788
% 6.00/6.18  # Contextual simplify-reflections      : 375
% 6.00/6.18  # Paramodulations                      : 698211
% 6.00/6.18  # Factorizations                       : 20
% 6.00/6.18  # Equation resolutions                 : 89
% 6.00/6.18  # Propositional unsat checks           : 0
% 6.00/6.18  #    Propositional check models        : 0
% 6.00/6.18  #    Propositional check unsatisfiable : 0
% 6.00/6.18  #    Propositional clauses             : 0
% 6.00/6.18  #    Propositional clauses after purity: 0
% 6.00/6.18  #    Propositional unsat core size     : 0
% 6.00/6.18  #    Propositional preprocessing time  : 0.000
% 6.00/6.18  #    Propositional encoding time       : 0.000
% 6.00/6.18  #    Propositional solver time         : 0.000
% 6.00/6.18  #    Success case prop preproc time    : 0.000
% 6.00/6.18  #    Success case prop encoding time   : 0.000
% 6.00/6.18  #    Success case prop solver time     : 0.000
% 6.00/6.18  # Current number of processed clauses  : 3341
% 6.00/6.18  #    Positive orientable unit clauses  : 6
% 6.00/6.18  #    Positive unorientable unit clauses: 0
% 6.00/6.18  #    Negative unit clauses             : 6
% 6.00/6.18  #    Non-unit-clauses                  : 3329
% 6.00/6.18  # Current number of unprocessed clauses: 562550
% 6.00/6.18  # ...number of literals in the above   : 1457014
% 6.00/6.18  # Current number of archived formulas  : 0
% 6.00/6.18  # Current number of archived clauses   : 3712
% 6.00/6.18  # Clause-clause subsumption calls (NU) : 5019352
% 6.00/6.18  # Rec. Clause-clause subsumption calls : 3893082
% 6.00/6.18  # Non-unit clause-clause subsumptions  : 121161
% 6.00/6.18  # Unit Clause-clause subsumption calls : 5432
% 6.00/6.18  # Rewrite failures with RHS unbound    : 0
% 6.00/6.18  # BW rewrite match attempts            : 3
% 6.00/6.18  # BW rewrite match successes           : 3
% 6.00/6.18  # Condensation attempts                : 0
% 6.00/6.18  # Condensation successes               : 0
% 6.00/6.18  # Termbank termtop insertions          : 13006780
% 6.02/6.21  
% 6.02/6.21  # -------------------------------------------------
% 6.02/6.21  # User time                : 5.632 s
% 6.02/6.21  # System time              : 0.236 s
% 6.02/6.21  # Total time               : 5.868 s
% 6.02/6.21  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
