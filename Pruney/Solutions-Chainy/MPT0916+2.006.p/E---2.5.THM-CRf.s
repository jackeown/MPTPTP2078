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
% DateTime   : Thu Dec  3 11:00:21 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 300 expanded)
%              Number of clauses        :   59 ( 137 expanded)
%              Number of leaves         :   12 (  74 expanded)
%              Depth                    :   12
%              Number of atoms          :  237 ( 973 expanded)
%              Number of equality atoms :   77 ( 146 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   15 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t76_mcart_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(X1))
     => ! [X5] :
          ( m1_subset_1(X5,k1_zfmisc_1(X2))
         => ! [X6] :
              ( m1_subset_1(X6,k1_zfmisc_1(X3))
             => ! [X7] :
                  ( m1_subset_1(X7,k3_zfmisc_1(X1,X2,X3))
                 => ( r2_hidden(X7,k3_zfmisc_1(X4,X5,X6))
                   => ( r2_hidden(k5_mcart_1(X1,X2,X3,X7),X4)
                      & r2_hidden(k6_mcart_1(X1,X2,X3,X7),X5)
                      & r2_hidden(k7_mcart_1(X1,X2,X3,X7),X6) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_mcart_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(t10_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
     => ( r2_hidden(k1_mcart_1(X1),X2)
        & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

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

fof(t68_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ~ v1_xboole_0(X3)
     => ~ ( r1_tarski(X3,X1)
          & r1_tarski(X3,X2)
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_xboole_1)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( m1_subset_1(X4,k1_zfmisc_1(X1))
       => ! [X5] :
            ( m1_subset_1(X5,k1_zfmisc_1(X2))
           => ! [X6] :
                ( m1_subset_1(X6,k1_zfmisc_1(X3))
               => ! [X7] :
                    ( m1_subset_1(X7,k3_zfmisc_1(X1,X2,X3))
                   => ( r2_hidden(X7,k3_zfmisc_1(X4,X5,X6))
                     => ( r2_hidden(k5_mcart_1(X1,X2,X3,X7),X4)
                        & r2_hidden(k6_mcart_1(X1,X2,X3,X7),X5)
                        & r2_hidden(k7_mcart_1(X1,X2,X3,X7),X6) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t76_mcart_1])).

fof(c_0_13,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(esk4_0))
    & m1_subset_1(esk8_0,k1_zfmisc_1(esk5_0))
    & m1_subset_1(esk9_0,k1_zfmisc_1(esk6_0))
    & m1_subset_1(esk10_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0))
    & r2_hidden(esk10_0,k3_zfmisc_1(esk7_0,esk8_0,esk9_0))
    & ( ~ r2_hidden(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0),esk7_0)
      | ~ r2_hidden(k6_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0),esk8_0)
      | ~ r2_hidden(k7_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0),esk9_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

fof(c_0_14,plain,(
    ! [X34,X35,X36] : k3_zfmisc_1(X34,X35,X36) = k2_zfmisc_1(k2_zfmisc_1(X34,X35),X36) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_15,plain,(
    ! [X37,X38,X39] :
      ( ( r2_hidden(k1_mcart_1(X37),X38)
        | ~ r2_hidden(X37,k2_zfmisc_1(X38,X39)) )
      & ( r2_hidden(k2_mcart_1(X37),X39)
        | ~ r2_hidden(X37,k2_zfmisc_1(X38,X39)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).

cnf(c_0_16,negated_conjecture,
    ( r2_hidden(esk10_0,k3_zfmisc_1(esk7_0,esk8_0,esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_18,plain,(
    ! [X40,X41,X42,X43] :
      ( ( k5_mcart_1(X40,X41,X42,X43) = k1_mcart_1(k1_mcart_1(X43))
        | ~ m1_subset_1(X43,k3_zfmisc_1(X40,X41,X42))
        | X40 = k1_xboole_0
        | X41 = k1_xboole_0
        | X42 = k1_xboole_0 )
      & ( k6_mcart_1(X40,X41,X42,X43) = k2_mcart_1(k1_mcart_1(X43))
        | ~ m1_subset_1(X43,k3_zfmisc_1(X40,X41,X42))
        | X40 = k1_xboole_0
        | X41 = k1_xboole_0
        | X42 = k1_xboole_0 )
      & ( k7_mcart_1(X40,X41,X42,X43) = k2_mcart_1(X43)
        | ~ m1_subset_1(X43,k3_zfmisc_1(X40,X41,X42))
        | X40 = k1_xboole_0
        | X41 = k1_xboole_0
        | X42 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_mcart_1])])])])).

fof(c_0_19,plain,(
    ! [X27,X28,X29] :
      ( v1_xboole_0(X29)
      | ~ r1_tarski(X29,X27)
      | ~ r1_tarski(X29,X28)
      | ~ r1_xboole_0(X27,X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t68_xboole_1])])])).

fof(c_0_20,plain,(
    ! [X30,X31] : r1_xboole_0(k4_xboole_0(X30,X31),X31) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

cnf(c_0_21,plain,
    ( r2_hidden(k1_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk10_0,k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),esk9_0)) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_23,plain,
    ( k6_mcart_1(X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk10_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_25,plain,
    ( k5_mcart_1(X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(X4))
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_26,plain,(
    ! [X8,X9,X10] :
      ( ( ~ v1_xboole_0(X8)
        | ~ r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_1(X10),X10)
        | v1_xboole_0(X10) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_27,plain,(
    ! [X18,X19,X21,X22,X23] :
      ( ( r2_hidden(esk3_2(X18,X19),X18)
        | r1_xboole_0(X18,X19) )
      & ( r2_hidden(esk3_2(X18,X19),X19)
        | r1_xboole_0(X18,X19) )
      & ( ~ r2_hidden(X23,X21)
        | ~ r2_hidden(X23,X22)
        | ~ r1_xboole_0(X21,X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_28,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_30,plain,(
    ! [X26] : r1_tarski(k1_xboole_0,X26) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_31,plain,(
    ! [X32,X33] :
      ( ( ~ m1_subset_1(X32,k1_zfmisc_1(X33))
        | r1_tarski(X32,X33) )
      & ( ~ r1_tarski(X32,X33)
        | m1_subset_1(X32,k1_zfmisc_1(X33)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_32,plain,
    ( r2_hidden(k2_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk10_0),k2_zfmisc_1(esk7_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_34,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k6_mcart_1(X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_23,c_0_17])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(esk10_0,k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0)) ),
    inference(rw,[status(thm)],[c_0_24,c_0_17])).

cnf(c_0_36,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k5_mcart_1(X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(X4))
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_25,c_0_17])).

cnf(c_0_37,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_38,plain,
    ( r2_hidden(esk3_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_39,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,k4_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_40,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_41,plain,(
    ! [X12,X13,X14,X15,X16] :
      ( ( ~ r1_tarski(X12,X13)
        | ~ r2_hidden(X14,X12)
        | r2_hidden(X14,X13) )
      & ( r2_hidden(esk2_2(X15,X16),X15)
        | r1_tarski(X15,X16) )
      & ( ~ r2_hidden(esk2_2(X15,X16),X16)
        | r1_tarski(X15,X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(esk10_0)),esk8_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_45,negated_conjecture,
    ( k2_mcart_1(k1_mcart_1(esk10_0)) = k6_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0)
    | esk6_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(esk10_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_33])).

cnf(c_0_47,negated_conjecture,
    ( k1_mcart_1(k1_mcart_1(esk10_0)) = k5_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0)
    | esk6_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_36,c_0_35])).

cnf(c_0_48,plain,
    ( k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_49,plain,
    ( r1_xboole_0(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_50,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_40])])).

cnf(c_0_51,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(esk7_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

fof(c_0_53,plain,(
    ! [X24,X25] :
      ( ( r1_tarski(X24,X25)
        | X24 != X25 )
      & ( r1_tarski(X25,X24)
        | X24 != X25 )
      & ( ~ r1_tarski(X24,X25)
        | ~ r1_tarski(X25,X24)
        | X24 = X25 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_54,negated_conjecture,
    ( ~ r2_hidden(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0),esk7_0)
    | ~ r2_hidden(k6_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0),esk8_0)
    | ~ r2_hidden(k7_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0),esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_55,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | r2_hidden(k6_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_56,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | r2_hidden(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_57,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4)
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_48,c_0_17])).

cnf(c_0_58,plain,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_59,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(k2_mcart_1(esk10_0),esk9_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_22])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_62,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_63,negated_conjecture,
    ( ~ v1_xboole_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_46])).

cnf(c_0_64,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_65,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | ~ r2_hidden(k7_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0),esk9_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56])).

cnf(c_0_66,negated_conjecture,
    ( k7_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0) = k2_mcart_1(esk10_0)
    | esk6_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_57,c_0_35])).

cnf(c_0_67,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,k1_xboole_0)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_58])).

cnf(c_0_68,negated_conjecture,
    ( r1_tarski(esk9_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_59])).

cnf(c_0_69,negated_conjecture,
    ( ~ v1_xboole_0(esk9_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_60])).

cnf(c_0_70,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_71,negated_conjecture,
    ( r2_hidden(esk1_1(esk7_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63])).

cnf(c_0_72,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_64])).

cnf(c_0_73,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_60])])).

cnf(c_0_74,negated_conjecture,
    ( ~ r1_tarski(esk9_0,k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_69])).

cnf(c_0_75,negated_conjecture,
    ( r1_tarski(esk8_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_70])).

cnf(c_0_76,negated_conjecture,
    ( ~ v1_xboole_0(esk8_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_44])).

cnf(c_0_77,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_71])).

cnf(c_0_78,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_67,c_0_72])).

cnf(c_0_79,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_73]),c_0_74])).

cnf(c_0_80,negated_conjecture,
    ( ~ r1_tarski(esk8_0,k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_75]),c_0_76])).

cnf(c_0_81,negated_conjecture,
    ( ~ r1_tarski(esk4_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_82,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_79]),c_0_80])).

cnf(c_0_83,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_82]),c_0_40])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:05:46 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.20/0.35  # No SInE strategy applied
% 0.20/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.40  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.20/0.40  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.40  #
% 0.20/0.40  # Preprocessing time       : 0.028 s
% 0.20/0.40  
% 0.20/0.40  # Proof found!
% 0.20/0.40  # SZS status Theorem
% 0.20/0.40  # SZS output start CNFRefutation
% 0.20/0.40  fof(t76_mcart_1, conjecture, ![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(X1))=>![X5]:(m1_subset_1(X5,k1_zfmisc_1(X2))=>![X6]:(m1_subset_1(X6,k1_zfmisc_1(X3))=>![X7]:(m1_subset_1(X7,k3_zfmisc_1(X1,X2,X3))=>(r2_hidden(X7,k3_zfmisc_1(X4,X5,X6))=>((r2_hidden(k5_mcart_1(X1,X2,X3,X7),X4)&r2_hidden(k6_mcart_1(X1,X2,X3,X7),X5))&r2_hidden(k7_mcart_1(X1,X2,X3,X7),X6))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_mcart_1)).
% 0.20/0.40  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 0.20/0.40  fof(t10_mcart_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(X2,X3))=>(r2_hidden(k1_mcart_1(X1),X2)&r2_hidden(k2_mcart_1(X1),X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 0.20/0.40  fof(t50_mcart_1, axiom, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>((k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))&k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4)))&k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_mcart_1)).
% 0.20/0.40  fof(t68_xboole_1, axiom, ![X1, X2, X3]:(~(v1_xboole_0(X3))=>~(((r1_tarski(X3,X1)&r1_tarski(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_xboole_1)).
% 0.20/0.40  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 0.20/0.40  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.20/0.40  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.20/0.40  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.20/0.40  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.40  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.40  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.40  fof(c_0_12, negated_conjecture, ~(![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(X1))=>![X5]:(m1_subset_1(X5,k1_zfmisc_1(X2))=>![X6]:(m1_subset_1(X6,k1_zfmisc_1(X3))=>![X7]:(m1_subset_1(X7,k3_zfmisc_1(X1,X2,X3))=>(r2_hidden(X7,k3_zfmisc_1(X4,X5,X6))=>((r2_hidden(k5_mcart_1(X1,X2,X3,X7),X4)&r2_hidden(k6_mcart_1(X1,X2,X3,X7),X5))&r2_hidden(k7_mcart_1(X1,X2,X3,X7),X6)))))))), inference(assume_negation,[status(cth)],[t76_mcart_1])).
% 0.20/0.40  fof(c_0_13, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(esk4_0))&(m1_subset_1(esk8_0,k1_zfmisc_1(esk5_0))&(m1_subset_1(esk9_0,k1_zfmisc_1(esk6_0))&(m1_subset_1(esk10_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0))&(r2_hidden(esk10_0,k3_zfmisc_1(esk7_0,esk8_0,esk9_0))&(~r2_hidden(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0),esk7_0)|~r2_hidden(k6_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0),esk8_0)|~r2_hidden(k7_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0),esk9_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 0.20/0.40  fof(c_0_14, plain, ![X34, X35, X36]:k3_zfmisc_1(X34,X35,X36)=k2_zfmisc_1(k2_zfmisc_1(X34,X35),X36), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 0.20/0.40  fof(c_0_15, plain, ![X37, X38, X39]:((r2_hidden(k1_mcart_1(X37),X38)|~r2_hidden(X37,k2_zfmisc_1(X38,X39)))&(r2_hidden(k2_mcart_1(X37),X39)|~r2_hidden(X37,k2_zfmisc_1(X38,X39)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).
% 0.20/0.40  cnf(c_0_16, negated_conjecture, (r2_hidden(esk10_0,k3_zfmisc_1(esk7_0,esk8_0,esk9_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.40  cnf(c_0_17, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.40  fof(c_0_18, plain, ![X40, X41, X42, X43]:(((k5_mcart_1(X40,X41,X42,X43)=k1_mcart_1(k1_mcart_1(X43))|~m1_subset_1(X43,k3_zfmisc_1(X40,X41,X42))|(X40=k1_xboole_0|X41=k1_xboole_0|X42=k1_xboole_0))&(k6_mcart_1(X40,X41,X42,X43)=k2_mcart_1(k1_mcart_1(X43))|~m1_subset_1(X43,k3_zfmisc_1(X40,X41,X42))|(X40=k1_xboole_0|X41=k1_xboole_0|X42=k1_xboole_0)))&(k7_mcart_1(X40,X41,X42,X43)=k2_mcart_1(X43)|~m1_subset_1(X43,k3_zfmisc_1(X40,X41,X42))|(X40=k1_xboole_0|X41=k1_xboole_0|X42=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_mcart_1])])])])).
% 0.20/0.40  fof(c_0_19, plain, ![X27, X28, X29]:(v1_xboole_0(X29)|(~r1_tarski(X29,X27)|~r1_tarski(X29,X28)|~r1_xboole_0(X27,X28))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t68_xboole_1])])])).
% 0.20/0.40  fof(c_0_20, plain, ![X30, X31]:r1_xboole_0(k4_xboole_0(X30,X31),X31), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 0.20/0.40  cnf(c_0_21, plain, (r2_hidden(k1_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.40  cnf(c_0_22, negated_conjecture, (r2_hidden(esk10_0,k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),esk9_0))), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 0.20/0.40  cnf(c_0_23, plain, (k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4))|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.40  cnf(c_0_24, negated_conjecture, (m1_subset_1(esk10_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.40  cnf(c_0_25, plain, (k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.40  fof(c_0_26, plain, ![X8, X9, X10]:((~v1_xboole_0(X8)|~r2_hidden(X9,X8))&(r2_hidden(esk1_1(X10),X10)|v1_xboole_0(X10))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.20/0.40  fof(c_0_27, plain, ![X18, X19, X21, X22, X23]:(((r2_hidden(esk3_2(X18,X19),X18)|r1_xboole_0(X18,X19))&(r2_hidden(esk3_2(X18,X19),X19)|r1_xboole_0(X18,X19)))&(~r2_hidden(X23,X21)|~r2_hidden(X23,X22)|~r1_xboole_0(X21,X22))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.20/0.40  cnf(c_0_28, plain, (v1_xboole_0(X1)|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.40  cnf(c_0_29, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.40  fof(c_0_30, plain, ![X26]:r1_tarski(k1_xboole_0,X26), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.20/0.40  fof(c_0_31, plain, ![X32, X33]:((~m1_subset_1(X32,k1_zfmisc_1(X33))|r1_tarski(X32,X33))&(~r1_tarski(X32,X33)|m1_subset_1(X32,k1_zfmisc_1(X33)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.40  cnf(c_0_32, plain, (r2_hidden(k2_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.40  cnf(c_0_33, negated_conjecture, (r2_hidden(k1_mcart_1(esk10_0),k2_zfmisc_1(esk7_0,esk8_0))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.20/0.40  cnf(c_0_34, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4))|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_23, c_0_17])).
% 0.20/0.40  cnf(c_0_35, negated_conjecture, (m1_subset_1(esk10_0,k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0))), inference(rw,[status(thm)],[c_0_24, c_0_17])).
% 0.20/0.40  cnf(c_0_36, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_25, c_0_17])).
% 0.20/0.40  cnf(c_0_37, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.40  cnf(c_0_38, plain, (r2_hidden(esk3_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.40  cnf(c_0_39, plain, (v1_xboole_0(X1)|~r1_tarski(X1,k4_xboole_0(X2,X3))|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.20/0.40  cnf(c_0_40, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.40  fof(c_0_41, plain, ![X12, X13, X14, X15, X16]:((~r1_tarski(X12,X13)|(~r2_hidden(X14,X12)|r2_hidden(X14,X13)))&((r2_hidden(esk2_2(X15,X16),X15)|r1_tarski(X15,X16))&(~r2_hidden(esk2_2(X15,X16),X16)|r1_tarski(X15,X16)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.40  cnf(c_0_42, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.40  cnf(c_0_43, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.40  cnf(c_0_44, negated_conjecture, (r2_hidden(k2_mcart_1(k1_mcart_1(esk10_0)),esk8_0)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.20/0.40  cnf(c_0_45, negated_conjecture, (k2_mcart_1(k1_mcart_1(esk10_0))=k6_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0)|esk6_0=k1_xboole_0|esk5_0=k1_xboole_0|esk4_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.20/0.40  cnf(c_0_46, negated_conjecture, (r2_hidden(k1_mcart_1(k1_mcart_1(esk10_0)),esk7_0)), inference(spm,[status(thm)],[c_0_21, c_0_33])).
% 0.20/0.40  cnf(c_0_47, negated_conjecture, (k1_mcart_1(k1_mcart_1(esk10_0))=k5_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0)|esk6_0=k1_xboole_0|esk5_0=k1_xboole_0|esk4_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_36, c_0_35])).
% 0.20/0.40  cnf(c_0_48, plain, (k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.40  cnf(c_0_49, plain, (r1_xboole_0(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.20/0.40  cnf(c_0_50, plain, (v1_xboole_0(k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_40])])).
% 0.20/0.40  cnf(c_0_51, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.20/0.40  cnf(c_0_52, negated_conjecture, (r1_tarski(esk7_0,esk4_0)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.20/0.40  fof(c_0_53, plain, ![X24, X25]:(((r1_tarski(X24,X25)|X24!=X25)&(r1_tarski(X25,X24)|X24!=X25))&(~r1_tarski(X24,X25)|~r1_tarski(X25,X24)|X24=X25)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.40  cnf(c_0_54, negated_conjecture, (~r2_hidden(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0),esk7_0)|~r2_hidden(k6_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0),esk8_0)|~r2_hidden(k7_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0),esk9_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.40  cnf(c_0_55, negated_conjecture, (esk4_0=k1_xboole_0|esk5_0=k1_xboole_0|esk6_0=k1_xboole_0|r2_hidden(k6_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0),esk8_0)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.20/0.40  cnf(c_0_56, negated_conjecture, (esk4_0=k1_xboole_0|esk5_0=k1_xboole_0|esk6_0=k1_xboole_0|r2_hidden(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0),esk7_0)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.20/0.40  cnf(c_0_57, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_48, c_0_17])).
% 0.20/0.40  cnf(c_0_58, plain, (r1_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.20/0.40  cnf(c_0_59, negated_conjecture, (m1_subset_1(esk9_0,k1_zfmisc_1(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.40  cnf(c_0_60, negated_conjecture, (r2_hidden(k2_mcart_1(esk10_0),esk9_0)), inference(spm,[status(thm)],[c_0_32, c_0_22])).
% 0.20/0.40  cnf(c_0_61, negated_conjecture, (r2_hidden(X1,esk4_0)|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.20/0.40  cnf(c_0_62, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.40  cnf(c_0_63, negated_conjecture, (~v1_xboole_0(esk7_0)), inference(spm,[status(thm)],[c_0_37, c_0_46])).
% 0.20/0.40  cnf(c_0_64, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.20/0.40  cnf(c_0_65, negated_conjecture, (esk6_0=k1_xboole_0|esk5_0=k1_xboole_0|esk4_0=k1_xboole_0|~r2_hidden(k7_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0),esk9_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56])).
% 0.20/0.40  cnf(c_0_66, negated_conjecture, (k7_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0)=k2_mcart_1(esk10_0)|esk6_0=k1_xboole_0|esk5_0=k1_xboole_0|esk4_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_57, c_0_35])).
% 0.20/0.40  cnf(c_0_67, plain, (v1_xboole_0(X1)|~r1_tarski(X1,k1_xboole_0)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_28, c_0_58])).
% 0.20/0.40  cnf(c_0_68, negated_conjecture, (r1_tarski(esk9_0,esk6_0)), inference(spm,[status(thm)],[c_0_42, c_0_59])).
% 0.20/0.40  cnf(c_0_69, negated_conjecture, (~v1_xboole_0(esk9_0)), inference(spm,[status(thm)],[c_0_37, c_0_60])).
% 0.20/0.40  cnf(c_0_70, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.40  cnf(c_0_71, negated_conjecture, (r2_hidden(esk1_1(esk7_0),esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_63])).
% 0.20/0.40  cnf(c_0_72, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_64])).
% 0.20/0.40  cnf(c_0_73, negated_conjecture, (esk4_0=k1_xboole_0|esk5_0=k1_xboole_0|esk6_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_60])])).
% 0.20/0.40  cnf(c_0_74, negated_conjecture, (~r1_tarski(esk9_0,k1_xboole_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_69])).
% 0.20/0.40  cnf(c_0_75, negated_conjecture, (r1_tarski(esk8_0,esk5_0)), inference(spm,[status(thm)],[c_0_42, c_0_70])).
% 0.20/0.40  cnf(c_0_76, negated_conjecture, (~v1_xboole_0(esk8_0)), inference(spm,[status(thm)],[c_0_37, c_0_44])).
% 0.20/0.40  cnf(c_0_77, negated_conjecture, (~v1_xboole_0(esk4_0)), inference(spm,[status(thm)],[c_0_37, c_0_71])).
% 0.20/0.40  cnf(c_0_78, plain, (v1_xboole_0(X1)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_67, c_0_72])).
% 0.20/0.40  cnf(c_0_79, negated_conjecture, (esk5_0=k1_xboole_0|esk4_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_73]), c_0_74])).
% 0.20/0.40  cnf(c_0_80, negated_conjecture, (~r1_tarski(esk8_0,k1_xboole_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_75]), c_0_76])).
% 0.20/0.40  cnf(c_0_81, negated_conjecture, (~r1_tarski(esk4_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 0.20/0.40  cnf(c_0_82, negated_conjecture, (esk4_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_79]), c_0_80])).
% 0.20/0.40  cnf(c_0_83, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81, c_0_82]), c_0_40])]), ['proof']).
% 0.20/0.40  # SZS output end CNFRefutation
% 0.20/0.40  # Proof object total steps             : 84
% 0.20/0.40  # Proof object clause steps            : 59
% 0.20/0.40  # Proof object formula steps           : 25
% 0.20/0.40  # Proof object conjectures             : 37
% 0.20/0.40  # Proof object clause conjectures      : 34
% 0.20/0.40  # Proof object formula conjectures     : 3
% 0.20/0.40  # Proof object initial clauses used    : 21
% 0.20/0.40  # Proof object initial formulas used   : 12
% 0.20/0.40  # Proof object generating inferences   : 31
% 0.20/0.40  # Proof object simplifying inferences  : 19
% 0.20/0.40  # Training examples: 0 positive, 0 negative
% 0.20/0.40  # Parsed axioms                        : 12
% 0.20/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.40  # Initial clauses                      : 28
% 0.20/0.40  # Removed in clause preprocessing      : 1
% 0.20/0.40  # Initial clauses in saturation        : 27
% 0.20/0.40  # Processed clauses                    : 438
% 0.20/0.40  # ...of these trivial                  : 7
% 0.20/0.40  # ...subsumed                          : 229
% 0.20/0.40  # ...remaining for further processing  : 202
% 0.20/0.40  # Other redundant clauses eliminated   : 2
% 0.20/0.40  # Clauses deleted for lack of memory   : 0
% 0.20/0.40  # Backward-subsumed                    : 14
% 0.20/0.40  # Backward-rewritten                   : 27
% 0.20/0.40  # Generated clauses                    : 1849
% 0.20/0.40  # ...of the previous two non-trivial   : 841
% 0.20/0.40  # Contextual simplify-reflections      : 5
% 0.20/0.40  # Paramodulations                      : 1847
% 0.20/0.40  # Factorizations                       : 0
% 0.20/0.40  # Equation resolutions                 : 2
% 0.20/0.40  # Propositional unsat checks           : 0
% 0.20/0.40  #    Propositional check models        : 0
% 0.20/0.40  #    Propositional check unsatisfiable : 0
% 0.20/0.40  #    Propositional clauses             : 0
% 0.20/0.40  #    Propositional clauses after purity: 0
% 0.20/0.40  #    Propositional unsat core size     : 0
% 0.20/0.40  #    Propositional preprocessing time  : 0.000
% 0.20/0.40  #    Propositional encoding time       : 0.000
% 0.20/0.40  #    Propositional solver time         : 0.000
% 0.20/0.40  #    Success case prop preproc time    : 0.000
% 0.20/0.40  #    Success case prop encoding time   : 0.000
% 0.20/0.40  #    Success case prop solver time     : 0.000
% 0.20/0.40  # Current number of processed clauses  : 159
% 0.20/0.40  #    Positive orientable unit clauses  : 27
% 0.20/0.40  #    Positive unorientable unit clauses: 0
% 0.20/0.40  #    Negative unit clauses             : 15
% 0.20/0.40  #    Non-unit-clauses                  : 117
% 0.20/0.40  # Current number of unprocessed clauses: 410
% 0.20/0.40  # ...number of literals in the above   : 1310
% 0.20/0.40  # Current number of archived formulas  : 0
% 0.20/0.40  # Current number of archived clauses   : 42
% 0.20/0.40  # Clause-clause subsumption calls (NU) : 1714
% 0.20/0.40  # Rec. Clause-clause subsumption calls : 1450
% 0.20/0.40  # Non-unit clause-clause subsumptions  : 91
% 0.20/0.40  # Unit Clause-clause subsumption calls : 174
% 0.20/0.40  # Rewrite failures with RHS unbound    : 0
% 0.20/0.40  # BW rewrite match attempts            : 12
% 0.20/0.40  # BW rewrite match successes           : 3
% 0.20/0.40  # Condensation attempts                : 0
% 0.20/0.40  # Condensation successes               : 0
% 0.20/0.40  # Termbank termtop insertions          : 18868
% 0.20/0.40  
% 0.20/0.40  # -------------------------------------------------
% 0.20/0.40  # User time                : 0.051 s
% 0.20/0.40  # System time              : 0.005 s
% 0.20/0.40  # Total time               : 0.056 s
% 0.20/0.40  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
