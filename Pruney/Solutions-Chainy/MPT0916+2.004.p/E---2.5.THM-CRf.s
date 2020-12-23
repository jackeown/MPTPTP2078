%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:21 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 384 expanded)
%              Number of clauses        :   79 ( 180 expanded)
%              Number of leaves         :   15 (  94 expanded)
%              Depth                    :   13
%              Number of atoms          :  269 (1106 expanded)
%              Number of equality atoms :   85 ( 164 expanded)
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

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

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

fof(t63_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X2,X3) )
     => r1_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t69_xboole_1,axiom,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ~ ( r1_tarski(X2,X1)
          & r1_xboole_0(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

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

fof(c_0_15,negated_conjecture,(
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

fof(c_0_16,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(esk4_0))
    & m1_subset_1(esk8_0,k1_zfmisc_1(esk5_0))
    & m1_subset_1(esk9_0,k1_zfmisc_1(esk6_0))
    & m1_subset_1(esk10_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0))
    & r2_hidden(esk10_0,k3_zfmisc_1(esk7_0,esk8_0,esk9_0))
    & ( ~ r2_hidden(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0),esk7_0)
      | ~ r2_hidden(k6_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0),esk8_0)
      | ~ r2_hidden(k7_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0),esk9_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

fof(c_0_17,plain,(
    ! [X51,X52,X53] : k3_zfmisc_1(X51,X52,X53) = k2_zfmisc_1(k2_zfmisc_1(X51,X52),X53) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_18,plain,(
    ! [X43,X44] :
      ( ( ~ m1_subset_1(X43,k1_zfmisc_1(X44))
        | r1_tarski(X43,X44) )
      & ( ~ r1_tarski(X43,X44)
        | m1_subset_1(X43,k1_zfmisc_1(X44)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_19,plain,(
    ! [X54,X55,X56] :
      ( ( r2_hidden(k1_mcart_1(X54),X55)
        | ~ r2_hidden(X54,k2_zfmisc_1(X55,X56)) )
      & ( r2_hidden(k2_mcart_1(X54),X56)
        | ~ r2_hidden(X54,k2_zfmisc_1(X55,X56)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(esk10_0,k3_zfmisc_1(esk7_0,esk8_0,esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_22,plain,(
    ! [X57,X58,X59,X60] :
      ( ( k5_mcart_1(X57,X58,X59,X60) = k1_mcart_1(k1_mcart_1(X60))
        | ~ m1_subset_1(X60,k3_zfmisc_1(X57,X58,X59))
        | X57 = k1_xboole_0
        | X58 = k1_xboole_0
        | X59 = k1_xboole_0 )
      & ( k6_mcart_1(X57,X58,X59,X60) = k2_mcart_1(k1_mcart_1(X60))
        | ~ m1_subset_1(X60,k3_zfmisc_1(X57,X58,X59))
        | X57 = k1_xboole_0
        | X58 = k1_xboole_0
        | X59 = k1_xboole_0 )
      & ( k7_mcart_1(X57,X58,X59,X60) = k2_mcart_1(X60)
        | ~ m1_subset_1(X60,k3_zfmisc_1(X57,X58,X59))
        | X57 = k1_xboole_0
        | X58 = k1_xboole_0
        | X59 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_mcart_1])])])])).

fof(c_0_23,plain,(
    ! [X31,X32,X33] :
      ( ~ r1_tarski(X31,X32)
      | ~ r1_xboole_0(X32,X33)
      | r1_xboole_0(X31,X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_26,plain,(
    ! [X18,X19] :
      ( ~ r1_xboole_0(X18,X19)
      | r1_xboole_0(X19,X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

fof(c_0_27,plain,(
    ! [X36,X37] : r1_xboole_0(k4_xboole_0(X36,X37),X37) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

cnf(c_0_28,plain,
    ( r2_hidden(k1_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk10_0,k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),esk9_0)) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_30,plain,
    ( k5_mcart_1(X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(X4))
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk10_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_33,plain,
    ( r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(esk7_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_35,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk10_0),k2_zfmisc_1(esk7_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_38,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k5_mcart_1(X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(X4))
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_30,c_0_21])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(esk10_0,k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0)) ),
    inference(rw,[status(thm)],[c_0_31,c_0_21])).

cnf(c_0_40,plain,
    ( k6_mcart_1(X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_41,negated_conjecture,
    ( r1_tarski(esk9_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_32])).

fof(c_0_42,plain,(
    ! [X28] : r1_tarski(k1_xboole_0,X28) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_43,negated_conjecture,
    ( r1_xboole_0(esk7_0,X1)
    | ~ r1_xboole_0(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_44,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(esk10_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_37])).

cnf(c_0_46,negated_conjecture,
    ( k1_mcart_1(k1_mcart_1(esk10_0)) = k5_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0)
    | esk4_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_47,plain,
    ( r2_hidden(k2_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_48,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k6_mcart_1(X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_40,c_0_21])).

cnf(c_0_49,negated_conjecture,
    ( r1_xboole_0(esk9_0,X1)
    | ~ r1_xboole_0(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_41])).

cnf(c_0_50,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_51,negated_conjecture,
    ( r1_xboole_0(esk7_0,k4_xboole_0(X1,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_52,negated_conjecture,
    ( ~ r2_hidden(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0),esk7_0)
    | ~ r2_hidden(k6_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0),esk8_0)
    | ~ r2_hidden(k7_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0),esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_53,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | r2_hidden(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(esk10_0)),esk8_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_37])).

cnf(c_0_55,negated_conjecture,
    ( k2_mcart_1(k1_mcart_1(esk10_0)) = k6_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0)
    | esk4_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_48,c_0_39])).

cnf(c_0_56,plain,
    ( k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_57,plain,(
    ! [X20,X21,X23,X24,X25] :
      ( ( r1_xboole_0(X20,X21)
        | r2_hidden(esk3_2(X20,X21),k3_xboole_0(X20,X21)) )
      & ( ~ r2_hidden(X25,k3_xboole_0(X23,X24))
        | ~ r1_xboole_0(X23,X24) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_58,plain,(
    ! [X29,X30] : k4_xboole_0(X29,k4_xboole_0(X29,X30)) = k3_xboole_0(X29,X30) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_59,negated_conjecture,
    ( r1_xboole_0(esk9_0,k4_xboole_0(X1,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_44])).

cnf(c_0_60,plain,
    ( r1_xboole_0(k1_xboole_0,X1)
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_50])).

fof(c_0_61,plain,(
    ! [X34,X35] :
      ( v1_xboole_0(X35)
      | ~ r1_tarski(X35,X34)
      | ~ r1_xboole_0(X35,X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_xboole_1])])])).

fof(c_0_62,plain,(
    ! [X12,X13,X14,X15,X16] :
      ( ( ~ r1_tarski(X12,X13)
        | ~ r2_hidden(X14,X12)
        | r2_hidden(X14,X13) )
      & ( r2_hidden(esk2_2(X15,X16),X15)
        | r1_tarski(X15,X16) )
      & ( ~ r2_hidden(esk2_2(X15,X16),X16)
        | r1_tarski(X15,X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_63,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(X1,esk4_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_51])).

fof(c_0_64,plain,(
    ! [X8,X9,X10] :
      ( ( ~ v1_xboole_0(X8)
        | ~ r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_1(X10),X10)
        | v1_xboole_0(X10) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_65,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | ~ r2_hidden(k6_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0),esk8_0)
    | ~ r2_hidden(k7_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0),esk9_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_66,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | r2_hidden(k6_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_67,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4)
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_56,c_0_21])).

cnf(c_0_68,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_69,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_70,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(X1,esk6_0),esk9_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_59])).

fof(c_0_71,plain,(
    ! [X38,X39] :
      ( ( ~ r1_xboole_0(X38,X39)
        | k4_xboole_0(X38,X39) = X38 )
      & ( k4_xboole_0(X38,X39) != X38
        | r1_xboole_0(X38,X39) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

cnf(c_0_72,plain,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_60,c_0_36])).

cnf(c_0_73,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk3_2(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_74,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_75,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_76,negated_conjecture,
    ( r1_xboole_0(k1_xboole_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_63])).

cnf(c_0_77,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_78,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_79,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | ~ r2_hidden(k7_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0),esk9_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_80,negated_conjecture,
    ( k7_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0) = k2_mcart_1(esk10_0)
    | esk4_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_67,c_0_39])).

cnf(c_0_81,negated_conjecture,
    ( r2_hidden(k2_mcart_1(esk10_0),esk9_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_29])).

cnf(c_0_82,plain,
    ( ~ r1_xboole_0(X2,X3)
    | ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_83,negated_conjecture,
    ( r1_xboole_0(k1_xboole_0,esk9_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_70])).

cnf(c_0_84,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_85,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_72])).

cnf(c_0_86,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk3_2(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_73,c_0_69])).

cnf(c_0_87,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_88,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | v1_xboole_0(X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_89,negated_conjecture,
    ( r1_xboole_0(esk7_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_76])).

cnf(c_0_90,negated_conjecture,
    ( ~ v1_xboole_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_77,c_0_45])).

cnf(c_0_91,negated_conjecture,
    ( r1_tarski(esk8_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_78])).

cnf(c_0_92,negated_conjecture,
    ( v1_xboole_0(esk9_0)
    | ~ r1_xboole_0(esk9_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_74,c_0_41])).

cnf(c_0_93,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_81])])).

cnf(c_0_94,negated_conjecture,
    ( ~ v1_xboole_0(esk9_0) ),
    inference(spm,[status(thm)],[c_0_77,c_0_81])).

cnf(c_0_95,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,esk9_0))) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_96,negated_conjecture,
    ( k4_xboole_0(k1_xboole_0,esk9_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_84,c_0_83])).

cnf(c_0_97,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_82,c_0_85])).

cnf(c_0_98,plain,
    ( k4_xboole_0(X1,X2) = X1
    | r2_hidden(esk3_2(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_84,c_0_86])).

cnf(c_0_99,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_87,c_0_34])).

cnf(c_0_100,negated_conjecture,
    ( r2_hidden(esk2_2(esk7_0,k1_xboole_0),esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_90])).

cnf(c_0_101,negated_conjecture,
    ( v1_xboole_0(esk8_0)
    | ~ r1_xboole_0(esk8_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_74,c_0_91])).

cnf(c_0_102,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_85])]),c_0_94])).

cnf(c_0_103,negated_conjecture,
    ( ~ v1_xboole_0(esk8_0) ),
    inference(spm,[status(thm)],[c_0_77,c_0_54])).

cnf(c_0_104,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(rw,[status(thm)],[c_0_95,c_0_96])).

cnf(c_0_105,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(spm,[status(thm)],[c_0_97,c_0_98])).

cnf(c_0_106,negated_conjecture,
    ( r2_hidden(esk2_2(esk7_0,k1_xboole_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_99,c_0_100])).

cnf(c_0_107,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_102]),c_0_85])]),c_0_103])).

cnf(c_0_108,negated_conjecture,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_104,c_0_105])).

cnf(c_0_109,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_106,c_0_107]),c_0_108]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 21:02:30 EST 2020
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
% 0.13/0.40  fof(t76_mcart_1, conjecture, ![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(X1))=>![X5]:(m1_subset_1(X5,k1_zfmisc_1(X2))=>![X6]:(m1_subset_1(X6,k1_zfmisc_1(X3))=>![X7]:(m1_subset_1(X7,k3_zfmisc_1(X1,X2,X3))=>(r2_hidden(X7,k3_zfmisc_1(X4,X5,X6))=>((r2_hidden(k5_mcart_1(X1,X2,X3,X7),X4)&r2_hidden(k6_mcart_1(X1,X2,X3,X7),X5))&r2_hidden(k7_mcart_1(X1,X2,X3,X7),X6))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_mcart_1)).
% 0.13/0.40  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 0.13/0.40  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.13/0.40  fof(t10_mcart_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(X2,X3))=>(r2_hidden(k1_mcart_1(X1),X2)&r2_hidden(k2_mcart_1(X1),X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 0.13/0.40  fof(t50_mcart_1, axiom, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>((k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))&k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4)))&k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_mcart_1)).
% 0.13/0.40  fof(t63_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X2,X3))=>r1_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 0.13/0.40  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.13/0.40  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 0.13/0.40  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.13/0.40  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.13/0.40  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.13/0.40  fof(t69_xboole_1, axiom, ![X1, X2]:(~(v1_xboole_0(X2))=>~((r1_tarski(X2,X1)&r1_xboole_0(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 0.13/0.40  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.13/0.40  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.13/0.40  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.13/0.40  fof(c_0_15, negated_conjecture, ~(![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(X1))=>![X5]:(m1_subset_1(X5,k1_zfmisc_1(X2))=>![X6]:(m1_subset_1(X6,k1_zfmisc_1(X3))=>![X7]:(m1_subset_1(X7,k3_zfmisc_1(X1,X2,X3))=>(r2_hidden(X7,k3_zfmisc_1(X4,X5,X6))=>((r2_hidden(k5_mcart_1(X1,X2,X3,X7),X4)&r2_hidden(k6_mcart_1(X1,X2,X3,X7),X5))&r2_hidden(k7_mcart_1(X1,X2,X3,X7),X6)))))))), inference(assume_negation,[status(cth)],[t76_mcart_1])).
% 0.13/0.40  fof(c_0_16, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(esk4_0))&(m1_subset_1(esk8_0,k1_zfmisc_1(esk5_0))&(m1_subset_1(esk9_0,k1_zfmisc_1(esk6_0))&(m1_subset_1(esk10_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0))&(r2_hidden(esk10_0,k3_zfmisc_1(esk7_0,esk8_0,esk9_0))&(~r2_hidden(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0),esk7_0)|~r2_hidden(k6_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0),esk8_0)|~r2_hidden(k7_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0),esk9_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 0.13/0.40  fof(c_0_17, plain, ![X51, X52, X53]:k3_zfmisc_1(X51,X52,X53)=k2_zfmisc_1(k2_zfmisc_1(X51,X52),X53), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 0.13/0.40  fof(c_0_18, plain, ![X43, X44]:((~m1_subset_1(X43,k1_zfmisc_1(X44))|r1_tarski(X43,X44))&(~r1_tarski(X43,X44)|m1_subset_1(X43,k1_zfmisc_1(X44)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.13/0.40  fof(c_0_19, plain, ![X54, X55, X56]:((r2_hidden(k1_mcart_1(X54),X55)|~r2_hidden(X54,k2_zfmisc_1(X55,X56)))&(r2_hidden(k2_mcart_1(X54),X56)|~r2_hidden(X54,k2_zfmisc_1(X55,X56)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).
% 0.13/0.40  cnf(c_0_20, negated_conjecture, (r2_hidden(esk10_0,k3_zfmisc_1(esk7_0,esk8_0,esk9_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.40  cnf(c_0_21, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.40  fof(c_0_22, plain, ![X57, X58, X59, X60]:(((k5_mcart_1(X57,X58,X59,X60)=k1_mcart_1(k1_mcart_1(X60))|~m1_subset_1(X60,k3_zfmisc_1(X57,X58,X59))|(X57=k1_xboole_0|X58=k1_xboole_0|X59=k1_xboole_0))&(k6_mcart_1(X57,X58,X59,X60)=k2_mcart_1(k1_mcart_1(X60))|~m1_subset_1(X60,k3_zfmisc_1(X57,X58,X59))|(X57=k1_xboole_0|X58=k1_xboole_0|X59=k1_xboole_0)))&(k7_mcart_1(X57,X58,X59,X60)=k2_mcart_1(X60)|~m1_subset_1(X60,k3_zfmisc_1(X57,X58,X59))|(X57=k1_xboole_0|X58=k1_xboole_0|X59=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_mcart_1])])])])).
% 0.13/0.40  fof(c_0_23, plain, ![X31, X32, X33]:(~r1_tarski(X31,X32)|~r1_xboole_0(X32,X33)|r1_xboole_0(X31,X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).
% 0.13/0.40  cnf(c_0_24, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.40  cnf(c_0_25, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.40  fof(c_0_26, plain, ![X18, X19]:(~r1_xboole_0(X18,X19)|r1_xboole_0(X19,X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.13/0.40  fof(c_0_27, plain, ![X36, X37]:r1_xboole_0(k4_xboole_0(X36,X37),X37), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 0.13/0.40  cnf(c_0_28, plain, (r2_hidden(k1_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.40  cnf(c_0_29, negated_conjecture, (r2_hidden(esk10_0,k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),esk9_0))), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 0.13/0.40  cnf(c_0_30, plain, (k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.40  cnf(c_0_31, negated_conjecture, (m1_subset_1(esk10_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.40  cnf(c_0_32, negated_conjecture, (m1_subset_1(esk9_0,k1_zfmisc_1(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.40  cnf(c_0_33, plain, (r1_xboole_0(X1,X3)|~r1_tarski(X1,X2)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.40  cnf(c_0_34, negated_conjecture, (r1_tarski(esk7_0,esk4_0)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.13/0.40  cnf(c_0_35, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.40  cnf(c_0_36, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.13/0.40  cnf(c_0_37, negated_conjecture, (r2_hidden(k1_mcart_1(esk10_0),k2_zfmisc_1(esk7_0,esk8_0))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.13/0.40  cnf(c_0_38, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_30, c_0_21])).
% 0.13/0.40  cnf(c_0_39, negated_conjecture, (m1_subset_1(esk10_0,k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0))), inference(rw,[status(thm)],[c_0_31, c_0_21])).
% 0.13/0.40  cnf(c_0_40, plain, (k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4))|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.40  cnf(c_0_41, negated_conjecture, (r1_tarski(esk9_0,esk6_0)), inference(spm,[status(thm)],[c_0_24, c_0_32])).
% 0.13/0.40  fof(c_0_42, plain, ![X28]:r1_tarski(k1_xboole_0,X28), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.13/0.40  cnf(c_0_43, negated_conjecture, (r1_xboole_0(esk7_0,X1)|~r1_xboole_0(esk4_0,X1)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.13/0.40  cnf(c_0_44, plain, (r1_xboole_0(X1,k4_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.13/0.40  cnf(c_0_45, negated_conjecture, (r2_hidden(k1_mcart_1(k1_mcart_1(esk10_0)),esk7_0)), inference(spm,[status(thm)],[c_0_28, c_0_37])).
% 0.13/0.40  cnf(c_0_46, negated_conjecture, (k1_mcart_1(k1_mcart_1(esk10_0))=k5_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0)|esk4_0=k1_xboole_0|esk5_0=k1_xboole_0|esk6_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.13/0.40  cnf(c_0_47, plain, (r2_hidden(k2_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.40  cnf(c_0_48, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4))|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_40, c_0_21])).
% 0.13/0.40  cnf(c_0_49, negated_conjecture, (r1_xboole_0(esk9_0,X1)|~r1_xboole_0(esk6_0,X1)), inference(spm,[status(thm)],[c_0_33, c_0_41])).
% 0.13/0.40  cnf(c_0_50, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.13/0.40  cnf(c_0_51, negated_conjecture, (r1_xboole_0(esk7_0,k4_xboole_0(X1,esk4_0))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.13/0.40  cnf(c_0_52, negated_conjecture, (~r2_hidden(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0),esk7_0)|~r2_hidden(k6_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0),esk8_0)|~r2_hidden(k7_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0),esk9_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.40  cnf(c_0_53, negated_conjecture, (esk6_0=k1_xboole_0|esk5_0=k1_xboole_0|esk4_0=k1_xboole_0|r2_hidden(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0),esk7_0)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.13/0.40  cnf(c_0_54, negated_conjecture, (r2_hidden(k2_mcart_1(k1_mcart_1(esk10_0)),esk8_0)), inference(spm,[status(thm)],[c_0_47, c_0_37])).
% 0.13/0.40  cnf(c_0_55, negated_conjecture, (k2_mcart_1(k1_mcart_1(esk10_0))=k6_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0)|esk4_0=k1_xboole_0|esk5_0=k1_xboole_0|esk6_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_48, c_0_39])).
% 0.13/0.40  cnf(c_0_56, plain, (k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.40  fof(c_0_57, plain, ![X20, X21, X23, X24, X25]:((r1_xboole_0(X20,X21)|r2_hidden(esk3_2(X20,X21),k3_xboole_0(X20,X21)))&(~r2_hidden(X25,k3_xboole_0(X23,X24))|~r1_xboole_0(X23,X24))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.13/0.40  fof(c_0_58, plain, ![X29, X30]:k4_xboole_0(X29,k4_xboole_0(X29,X30))=k3_xboole_0(X29,X30), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.13/0.40  cnf(c_0_59, negated_conjecture, (r1_xboole_0(esk9_0,k4_xboole_0(X1,esk6_0))), inference(spm,[status(thm)],[c_0_49, c_0_44])).
% 0.13/0.40  cnf(c_0_60, plain, (r1_xboole_0(k1_xboole_0,X1)|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_33, c_0_50])).
% 0.13/0.40  fof(c_0_61, plain, ![X34, X35]:(v1_xboole_0(X35)|(~r1_tarski(X35,X34)|~r1_xboole_0(X35,X34))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_xboole_1])])])).
% 0.13/0.40  fof(c_0_62, plain, ![X12, X13, X14, X15, X16]:((~r1_tarski(X12,X13)|(~r2_hidden(X14,X12)|r2_hidden(X14,X13)))&((r2_hidden(esk2_2(X15,X16),X15)|r1_tarski(X15,X16))&(~r2_hidden(esk2_2(X15,X16),X16)|r1_tarski(X15,X16)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.13/0.40  cnf(c_0_63, negated_conjecture, (r1_xboole_0(k4_xboole_0(X1,esk4_0),esk7_0)), inference(spm,[status(thm)],[c_0_35, c_0_51])).
% 0.13/0.40  fof(c_0_64, plain, ![X8, X9, X10]:((~v1_xboole_0(X8)|~r2_hidden(X9,X8))&(r2_hidden(esk1_1(X10),X10)|v1_xboole_0(X10))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.13/0.40  cnf(c_0_65, negated_conjecture, (esk4_0=k1_xboole_0|esk5_0=k1_xboole_0|esk6_0=k1_xboole_0|~r2_hidden(k6_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0),esk8_0)|~r2_hidden(k7_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0),esk9_0)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.13/0.40  cnf(c_0_66, negated_conjecture, (esk6_0=k1_xboole_0|esk5_0=k1_xboole_0|esk4_0=k1_xboole_0|r2_hidden(k6_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0),esk8_0)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.13/0.40  cnf(c_0_67, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_56, c_0_21])).
% 0.13/0.40  cnf(c_0_68, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.13/0.40  cnf(c_0_69, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.13/0.40  cnf(c_0_70, negated_conjecture, (r1_xboole_0(k4_xboole_0(X1,esk6_0),esk9_0)), inference(spm,[status(thm)],[c_0_35, c_0_59])).
% 0.13/0.40  fof(c_0_71, plain, ![X38, X39]:((~r1_xboole_0(X38,X39)|k4_xboole_0(X38,X39)=X38)&(k4_xboole_0(X38,X39)!=X38|r1_xboole_0(X38,X39))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.13/0.40  cnf(c_0_72, plain, (r1_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_60, c_0_36])).
% 0.13/0.40  cnf(c_0_73, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk3_2(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.13/0.40  cnf(c_0_74, plain, (v1_xboole_0(X1)|~r1_tarski(X1,X2)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.13/0.40  cnf(c_0_75, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.13/0.40  cnf(c_0_76, negated_conjecture, (r1_xboole_0(k1_xboole_0,esk7_0)), inference(spm,[status(thm)],[c_0_60, c_0_63])).
% 0.13/0.40  cnf(c_0_77, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.13/0.40  cnf(c_0_78, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.40  cnf(c_0_79, negated_conjecture, (esk6_0=k1_xboole_0|esk5_0=k1_xboole_0|esk4_0=k1_xboole_0|~r2_hidden(k7_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0),esk9_0)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.13/0.40  cnf(c_0_80, negated_conjecture, (k7_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0)=k2_mcart_1(esk10_0)|esk4_0=k1_xboole_0|esk5_0=k1_xboole_0|esk6_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_67, c_0_39])).
% 0.13/0.40  cnf(c_0_81, negated_conjecture, (r2_hidden(k2_mcart_1(esk10_0),esk9_0)), inference(spm,[status(thm)],[c_0_47, c_0_29])).
% 0.13/0.40  cnf(c_0_82, plain, (~r1_xboole_0(X2,X3)|~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_68, c_0_69])).
% 0.13/0.40  cnf(c_0_83, negated_conjecture, (r1_xboole_0(k1_xboole_0,esk9_0)), inference(spm,[status(thm)],[c_0_60, c_0_70])).
% 0.13/0.40  cnf(c_0_84, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.13/0.40  cnf(c_0_85, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_35, c_0_72])).
% 0.13/0.40  cnf(c_0_86, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk3_2(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))), inference(rw,[status(thm)],[c_0_73, c_0_69])).
% 0.13/0.40  cnf(c_0_87, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.13/0.40  cnf(c_0_88, plain, (r2_hidden(esk2_2(X1,X2),X1)|v1_xboole_0(X1)|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 0.13/0.40  cnf(c_0_89, negated_conjecture, (r1_xboole_0(esk7_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_35, c_0_76])).
% 0.13/0.40  cnf(c_0_90, negated_conjecture, (~v1_xboole_0(esk7_0)), inference(spm,[status(thm)],[c_0_77, c_0_45])).
% 0.13/0.40  cnf(c_0_91, negated_conjecture, (r1_tarski(esk8_0,esk5_0)), inference(spm,[status(thm)],[c_0_24, c_0_78])).
% 0.13/0.40  cnf(c_0_92, negated_conjecture, (v1_xboole_0(esk9_0)|~r1_xboole_0(esk9_0,esk6_0)), inference(spm,[status(thm)],[c_0_74, c_0_41])).
% 0.13/0.40  cnf(c_0_93, negated_conjecture, (esk4_0=k1_xboole_0|esk5_0=k1_xboole_0|esk6_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_81])])).
% 0.13/0.40  cnf(c_0_94, negated_conjecture, (~v1_xboole_0(esk9_0)), inference(spm,[status(thm)],[c_0_77, c_0_81])).
% 0.13/0.40  cnf(c_0_95, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,esk9_0)))), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 0.13/0.40  cnf(c_0_96, negated_conjecture, (k4_xboole_0(k1_xboole_0,esk9_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_84, c_0_83])).
% 0.13/0.40  cnf(c_0_97, plain, (~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_82, c_0_85])).
% 0.13/0.40  cnf(c_0_98, plain, (k4_xboole_0(X1,X2)=X1|r2_hidden(esk3_2(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_84, c_0_86])).
% 0.13/0.40  cnf(c_0_99, negated_conjecture, (r2_hidden(X1,esk4_0)|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_87, c_0_34])).
% 0.13/0.40  cnf(c_0_100, negated_conjecture, (r2_hidden(esk2_2(esk7_0,k1_xboole_0),esk7_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_89]), c_0_90])).
% 0.13/0.40  cnf(c_0_101, negated_conjecture, (v1_xboole_0(esk8_0)|~r1_xboole_0(esk8_0,esk5_0)), inference(spm,[status(thm)],[c_0_74, c_0_91])).
% 0.13/0.40  cnf(c_0_102, negated_conjecture, (esk5_0=k1_xboole_0|esk4_0=k1_xboole_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_85])]), c_0_94])).
% 0.13/0.40  cnf(c_0_103, negated_conjecture, (~v1_xboole_0(esk8_0)), inference(spm,[status(thm)],[c_0_77, c_0_54])).
% 0.13/0.40  cnf(c_0_104, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(k1_xboole_0,k1_xboole_0))), inference(rw,[status(thm)],[c_0_95, c_0_96])).
% 0.13/0.40  cnf(c_0_105, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(spm,[status(thm)],[c_0_97, c_0_98])).
% 0.13/0.40  cnf(c_0_106, negated_conjecture, (r2_hidden(esk2_2(esk7_0,k1_xboole_0),esk4_0)), inference(spm,[status(thm)],[c_0_99, c_0_100])).
% 0.13/0.40  cnf(c_0_107, negated_conjecture, (esk4_0=k1_xboole_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_102]), c_0_85])]), c_0_103])).
% 0.13/0.40  cnf(c_0_108, negated_conjecture, (~r2_hidden(X1,k1_xboole_0)), inference(rw,[status(thm)],[c_0_104, c_0_105])).
% 0.13/0.40  cnf(c_0_109, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_106, c_0_107]), c_0_108]), ['proof']).
% 0.13/0.40  # SZS output end CNFRefutation
% 0.13/0.40  # Proof object total steps             : 110
% 0.13/0.40  # Proof object clause steps            : 79
% 0.13/0.40  # Proof object formula steps           : 31
% 0.13/0.40  # Proof object conjectures             : 50
% 0.13/0.40  # Proof object clause conjectures      : 47
% 0.13/0.40  # Proof object formula conjectures     : 3
% 0.13/0.40  # Proof object initial clauses used    : 25
% 0.13/0.40  # Proof object initial formulas used   : 15
% 0.13/0.40  # Proof object generating inferences   : 44
% 0.13/0.40  # Proof object simplifying inferences  : 20
% 0.13/0.40  # Training examples: 0 positive, 0 negative
% 0.13/0.40  # Parsed axioms                        : 20
% 0.13/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.40  # Initial clauses                      : 36
% 0.13/0.40  # Removed in clause preprocessing      : 2
% 0.13/0.40  # Initial clauses in saturation        : 34
% 0.13/0.40  # Processed clauses                    : 458
% 0.13/0.40  # ...of these trivial                  : 7
% 0.13/0.40  # ...subsumed                          : 125
% 0.13/0.40  # ...remaining for further processing  : 326
% 0.13/0.40  # Other redundant clauses eliminated   : 2
% 0.13/0.40  # Clauses deleted for lack of memory   : 0
% 0.13/0.40  # Backward-subsumed                    : 12
% 0.13/0.40  # Backward-rewritten                   : 68
% 0.13/0.40  # Generated clauses                    : 927
% 0.13/0.40  # ...of the previous two non-trivial   : 801
% 0.13/0.40  # Contextual simplify-reflections      : 0
% 0.13/0.40  # Paramodulations                      : 925
% 0.13/0.40  # Factorizations                       : 0
% 0.13/0.40  # Equation resolutions                 : 2
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
% 0.13/0.40  # Current number of processed clauses  : 211
% 0.13/0.40  #    Positive orientable unit clauses  : 102
% 0.13/0.40  #    Positive unorientable unit clauses: 0
% 0.13/0.40  #    Negative unit clauses             : 30
% 0.13/0.40  #    Non-unit-clauses                  : 79
% 0.13/0.40  # Current number of unprocessed clauses: 388
% 0.13/0.40  # ...number of literals in the above   : 727
% 0.13/0.40  # Current number of archived formulas  : 0
% 0.13/0.40  # Current number of archived clauses   : 115
% 0.13/0.40  # Clause-clause subsumption calls (NU) : 778
% 0.13/0.40  # Rec. Clause-clause subsumption calls : 605
% 0.13/0.40  # Non-unit clause-clause subsumptions  : 16
% 0.13/0.40  # Unit Clause-clause subsumption calls : 853
% 0.13/0.40  # Rewrite failures with RHS unbound    : 0
% 0.13/0.40  # BW rewrite match attempts            : 66
% 0.13/0.40  # BW rewrite match successes           : 30
% 0.13/0.40  # Condensation attempts                : 0
% 0.13/0.40  # Condensation successes               : 0
% 0.13/0.40  # Termbank termtop insertions          : 11490
% 0.13/0.40  
% 0.13/0.40  # -------------------------------------------------
% 0.13/0.40  # User time                : 0.050 s
% 0.13/0.40  # System time              : 0.007 s
% 0.13/0.40  # Total time               : 0.057 s
% 0.13/0.40  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
