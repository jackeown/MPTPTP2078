%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:22 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 881 expanded)
%              Number of clauses        :   81 ( 418 expanded)
%              Number of leaves         :   16 ( 213 expanded)
%              Depth                    :   14
%              Number of atoms          :  291 (2787 expanded)
%              Number of equality atoms :   94 ( 462 expanded)
%              Maximal formula depth    :   17 (   4 average)
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

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t63_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X2,X3) )
     => r1_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t106_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k4_xboole_0(X2,X3))
     => ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

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

fof(t6_mcart_1,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] :
            ~ ( r2_hidden(X2,X1)
              & ! [X3,X4,X5,X6,X7] :
                  ( ( r2_hidden(X3,X4)
                    & r2_hidden(X4,X5)
                    & r2_hidden(X5,X6)
                    & r2_hidden(X6,X7)
                    & r2_hidden(X7,X2) )
                 => r1_xboole_0(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_mcart_1)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(c_0_16,negated_conjecture,(
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

fof(c_0_17,plain,(
    ! [X35,X36] :
      ( ( ~ m1_subset_1(X35,k1_zfmisc_1(X36))
        | r1_tarski(X35,X36) )
      & ( ~ r1_tarski(X35,X36)
        | m1_subset_1(X35,k1_zfmisc_1(X36)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_18,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(esk4_0))
    & m1_subset_1(esk8_0,k1_zfmisc_1(esk5_0))
    & m1_subset_1(esk9_0,k1_zfmisc_1(esk6_0))
    & m1_subset_1(esk10_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0))
    & r2_hidden(esk10_0,k3_zfmisc_1(esk7_0,esk8_0,esk9_0))
    & ( ~ r2_hidden(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0),esk7_0)
      | ~ r2_hidden(k6_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0),esk8_0)
      | ~ r2_hidden(k7_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0),esk9_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

fof(c_0_19,plain,(
    ! [X20,X21] :
      ( ( r1_tarski(X20,X21)
        | X20 != X21 )
      & ( r1_tarski(X21,X20)
        | X20 != X21 )
      & ( ~ r1_tarski(X20,X21)
        | ~ r1_tarski(X21,X20)
        | X20 = X21 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_20,plain,(
    ! [X27,X28,X29] :
      ( ~ r1_tarski(X27,X28)
      | ~ r1_xboole_0(X28,X29)
      | r1_xboole_0(X27,X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).

cnf(c_0_21,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_23,plain,(
    ! [X37,X38,X39] : k3_zfmisc_1(X37,X38,X39) = k2_zfmisc_1(k2_zfmisc_1(X37,X38),X39) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_24,plain,(
    ! [X14,X15,X17,X18,X19] :
      ( ( r1_xboole_0(X14,X15)
        | r2_hidden(esk2_2(X14,X15),k3_xboole_0(X14,X15)) )
      & ( ~ r2_hidden(X19,k3_xboole_0(X17,X18))
        | ~ r1_xboole_0(X17,X18) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_25,plain,(
    ! [X25,X26] :
      ( ~ r1_tarski(X25,X26)
      | k3_xboole_0(X25,X26) = X25 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_26,plain,(
    ! [X22,X23,X24] :
      ( ( r1_tarski(X22,X23)
        | ~ r1_tarski(X22,k4_xboole_0(X23,X24)) )
      & ( r1_xboole_0(X22,X24)
        | ~ r1_tarski(X22,k4_xboole_0(X23,X24)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_28,plain,(
    ! [X12,X13] :
      ( ~ r1_xboole_0(X12,X13)
      | r1_xboole_0(X13,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_29,plain,
    ( r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,negated_conjecture,
    ( r1_tarski(esk9_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

fof(c_0_31,plain,(
    ! [X31,X32] : r1_xboole_0(k4_xboole_0(X31,X32),X32) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

fof(c_0_32,plain,(
    ! [X8,X9,X10] :
      ( ( ~ v1_xboole_0(X8)
        | ~ r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_1(X10),X10)
        | v1_xboole_0(X10) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_34,plain,(
    ! [X40,X41,X42] :
      ( ( r2_hidden(k1_mcart_1(X40),X41)
        | ~ r2_hidden(X40,k2_zfmisc_1(X41,X42)) )
      & ( r2_hidden(k2_mcart_1(X40),X42)
        | ~ r2_hidden(X40,k2_zfmisc_1(X41,X42)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk10_0,k3_zfmisc_1(esk7_0,esk8_0,esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_36,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_37,plain,(
    ! [X43,X44,X45,X46] :
      ( ( k5_mcart_1(X43,X44,X45,X46) = k1_mcart_1(k1_mcart_1(X46))
        | ~ m1_subset_1(X46,k3_zfmisc_1(X43,X44,X45))
        | X43 = k1_xboole_0
        | X44 = k1_xboole_0
        | X45 = k1_xboole_0 )
      & ( k6_mcart_1(X43,X44,X45,X46) = k2_mcart_1(k1_mcart_1(X46))
        | ~ m1_subset_1(X46,k3_zfmisc_1(X43,X44,X45))
        | X43 = k1_xboole_0
        | X44 = k1_xboole_0
        | X45 = k1_xboole_0 )
      & ( k7_mcart_1(X43,X44,X45,X46) = k2_mcart_1(X46)
        | ~ m1_subset_1(X46,k3_zfmisc_1(X43,X44,X45))
        | X43 = k1_xboole_0
        | X44 = k1_xboole_0
        | X45 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_mcart_1])])])])).

cnf(c_0_38,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_39,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_42,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_43,negated_conjecture,
    ( r1_xboole_0(esk9_0,X1)
    | ~ r1_xboole_0(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_44,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_45,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(esk8_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_33])).

cnf(c_0_47,plain,
    ( r2_hidden(k1_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk10_0,k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),esk9_0)) ),
    inference(rw,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_49,plain,
    ( k6_mcart_1(X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_50,negated_conjecture,
    ( m1_subset_1(esk10_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_51,plain,
    ( k5_mcart_1(X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(X4))
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_52,plain,
    ( ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_53,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_54,negated_conjecture,
    ( r1_xboole_0(X1,esk9_0)
    | ~ r1_xboole_0(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_55,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_44])).

cnf(c_0_56,plain,
    ( r2_hidden(k2_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_57,plain,
    ( v1_xboole_0(k3_xboole_0(X1,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_38,c_0_45])).

cnf(c_0_58,negated_conjecture,
    ( r1_xboole_0(esk8_0,X1)
    | ~ r1_xboole_0(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_46])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk10_0),k2_zfmisc_1(esk7_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_60,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k6_mcart_1(X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_49,c_0_36])).

cnf(c_0_61,negated_conjecture,
    ( m1_subset_1(esk10_0,k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0)) ),
    inference(rw,[status(thm)],[c_0_50,c_0_36])).

cnf(c_0_62,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k5_mcart_1(X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(X4))
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_51,c_0_36])).

cnf(c_0_63,plain,
    ( ~ r1_xboole_0(k4_xboole_0(X1,X2),X1)
    | ~ r2_hidden(X3,k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_64,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(X1,esk6_0),esk9_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

fof(c_0_65,plain,(
    ! [X47,X49,X50,X51,X52,X53] :
      ( ( r2_hidden(esk3_1(X47),X47)
        | X47 = k1_xboole_0 )
      & ( ~ r2_hidden(X49,X50)
        | ~ r2_hidden(X50,X51)
        | ~ r2_hidden(X51,X52)
        | ~ r2_hidden(X52,X53)
        | ~ r2_hidden(X53,esk3_1(X47))
        | r1_xboole_0(X49,X47)
        | X47 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_mcart_1])])])])])])).

cnf(c_0_66,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(k2_mcart_1(esk10_0),esk9_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_48])).

cnf(c_0_68,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_57,c_0_39])).

cnf(c_0_69,negated_conjecture,
    ( r1_xboole_0(X1,esk8_0)
    | ~ r1_xboole_0(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_58])).

cnf(c_0_70,negated_conjecture,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(esk10_0)),esk8_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_59])).

cnf(c_0_71,negated_conjecture,
    ( k2_mcart_1(k1_mcart_1(esk10_0)) = k6_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0)
    | esk6_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_72,negated_conjecture,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(esk10_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_59])).

cnf(c_0_73,negated_conjecture,
    ( k1_mcart_1(k1_mcart_1(esk10_0)) = k5_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0)
    | esk6_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_62,c_0_61])).

cnf(c_0_74,plain,
    ( k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_75,plain,(
    ! [X33,X34] :
      ( ( ~ r1_xboole_0(X33,X34)
        | k4_xboole_0(X33,X34) = X33 )
      & ( k4_xboole_0(X33,X34) != X33
        | r1_xboole_0(X33,X34) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

cnf(c_0_76,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk9_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_77,plain,
    ( r2_hidden(esk3_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_78,negated_conjecture,
    ( ~ v1_xboole_0(esk9_0) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_79,negated_conjecture,
    ( v1_xboole_0(esk9_0)
    | ~ r1_xboole_0(esk9_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_30])).

cnf(c_0_80,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(X1,esk5_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_55])).

cnf(c_0_81,negated_conjecture,
    ( ~ r2_hidden(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0),esk7_0)
    | ~ r2_hidden(k6_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0),esk8_0)
    | ~ r2_hidden(k7_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0),esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_82,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | r2_hidden(k6_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_83,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | r2_hidden(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_84,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4)
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_74,c_0_36])).

cnf(c_0_85,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_86,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_87,negated_conjecture,
    ( k4_xboole_0(esk9_0,esk6_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_88,negated_conjecture,
    ( ~ r1_xboole_0(esk9_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_89,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk8_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_80])).

cnf(c_0_90,negated_conjecture,
    ( ~ v1_xboole_0(esk8_0) ),
    inference(spm,[status(thm)],[c_0_66,c_0_70])).

cnf(c_0_91,negated_conjecture,
    ( v1_xboole_0(esk8_0)
    | ~ r1_xboole_0(esk8_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_46])).

cnf(c_0_92,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_93,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | ~ r2_hidden(k7_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0),esk9_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_83])).

cnf(c_0_94,negated_conjecture,
    ( k7_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0) = k2_mcart_1(esk10_0)
    | esk6_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_84,c_0_61])).

cnf(c_0_95,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_85,c_0_53])).

cnf(c_0_96,negated_conjecture,
    ( esk9_0 != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_88])).

cnf(c_0_97,negated_conjecture,
    ( k4_xboole_0(esk8_0,esk5_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_89,c_0_77])).

cnf(c_0_98,negated_conjecture,
    ( ~ r1_xboole_0(esk8_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_99,negated_conjecture,
    ( r1_tarski(esk7_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_92])).

cnf(c_0_100,negated_conjecture,
    ( ~ v1_xboole_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_66,c_0_72])).

cnf(c_0_101,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_67])])).

cnf(c_0_102,negated_conjecture,
    ( ~ r1_tarski(esk9_0,k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_87]),c_0_96])).

cnf(c_0_103,negated_conjecture,
    ( esk8_0 != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_97]),c_0_98])).

fof(c_0_104,plain,(
    ! [X30] : r1_xboole_0(X30,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

cnf(c_0_105,negated_conjecture,
    ( ~ r1_xboole_0(esk7_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_99]),c_0_100])).

cnf(c_0_106,negated_conjecture,
    ( r1_xboole_0(esk7_0,X1)
    | ~ r1_xboole_0(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_99])).

cnf(c_0_107,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_101]),c_0_102])).

cnf(c_0_108,negated_conjecture,
    ( ~ r1_tarski(esk8_0,k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_97]),c_0_103])).

cnf(c_0_109,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_104])).

cnf(c_0_110,negated_conjecture,
    ( ~ r1_xboole_0(esk4_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_105,c_0_106])).

cnf(c_0_111,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_107]),c_0_108])).

cnf(c_0_112,plain,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_109])).

cnf(c_0_113,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_110,c_0_111]),c_0_111]),c_0_112])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:50:09 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.41  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.19/0.41  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.41  #
% 0.19/0.41  # Preprocessing time       : 0.028 s
% 0.19/0.41  
% 0.19/0.41  # Proof found!
% 0.19/0.41  # SZS status Theorem
% 0.19/0.41  # SZS output start CNFRefutation
% 0.19/0.41  fof(t76_mcart_1, conjecture, ![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(X1))=>![X5]:(m1_subset_1(X5,k1_zfmisc_1(X2))=>![X6]:(m1_subset_1(X6,k1_zfmisc_1(X3))=>![X7]:(m1_subset_1(X7,k3_zfmisc_1(X1,X2,X3))=>(r2_hidden(X7,k3_zfmisc_1(X4,X5,X6))=>((r2_hidden(k5_mcart_1(X1,X2,X3,X7),X4)&r2_hidden(k6_mcart_1(X1,X2,X3,X7),X5))&r2_hidden(k7_mcart_1(X1,X2,X3,X7),X6))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_mcart_1)).
% 0.19/0.41  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.41  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.41  fof(t63_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X2,X3))=>r1_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 0.19/0.41  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 0.19/0.41  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.19/0.41  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.19/0.41  fof(t106_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k4_xboole_0(X2,X3))=>(r1_tarski(X1,X2)&r1_xboole_0(X1,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 0.19/0.41  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.19/0.41  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 0.19/0.41  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.19/0.41  fof(t10_mcart_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(X2,X3))=>(r2_hidden(k1_mcart_1(X1),X2)&r2_hidden(k2_mcart_1(X1),X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 0.19/0.41  fof(t50_mcart_1, axiom, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>((k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))&k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4)))&k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_mcart_1)).
% 0.19/0.41  fof(t6_mcart_1, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&![X3, X4, X5, X6, X7]:(((((r2_hidden(X3,X4)&r2_hidden(X4,X5))&r2_hidden(X5,X6))&r2_hidden(X6,X7))&r2_hidden(X7,X2))=>r1_xboole_0(X3,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_mcart_1)).
% 0.19/0.41  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.19/0.41  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.19/0.41  fof(c_0_16, negated_conjecture, ~(![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(X1))=>![X5]:(m1_subset_1(X5,k1_zfmisc_1(X2))=>![X6]:(m1_subset_1(X6,k1_zfmisc_1(X3))=>![X7]:(m1_subset_1(X7,k3_zfmisc_1(X1,X2,X3))=>(r2_hidden(X7,k3_zfmisc_1(X4,X5,X6))=>((r2_hidden(k5_mcart_1(X1,X2,X3,X7),X4)&r2_hidden(k6_mcart_1(X1,X2,X3,X7),X5))&r2_hidden(k7_mcart_1(X1,X2,X3,X7),X6)))))))), inference(assume_negation,[status(cth)],[t76_mcart_1])).
% 0.19/0.41  fof(c_0_17, plain, ![X35, X36]:((~m1_subset_1(X35,k1_zfmisc_1(X36))|r1_tarski(X35,X36))&(~r1_tarski(X35,X36)|m1_subset_1(X35,k1_zfmisc_1(X36)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.41  fof(c_0_18, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(esk4_0))&(m1_subset_1(esk8_0,k1_zfmisc_1(esk5_0))&(m1_subset_1(esk9_0,k1_zfmisc_1(esk6_0))&(m1_subset_1(esk10_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0))&(r2_hidden(esk10_0,k3_zfmisc_1(esk7_0,esk8_0,esk9_0))&(~r2_hidden(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0),esk7_0)|~r2_hidden(k6_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0),esk8_0)|~r2_hidden(k7_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0),esk9_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).
% 0.19/0.41  fof(c_0_19, plain, ![X20, X21]:(((r1_tarski(X20,X21)|X20!=X21)&(r1_tarski(X21,X20)|X20!=X21))&(~r1_tarski(X20,X21)|~r1_tarski(X21,X20)|X20=X21)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.41  fof(c_0_20, plain, ![X27, X28, X29]:(~r1_tarski(X27,X28)|~r1_xboole_0(X28,X29)|r1_xboole_0(X27,X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).
% 0.19/0.41  cnf(c_0_21, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.41  cnf(c_0_22, negated_conjecture, (m1_subset_1(esk9_0,k1_zfmisc_1(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.41  fof(c_0_23, plain, ![X37, X38, X39]:k3_zfmisc_1(X37,X38,X39)=k2_zfmisc_1(k2_zfmisc_1(X37,X38),X39), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 0.19/0.41  fof(c_0_24, plain, ![X14, X15, X17, X18, X19]:((r1_xboole_0(X14,X15)|r2_hidden(esk2_2(X14,X15),k3_xboole_0(X14,X15)))&(~r2_hidden(X19,k3_xboole_0(X17,X18))|~r1_xboole_0(X17,X18))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.19/0.41  fof(c_0_25, plain, ![X25, X26]:(~r1_tarski(X25,X26)|k3_xboole_0(X25,X26)=X25), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.19/0.41  fof(c_0_26, plain, ![X22, X23, X24]:((r1_tarski(X22,X23)|~r1_tarski(X22,k4_xboole_0(X23,X24)))&(r1_xboole_0(X22,X24)|~r1_tarski(X22,k4_xboole_0(X23,X24)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).
% 0.19/0.41  cnf(c_0_27, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.41  fof(c_0_28, plain, ![X12, X13]:(~r1_xboole_0(X12,X13)|r1_xboole_0(X13,X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.19/0.41  cnf(c_0_29, plain, (r1_xboole_0(X1,X3)|~r1_tarski(X1,X2)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.41  cnf(c_0_30, negated_conjecture, (r1_tarski(esk9_0,esk6_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.19/0.41  fof(c_0_31, plain, ![X31, X32]:r1_xboole_0(k4_xboole_0(X31,X32),X32), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 0.19/0.41  fof(c_0_32, plain, ![X8, X9, X10]:((~v1_xboole_0(X8)|~r2_hidden(X9,X8))&(r2_hidden(esk1_1(X10),X10)|v1_xboole_0(X10))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.19/0.41  cnf(c_0_33, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.41  fof(c_0_34, plain, ![X40, X41, X42]:((r2_hidden(k1_mcart_1(X40),X41)|~r2_hidden(X40,k2_zfmisc_1(X41,X42)))&(r2_hidden(k2_mcart_1(X40),X42)|~r2_hidden(X40,k2_zfmisc_1(X41,X42)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).
% 0.19/0.41  cnf(c_0_35, negated_conjecture, (r2_hidden(esk10_0,k3_zfmisc_1(esk7_0,esk8_0,esk9_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.41  cnf(c_0_36, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.41  fof(c_0_37, plain, ![X43, X44, X45, X46]:(((k5_mcart_1(X43,X44,X45,X46)=k1_mcart_1(k1_mcart_1(X46))|~m1_subset_1(X46,k3_zfmisc_1(X43,X44,X45))|(X43=k1_xboole_0|X44=k1_xboole_0|X45=k1_xboole_0))&(k6_mcart_1(X43,X44,X45,X46)=k2_mcart_1(k1_mcart_1(X46))|~m1_subset_1(X46,k3_zfmisc_1(X43,X44,X45))|(X43=k1_xboole_0|X44=k1_xboole_0|X45=k1_xboole_0)))&(k7_mcart_1(X43,X44,X45,X46)=k2_mcart_1(X46)|~m1_subset_1(X46,k3_zfmisc_1(X43,X44,X45))|(X43=k1_xboole_0|X44=k1_xboole_0|X45=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_mcart_1])])])])).
% 0.19/0.41  cnf(c_0_38, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.41  cnf(c_0_39, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.41  cnf(c_0_40, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k4_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.41  cnf(c_0_41, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_27])).
% 0.19/0.41  cnf(c_0_42, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.41  cnf(c_0_43, negated_conjecture, (r1_xboole_0(esk9_0,X1)|~r1_xboole_0(esk6_0,X1)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.19/0.41  cnf(c_0_44, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.41  cnf(c_0_45, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.41  cnf(c_0_46, negated_conjecture, (r1_tarski(esk8_0,esk5_0)), inference(spm,[status(thm)],[c_0_21, c_0_33])).
% 0.19/0.41  cnf(c_0_47, plain, (r2_hidden(k1_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.41  cnf(c_0_48, negated_conjecture, (r2_hidden(esk10_0,k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),esk9_0))), inference(rw,[status(thm)],[c_0_35, c_0_36])).
% 0.19/0.41  cnf(c_0_49, plain, (k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4))|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.41  cnf(c_0_50, negated_conjecture, (m1_subset_1(esk10_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.41  cnf(c_0_51, plain, (k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.41  cnf(c_0_52, plain, (~r1_tarski(X1,X2)|~r1_xboole_0(X1,X2)|~r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.19/0.41  cnf(c_0_53, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.19/0.41  cnf(c_0_54, negated_conjecture, (r1_xboole_0(X1,esk9_0)|~r1_xboole_0(esk6_0,X1)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.19/0.41  cnf(c_0_55, plain, (r1_xboole_0(X1,k4_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_42, c_0_44])).
% 0.19/0.41  cnf(c_0_56, plain, (r2_hidden(k2_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.41  cnf(c_0_57, plain, (v1_xboole_0(k3_xboole_0(X1,X2))|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_38, c_0_45])).
% 0.19/0.41  cnf(c_0_58, negated_conjecture, (r1_xboole_0(esk8_0,X1)|~r1_xboole_0(esk5_0,X1)), inference(spm,[status(thm)],[c_0_29, c_0_46])).
% 0.19/0.41  cnf(c_0_59, negated_conjecture, (r2_hidden(k1_mcart_1(esk10_0),k2_zfmisc_1(esk7_0,esk8_0))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.19/0.41  cnf(c_0_60, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4))|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_49, c_0_36])).
% 0.19/0.41  cnf(c_0_61, negated_conjecture, (m1_subset_1(esk10_0,k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0))), inference(rw,[status(thm)],[c_0_50, c_0_36])).
% 0.19/0.41  cnf(c_0_62, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_51, c_0_36])).
% 0.19/0.41  cnf(c_0_63, plain, (~r1_xboole_0(k4_xboole_0(X1,X2),X1)|~r2_hidden(X3,k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.19/0.41  cnf(c_0_64, negated_conjecture, (r1_xboole_0(k4_xboole_0(X1,esk6_0),esk9_0)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.19/0.41  fof(c_0_65, plain, ![X47, X49, X50, X51, X52, X53]:((r2_hidden(esk3_1(X47),X47)|X47=k1_xboole_0)&(~r2_hidden(X49,X50)|~r2_hidden(X50,X51)|~r2_hidden(X51,X52)|~r2_hidden(X52,X53)|~r2_hidden(X53,esk3_1(X47))|r1_xboole_0(X49,X47)|X47=k1_xboole_0)), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_mcart_1])])])])])])).
% 0.19/0.41  cnf(c_0_66, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.41  cnf(c_0_67, negated_conjecture, (r2_hidden(k2_mcart_1(esk10_0),esk9_0)), inference(spm,[status(thm)],[c_0_56, c_0_48])).
% 0.19/0.41  cnf(c_0_68, plain, (v1_xboole_0(X1)|~r1_tarski(X1,X2)|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_57, c_0_39])).
% 0.19/0.41  cnf(c_0_69, negated_conjecture, (r1_xboole_0(X1,esk8_0)|~r1_xboole_0(esk5_0,X1)), inference(spm,[status(thm)],[c_0_42, c_0_58])).
% 0.19/0.41  cnf(c_0_70, negated_conjecture, (r2_hidden(k2_mcart_1(k1_mcart_1(esk10_0)),esk8_0)), inference(spm,[status(thm)],[c_0_56, c_0_59])).
% 0.19/0.41  cnf(c_0_71, negated_conjecture, (k2_mcart_1(k1_mcart_1(esk10_0))=k6_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0)|esk6_0=k1_xboole_0|esk5_0=k1_xboole_0|esk4_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.19/0.41  cnf(c_0_72, negated_conjecture, (r2_hidden(k1_mcart_1(k1_mcart_1(esk10_0)),esk7_0)), inference(spm,[status(thm)],[c_0_47, c_0_59])).
% 0.19/0.41  cnf(c_0_73, negated_conjecture, (k1_mcart_1(k1_mcart_1(esk10_0))=k5_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0)|esk6_0=k1_xboole_0|esk5_0=k1_xboole_0|esk4_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_62, c_0_61])).
% 0.19/0.41  cnf(c_0_74, plain, (k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.41  fof(c_0_75, plain, ![X33, X34]:((~r1_xboole_0(X33,X34)|k4_xboole_0(X33,X34)=X33)&(k4_xboole_0(X33,X34)!=X33|r1_xboole_0(X33,X34))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.19/0.41  cnf(c_0_76, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(esk9_0,esk6_0))), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.19/0.41  cnf(c_0_77, plain, (r2_hidden(esk3_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.19/0.41  cnf(c_0_78, negated_conjecture, (~v1_xboole_0(esk9_0)), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.19/0.41  cnf(c_0_79, negated_conjecture, (v1_xboole_0(esk9_0)|~r1_xboole_0(esk9_0,esk6_0)), inference(spm,[status(thm)],[c_0_68, c_0_30])).
% 0.19/0.41  cnf(c_0_80, negated_conjecture, (r1_xboole_0(k4_xboole_0(X1,esk5_0),esk8_0)), inference(spm,[status(thm)],[c_0_69, c_0_55])).
% 0.19/0.41  cnf(c_0_81, negated_conjecture, (~r2_hidden(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0),esk7_0)|~r2_hidden(k6_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0),esk8_0)|~r2_hidden(k7_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0),esk9_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.41  cnf(c_0_82, negated_conjecture, (esk4_0=k1_xboole_0|esk5_0=k1_xboole_0|esk6_0=k1_xboole_0|r2_hidden(k6_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0),esk8_0)), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 0.19/0.41  cnf(c_0_83, negated_conjecture, (esk4_0=k1_xboole_0|esk5_0=k1_xboole_0|esk6_0=k1_xboole_0|r2_hidden(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0),esk7_0)), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.19/0.41  cnf(c_0_84, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_74, c_0_36])).
% 0.19/0.41  cnf(c_0_85, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.41  cnf(c_0_86, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.19/0.41  cnf(c_0_87, negated_conjecture, (k4_xboole_0(esk9_0,esk6_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 0.19/0.41  cnf(c_0_88, negated_conjecture, (~r1_xboole_0(esk9_0,esk6_0)), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 0.19/0.41  cnf(c_0_89, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(esk8_0,esk5_0))), inference(spm,[status(thm)],[c_0_63, c_0_80])).
% 0.19/0.41  cnf(c_0_90, negated_conjecture, (~v1_xboole_0(esk8_0)), inference(spm,[status(thm)],[c_0_66, c_0_70])).
% 0.19/0.41  cnf(c_0_91, negated_conjecture, (v1_xboole_0(esk8_0)|~r1_xboole_0(esk8_0,esk5_0)), inference(spm,[status(thm)],[c_0_68, c_0_46])).
% 0.19/0.41  cnf(c_0_92, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.41  cnf(c_0_93, negated_conjecture, (esk6_0=k1_xboole_0|esk5_0=k1_xboole_0|esk4_0=k1_xboole_0|~r2_hidden(k7_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0),esk9_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_83])).
% 0.19/0.41  cnf(c_0_94, negated_conjecture, (k7_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0)=k2_mcart_1(esk10_0)|esk6_0=k1_xboole_0|esk5_0=k1_xboole_0|esk4_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_84, c_0_61])).
% 0.19/0.41  cnf(c_0_95, plain, (k4_xboole_0(X1,X2)=X1|~r1_tarski(X1,k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_85, c_0_53])).
% 0.19/0.41  cnf(c_0_96, negated_conjecture, (esk9_0!=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_88])).
% 0.19/0.41  cnf(c_0_97, negated_conjecture, (k4_xboole_0(esk8_0,esk5_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_89, c_0_77])).
% 0.19/0.41  cnf(c_0_98, negated_conjecture, (~r1_xboole_0(esk8_0,esk5_0)), inference(spm,[status(thm)],[c_0_90, c_0_91])).
% 0.19/0.41  cnf(c_0_99, negated_conjecture, (r1_tarski(esk7_0,esk4_0)), inference(spm,[status(thm)],[c_0_21, c_0_92])).
% 0.19/0.41  cnf(c_0_100, negated_conjecture, (~v1_xboole_0(esk7_0)), inference(spm,[status(thm)],[c_0_66, c_0_72])).
% 0.19/0.41  cnf(c_0_101, negated_conjecture, (esk4_0=k1_xboole_0|esk5_0=k1_xboole_0|esk6_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_94]), c_0_67])])).
% 0.19/0.41  cnf(c_0_102, negated_conjecture, (~r1_tarski(esk9_0,k1_xboole_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_87]), c_0_96])).
% 0.19/0.41  cnf(c_0_103, negated_conjecture, (esk8_0!=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_97]), c_0_98])).
% 0.19/0.41  fof(c_0_104, plain, ![X30]:r1_xboole_0(X30,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.19/0.41  cnf(c_0_105, negated_conjecture, (~r1_xboole_0(esk7_0,esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_99]), c_0_100])).
% 0.19/0.41  cnf(c_0_106, negated_conjecture, (r1_xboole_0(esk7_0,X1)|~r1_xboole_0(esk4_0,X1)), inference(spm,[status(thm)],[c_0_29, c_0_99])).
% 0.19/0.41  cnf(c_0_107, negated_conjecture, (esk5_0=k1_xboole_0|esk4_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_101]), c_0_102])).
% 0.19/0.41  cnf(c_0_108, negated_conjecture, (~r1_tarski(esk8_0,k1_xboole_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_97]), c_0_103])).
% 0.19/0.41  cnf(c_0_109, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_104])).
% 0.19/0.41  cnf(c_0_110, negated_conjecture, (~r1_xboole_0(esk4_0,esk4_0)), inference(spm,[status(thm)],[c_0_105, c_0_106])).
% 0.19/0.41  cnf(c_0_111, negated_conjecture, (esk4_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_107]), c_0_108])).
% 0.19/0.41  cnf(c_0_112, plain, (r1_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_42, c_0_109])).
% 0.19/0.41  cnf(c_0_113, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_110, c_0_111]), c_0_111]), c_0_112])]), ['proof']).
% 0.19/0.41  # SZS output end CNFRefutation
% 0.19/0.41  # Proof object total steps             : 114
% 0.19/0.41  # Proof object clause steps            : 81
% 0.19/0.41  # Proof object formula steps           : 33
% 0.19/0.41  # Proof object conjectures             : 52
% 0.19/0.41  # Proof object clause conjectures      : 49
% 0.19/0.41  # Proof object formula conjectures     : 3
% 0.19/0.41  # Proof object initial clauses used    : 26
% 0.19/0.41  # Proof object initial formulas used   : 16
% 0.19/0.41  # Proof object generating inferences   : 48
% 0.19/0.41  # Proof object simplifying inferences  : 20
% 0.19/0.41  # Training examples: 0 positive, 0 negative
% 0.19/0.41  # Parsed axioms                        : 16
% 0.19/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.41  # Initial clauses                      : 32
% 0.19/0.41  # Removed in clause preprocessing      : 1
% 0.19/0.41  # Initial clauses in saturation        : 31
% 0.19/0.41  # Processed clauses                    : 829
% 0.19/0.41  # ...of these trivial                  : 17
% 0.19/0.41  # ...subsumed                          : 492
% 0.19/0.41  # ...remaining for further processing  : 320
% 0.19/0.41  # Other redundant clauses eliminated   : 3
% 0.19/0.41  # Clauses deleted for lack of memory   : 0
% 0.19/0.41  # Backward-subsumed                    : 9
% 0.19/0.41  # Backward-rewritten                   : 71
% 0.19/0.41  # Generated clauses                    : 4611
% 0.19/0.41  # ...of the previous two non-trivial   : 1472
% 0.19/0.41  # Contextual simplify-reflections      : 1
% 0.19/0.41  # Paramodulations                      : 4608
% 0.19/0.41  # Factorizations                       : 0
% 0.19/0.41  # Equation resolutions                 : 3
% 0.19/0.41  # Propositional unsat checks           : 0
% 0.19/0.41  #    Propositional check models        : 0
% 0.19/0.41  #    Propositional check unsatisfiable : 0
% 0.19/0.41  #    Propositional clauses             : 0
% 0.19/0.41  #    Propositional clauses after purity: 0
% 0.19/0.41  #    Propositional unsat core size     : 0
% 0.19/0.41  #    Propositional preprocessing time  : 0.000
% 0.19/0.41  #    Propositional encoding time       : 0.000
% 0.19/0.41  #    Propositional solver time         : 0.000
% 0.19/0.41  #    Success case prop preproc time    : 0.000
% 0.19/0.41  #    Success case prop encoding time   : 0.000
% 0.19/0.41  #    Success case prop solver time     : 0.000
% 0.19/0.41  # Current number of processed clauses  : 238
% 0.19/0.41  #    Positive orientable unit clauses  : 62
% 0.19/0.41  #    Positive unorientable unit clauses: 0
% 0.19/0.41  #    Negative unit clauses             : 18
% 0.19/0.41  #    Non-unit-clauses                  : 158
% 0.19/0.41  # Current number of unprocessed clauses: 585
% 0.19/0.41  # ...number of literals in the above   : 1854
% 0.19/0.41  # Current number of archived formulas  : 0
% 0.19/0.41  # Current number of archived clauses   : 81
% 0.19/0.41  # Clause-clause subsumption calls (NU) : 3970
% 0.19/0.41  # Rec. Clause-clause subsumption calls : 2596
% 0.19/0.41  # Non-unit clause-clause subsumptions  : 121
% 0.19/0.41  # Unit Clause-clause subsumption calls : 1308
% 0.19/0.41  # Rewrite failures with RHS unbound    : 0
% 0.19/0.41  # BW rewrite match attempts            : 174
% 0.19/0.41  # BW rewrite match successes           : 28
% 0.19/0.41  # Condensation attempts                : 0
% 0.19/0.41  # Condensation successes               : 0
% 0.19/0.41  # Termbank termtop insertions          : 42181
% 0.19/0.42  
% 0.19/0.42  # -------------------------------------------------
% 0.19/0.42  # User time                : 0.073 s
% 0.19/0.42  # System time              : 0.004 s
% 0.19/0.42  # Total time               : 0.077 s
% 0.19/0.42  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
