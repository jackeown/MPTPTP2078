%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0903+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:22 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  119 (2534 expanded)
%              Number of clauses        :   84 (1094 expanded)
%              Number of leaves         :   17 ( 655 expanded)
%              Depth                    :   37
%              Number of atoms          :  405 (7847 expanded)
%              Number of equality atoms :  211 (3750 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   13 (   3 average)
%              Maximal term depth       :    8 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t63_mcart_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ~ ( ~ r1_tarski(X1,k4_zfmisc_1(X1,X2,X3,X4))
          & ~ r1_tarski(X1,k4_zfmisc_1(X2,X3,X4,X1))
          & ~ r1_tarski(X1,k4_zfmisc_1(X3,X4,X1,X2))
          & ~ r1_tarski(X1,k4_zfmisc_1(X4,X1,X2,X3)) )
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_mcart_1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t54_mcart_1,axiom,(
    ! [X1,X2,X3,X4] : k3_zfmisc_1(k2_zfmisc_1(X1,X2),X3,X4) = k4_zfmisc_1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_mcart_1)).

fof(dt_k9_mcart_1,axiom,(
    ! [X1,X2,X3,X4,X5] :
      ( m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))
     => m1_subset_1(k9_mcart_1(X1,X2,X3,X4,X5),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_mcart_1)).

fof(t34_mcart_1,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] :
            ~ ( r2_hidden(X2,X1)
              & ! [X3,X4,X5,X6] :
                  ~ ( ( r2_hidden(X3,X1)
                      | r2_hidden(X4,X1) )
                    & X2 = k4_mcart_1(X3,X4,X5,X6) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_mcart_1)).

fof(t49_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( ~ ( ~ r1_tarski(X1,k3_zfmisc_1(X1,X2,X3))
          & ~ r1_tarski(X1,k3_zfmisc_1(X2,X3,X1))
          & ~ r1_tarski(X1,k3_zfmisc_1(X3,X1,X2)) )
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_mcart_1)).

fof(d4_mcart_1,axiom,(
    ! [X1,X2,X3,X4] : k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k3_mcart_1(X1,X2,X3),X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_mcart_1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(t60_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & X4 != k1_xboole_0
        & ~ ! [X5] :
              ( m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))
             => X5 = k4_mcart_1(k8_mcart_1(X1,X2,X3,X4,X5),k9_mcart_1(X1,X2,X3,X4,X5),k10_mcart_1(X1,X2,X3,X4,X5),k11_mcart_1(X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_mcart_1)).

fof(dt_k8_mcart_1,axiom,(
    ! [X1,X2,X3,X4,X5] :
      ( m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))
     => m1_subset_1(k8_mcart_1(X1,X2,X3,X4,X5),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_mcart_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(t55_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & X4 != k1_xboole_0 )
    <=> k4_zfmisc_1(X1,X2,X3,X4) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_mcart_1)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

fof(t3_xboole_1,axiom,(
    ! [X1] :
      ( r1_tarski(X1,k1_xboole_0)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ~ ( ~ r1_tarski(X1,k4_zfmisc_1(X1,X2,X3,X4))
            & ~ r1_tarski(X1,k4_zfmisc_1(X2,X3,X4,X1))
            & ~ r1_tarski(X1,k4_zfmisc_1(X3,X4,X1,X2))
            & ~ r1_tarski(X1,k4_zfmisc_1(X4,X1,X2,X3)) )
       => X1 = k1_xboole_0 ) ),
    inference(assume_negation,[status(cth)],[t63_mcart_1])).

fof(c_0_18,plain,(
    ! [X40,X41,X42] :
      ( ~ r2_hidden(X40,X41)
      | ~ m1_subset_1(X41,k1_zfmisc_1(X42))
      | m1_subset_1(X40,X42) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_19,plain,(
    ! [X34,X35] :
      ( ( ~ m1_subset_1(X34,k1_zfmisc_1(X35))
        | r1_tarski(X34,X35) )
      & ( ~ r1_tarski(X34,X35)
        | m1_subset_1(X34,k1_zfmisc_1(X35)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_20,negated_conjecture,
    ( ( r1_tarski(esk2_0,k4_zfmisc_1(esk2_0,esk3_0,esk4_0,esk5_0))
      | r1_tarski(esk2_0,k4_zfmisc_1(esk3_0,esk4_0,esk5_0,esk2_0))
      | r1_tarski(esk2_0,k4_zfmisc_1(esk4_0,esk5_0,esk2_0,esk3_0))
      | r1_tarski(esk2_0,k4_zfmisc_1(esk5_0,esk2_0,esk3_0,esk4_0)) )
    & esk2_0 != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_17])])])])).

fof(c_0_21,plain,(
    ! [X43,X44,X45,X46] : k3_zfmisc_1(k2_zfmisc_1(X43,X44),X45,X46) = k4_zfmisc_1(X43,X44,X45,X46) ),
    inference(variable_rename,[status(thm)],[t54_mcart_1])).

cnf(c_0_22,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( r1_tarski(esk2_0,k4_zfmisc_1(esk2_0,esk3_0,esk4_0,esk5_0))
    | r1_tarski(esk2_0,k4_zfmisc_1(esk3_0,esk4_0,esk5_0,esk2_0))
    | r1_tarski(esk2_0,k4_zfmisc_1(esk4_0,esk5_0,esk2_0,esk3_0))
    | r1_tarski(esk2_0,k4_zfmisc_1(esk5_0,esk2_0,esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,plain,
    ( k3_zfmisc_1(k2_zfmisc_1(X1,X2),X3,X4) = k4_zfmisc_1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_26,plain,(
    ! [X19,X20,X21,X22,X23] :
      ( ~ m1_subset_1(X23,k4_zfmisc_1(X19,X20,X21,X22))
      | m1_subset_1(k9_mcart_1(X19,X20,X21,X22,X23),X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_mcart_1])])).

cnf(c_0_27,plain,
    ( m1_subset_1(X1,X2)
    | ~ r1_tarski(X3,X2)
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(esk2_0,k3_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0,esk5_0))
    | r1_tarski(esk2_0,k3_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0,esk2_0))
    | r1_tarski(esk2_0,k3_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk2_0,esk3_0))
    | r1_tarski(esk2_0,k3_zfmisc_1(k2_zfmisc_1(esk5_0,esk2_0),esk3_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_25]),c_0_25]),c_0_25]),c_0_25])).

fof(c_0_29,plain,(
    ! [X28,X30,X31,X32,X33] :
      ( ( r2_hidden(esk1_1(X28),X28)
        | X28 = k1_xboole_0 )
      & ( ~ r2_hidden(X30,X28)
        | esk1_1(X28) != k4_mcart_1(X30,X31,X32,X33)
        | X28 = k1_xboole_0 )
      & ( ~ r2_hidden(X31,X28)
        | esk1_1(X28) != k4_mcart_1(X30,X31,X32,X33)
        | X28 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_mcart_1])])])])])])).

cnf(c_0_30,plain,
    ( m1_subset_1(k9_mcart_1(X2,X3,X4,X5,X1),X3)
    | ~ m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(esk2_0,k3_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk2_0,esk3_0))
    | r1_tarski(esk2_0,k3_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0,esk2_0))
    | r1_tarski(esk2_0,k3_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0,esk5_0))
    | m1_subset_1(X1,k3_zfmisc_1(k2_zfmisc_1(esk5_0,esk2_0),esk3_0,esk4_0))
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_32,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_33,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_34,plain,(
    ! [X37,X38,X39] :
      ( ( ~ r1_tarski(X37,k3_zfmisc_1(X37,X38,X39))
        | X37 = k1_xboole_0 )
      & ( ~ r1_tarski(X37,k3_zfmisc_1(X38,X39,X37))
        | X37 = k1_xboole_0 )
      & ( ~ r1_tarski(X37,k3_zfmisc_1(X39,X37,X38))
        | X37 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t49_mcart_1])])])])).

cnf(c_0_35,plain,
    ( m1_subset_1(k9_mcart_1(X2,X3,X4,X5,X1),X3)
    | ~ m1_subset_1(X1,k3_zfmisc_1(k2_zfmisc_1(X2,X3),X4,X5)) ),
    inference(rw,[status(thm)],[c_0_30,c_0_25])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(esk2_0,k3_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0,esk5_0))
    | r1_tarski(esk2_0,k3_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0,esk2_0))
    | r1_tarski(esk2_0,k3_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk2_0,esk3_0))
    | m1_subset_1(esk1_1(esk2_0),k3_zfmisc_1(k2_zfmisc_1(esk5_0,esk2_0),esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])).

cnf(c_0_37,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k3_zfmisc_1(X2,X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_38,negated_conjecture,
    ( r1_tarski(esk2_0,k3_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk2_0,esk3_0))
    | r1_tarski(esk2_0,k3_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0,esk2_0))
    | r1_tarski(esk2_0,k3_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0,esk5_0))
    | m1_subset_1(k9_mcart_1(esk5_0,esk2_0,esk3_0,esk4_0,esk1_1(esk2_0)),esk2_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

fof(c_0_39,plain,(
    ! [X10,X11,X12,X13] : k4_mcart_1(X10,X11,X12,X13) = k4_tarski(k3_mcart_1(X10,X11,X12),X13) ),
    inference(variable_rename,[status(thm)],[d4_mcart_1])).

fof(c_0_40,plain,(
    ! [X7,X8,X9] : k3_mcart_1(X7,X8,X9) = k4_tarski(k4_tarski(X7,X8),X9) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

cnf(c_0_41,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k3_zfmisc_1(X2,X3,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(esk2_0,k3_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0,esk5_0))
    | r1_tarski(esk2_0,k3_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0,esk2_0))
    | m1_subset_1(k9_mcart_1(esk5_0,esk2_0,esk3_0,esk4_0,esk1_1(esk2_0)),esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_33])).

fof(c_0_43,plain,(
    ! [X51,X52,X53,X54,X55] :
      ( X51 = k1_xboole_0
      | X52 = k1_xboole_0
      | X53 = k1_xboole_0
      | X54 = k1_xboole_0
      | ~ m1_subset_1(X55,k4_zfmisc_1(X51,X52,X53,X54))
      | X55 = k4_mcart_1(k8_mcart_1(X51,X52,X53,X54,X55),k9_mcart_1(X51,X52,X53,X54,X55),k10_mcart_1(X51,X52,X53,X54,X55),k11_mcart_1(X51,X52,X53,X54,X55)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_mcart_1])])])).

cnf(c_0_44,plain,
    ( k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k3_mcart_1(X1,X2,X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_45,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_46,plain,(
    ! [X14,X15,X16,X17,X18] :
      ( ~ m1_subset_1(X18,k4_zfmisc_1(X14,X15,X16,X17))
      | m1_subset_1(k8_mcart_1(X14,X15,X16,X17,X18),X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_mcart_1])])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(esk2_0,k3_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0,esk5_0))
    | m1_subset_1(k9_mcart_1(esk5_0,esk2_0,esk3_0,esk4_0,esk1_1(esk2_0)),esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_33])).

cnf(c_0_48,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X5 = k4_mcart_1(k8_mcart_1(X1,X2,X3,X4,X5),k9_mcart_1(X1,X2,X3,X4,X5),k10_mcart_1(X1,X2,X3,X4,X5),k11_mcart_1(X1,X2,X3,X4,X5))
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_49,plain,
    ( k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4) ),
    inference(rw,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_50,plain,
    ( m1_subset_1(k8_mcart_1(X2,X3,X4,X5,X1),X2)
    | ~ m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(k9_mcart_1(esk5_0,esk2_0,esk3_0,esk4_0,esk1_1(esk2_0)),esk2_0)
    | m1_subset_1(X1,k3_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0,esk5_0))
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_47])).

cnf(c_0_52,plain,
    ( X2 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | esk1_1(X2) != k4_mcart_1(X3,X1,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_53,plain,
    ( X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | X5 = k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(X1,X2,X3,X4,X5),k9_mcart_1(X1,X2,X3,X4,X5)),k10_mcart_1(X1,X2,X3,X4,X5)),k11_mcart_1(X1,X2,X3,X4,X5))
    | ~ m1_subset_1(X5,k3_zfmisc_1(k2_zfmisc_1(X1,X2),X3,X4)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_49]),c_0_25])).

fof(c_0_54,plain,(
    ! [X26,X27] :
      ( ~ m1_subset_1(X26,X27)
      | v1_xboole_0(X27)
      | r2_hidden(X26,X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_55,plain,
    ( m1_subset_1(k8_mcart_1(X2,X3,X4,X5,X1),X2)
    | ~ m1_subset_1(X1,k3_zfmisc_1(k2_zfmisc_1(X2,X3),X4,X5)) ),
    inference(rw,[status(thm)],[c_0_50,c_0_25])).

cnf(c_0_56,negated_conjecture,
    ( m1_subset_1(esk1_1(esk2_0),k3_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0,esk5_0))
    | m1_subset_1(k9_mcart_1(esk5_0,esk2_0,esk3_0,esk4_0,esk1_1(esk2_0)),esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_32]),c_0_33])).

cnf(c_0_57,plain,
    ( X2 = k1_xboole_0
    | esk1_1(X2) != k4_tarski(k4_tarski(k4_tarski(X3,X1),X4),X5)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_52,c_0_49])).

cnf(c_0_58,negated_conjecture,
    ( k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(esk5_0,esk2_0,esk3_0,esk4_0,esk1_1(esk2_0)),k9_mcart_1(esk5_0,esk2_0,esk3_0,esk4_0,esk1_1(esk2_0))),k10_mcart_1(esk5_0,esk2_0,esk3_0,esk4_0,esk1_1(esk2_0))),k11_mcart_1(esk5_0,esk2_0,esk3_0,esk4_0,esk1_1(esk2_0))) = esk1_1(esk2_0)
    | esk5_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | r1_tarski(esk2_0,k3_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk2_0,esk3_0))
    | r1_tarski(esk2_0,k3_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0,esk2_0))
    | r1_tarski(esk2_0,k3_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_36]),c_0_33])).

cnf(c_0_59,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_60,negated_conjecture,
    ( m1_subset_1(k9_mcart_1(esk5_0,esk2_0,esk3_0,esk4_0,esk1_1(esk2_0)),esk2_0)
    | m1_subset_1(k8_mcart_1(esk2_0,esk3_0,esk4_0,esk5_0,esk1_1(esk2_0)),esk2_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_61,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | X1 = k1_xboole_0
    | r1_tarski(esk2_0,k3_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0,esk5_0))
    | r1_tarski(esk2_0,k3_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0,esk2_0))
    | r1_tarski(esk2_0,k3_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk2_0,esk3_0))
    | esk1_1(X1) != esk1_1(esk2_0)
    | ~ r2_hidden(k9_mcart_1(esk5_0,esk2_0,esk3_0,esk4_0,esk1_1(esk2_0)),X1) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(k9_mcart_1(esk5_0,esk2_0,esk3_0,esk4_0,esk1_1(esk2_0)),esk2_0)
    | v1_xboole_0(esk2_0)
    | m1_subset_1(k8_mcart_1(esk2_0,esk3_0,esk4_0,esk5_0,esk1_1(esk2_0)),esk2_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_63,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | r1_tarski(esk2_0,k3_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk2_0,esk3_0))
    | r1_tarski(esk2_0,k3_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0,esk2_0))
    | r1_tarski(esk2_0,k3_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0,esk5_0))
    | v1_xboole_0(esk2_0)
    | m1_subset_1(k8_mcart_1(esk2_0,esk3_0,esk4_0,esk5_0,esk1_1(esk2_0)),esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_33])).

cnf(c_0_64,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | r1_tarski(esk2_0,k3_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0,esk5_0))
    | r1_tarski(esk2_0,k3_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0,esk2_0))
    | v1_xboole_0(esk2_0)
    | m1_subset_1(k8_mcart_1(esk2_0,esk3_0,esk4_0,esk5_0,esk1_1(esk2_0)),esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_63]),c_0_33])).

fof(c_0_65,plain,(
    ! [X57,X58] :
      ( ~ r2_hidden(X57,X58)
      | ~ v1_xboole_0(X58) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_66,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | r1_tarski(esk2_0,k3_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0,esk5_0))
    | v1_xboole_0(esk2_0)
    | m1_subset_1(k8_mcart_1(esk2_0,esk3_0,esk4_0,esk5_0,esk1_1(esk2_0)),esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_64]),c_0_33])).

cnf(c_0_67,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_68,plain,
    ( X2 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | esk1_1(X2) != k4_mcart_1(X1,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_69,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | m1_subset_1(k8_mcart_1(esk2_0,esk3_0,esk4_0,esk5_0,esk1_1(esk2_0)),esk2_0)
    | m1_subset_1(X1,k3_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0,esk5_0))
    | ~ r2_hidden(X1,esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_66]),c_0_67])).

cnf(c_0_70,plain,
    ( X2 = k1_xboole_0
    | esk1_1(X2) != k4_tarski(k4_tarski(k4_tarski(X1,X3),X4),X5)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_68,c_0_49])).

cnf(c_0_71,negated_conjecture,
    ( k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(esk2_0,esk3_0,esk4_0,esk5_0,esk1_1(esk2_0)),k9_mcart_1(esk2_0,esk3_0,esk4_0,esk5_0,esk1_1(esk2_0))),k10_mcart_1(esk2_0,esk3_0,esk4_0,esk5_0,esk1_1(esk2_0))),k11_mcart_1(esk2_0,esk3_0,esk4_0,esk5_0,esk1_1(esk2_0))) = esk1_1(esk2_0)
    | esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | m1_subset_1(k9_mcart_1(esk5_0,esk2_0,esk3_0,esk4_0,esk1_1(esk2_0)),esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_56]),c_0_33])).

cnf(c_0_72,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | m1_subset_1(k8_mcart_1(esk2_0,esk3_0,esk4_0,esk5_0,esk1_1(esk2_0)),esk2_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_32]),c_0_33]),c_0_55])).

cnf(c_0_73,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | X1 = k1_xboole_0
    | m1_subset_1(k9_mcart_1(esk5_0,esk2_0,esk3_0,esk4_0,esk1_1(esk2_0)),esk2_0)
    | esk1_1(X1) != esk1_1(esk2_0)
    | ~ r2_hidden(k8_mcart_1(esk2_0,esk3_0,esk4_0,esk5_0,esk1_1(esk2_0)),X1) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_74,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | r2_hidden(k8_mcart_1(esk2_0,esk3_0,esk4_0,esk5_0,esk1_1(esk2_0)),esk2_0)
    | v1_xboole_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_72])).

cnf(c_0_75,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | v1_xboole_0(esk2_0)
    | m1_subset_1(k9_mcart_1(esk5_0,esk2_0,esk3_0,esk4_0,esk1_1(esk2_0)),esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_33])).

cnf(c_0_76,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | r2_hidden(k9_mcart_1(esk5_0,esk2_0,esk3_0,esk4_0,esk1_1(esk2_0)),esk2_0)
    | v1_xboole_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_75])).

fof(c_0_77,plain,(
    ! [X24,X25] :
      ( ~ r2_hidden(X24,X25)
      | m1_subset_1(X24,X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_78,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | r1_tarski(esk2_0,k3_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk2_0,esk3_0))
    | r1_tarski(esk2_0,k3_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0,esk2_0))
    | r1_tarski(esk2_0,k3_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0,esk5_0))
    | v1_xboole_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_76]),c_0_33])).

cnf(c_0_79,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

fof(c_0_80,plain,(
    ! [X47,X48,X49,X50] :
      ( ( X47 = k1_xboole_0
        | X48 = k1_xboole_0
        | X49 = k1_xboole_0
        | X50 = k1_xboole_0
        | k4_zfmisc_1(X47,X48,X49,X50) != k1_xboole_0 )
      & ( X47 != k1_xboole_0
        | k4_zfmisc_1(X47,X48,X49,X50) = k1_xboole_0 )
      & ( X48 != k1_xboole_0
        | k4_zfmisc_1(X47,X48,X49,X50) = k1_xboole_0 )
      & ( X49 != k1_xboole_0
        | k4_zfmisc_1(X47,X48,X49,X50) = k1_xboole_0 )
      & ( X50 != k1_xboole_0
        | k4_zfmisc_1(X47,X48,X49,X50) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_mcart_1])])])).

cnf(c_0_81,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | r1_tarski(esk2_0,k3_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0,esk5_0))
    | r1_tarski(esk2_0,k3_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0,esk2_0))
    | v1_xboole_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_78]),c_0_33])).

cnf(c_0_82,plain,
    ( X1 = k1_xboole_0
    | m1_subset_1(esk1_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_79,c_0_32])).

cnf(c_0_83,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | k4_zfmisc_1(X1,X2,X3,X4) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_84,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | r1_tarski(esk2_0,k3_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0,esk5_0))
    | v1_xboole_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_81]),c_0_33])).

cnf(c_0_85,plain,
    ( k3_zfmisc_1(k2_zfmisc_1(X1,X2),X3,X4) = k1_xboole_0
    | m1_subset_1(k8_mcart_1(X1,X2,X3,X4,esk1_1(k3_zfmisc_1(k2_zfmisc_1(X1,X2),X3,X4))),X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_82])).

cnf(c_0_86,plain,
    ( X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k3_zfmisc_1(k2_zfmisc_1(X1,X2),X3,X4) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_83,c_0_25])).

cnf(c_0_87,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | m1_subset_1(X1,k3_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0,esk5_0))
    | ~ r2_hidden(X1,esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_84]),c_0_67])).

cnf(c_0_88,plain,
    ( k3_zfmisc_1(k2_zfmisc_1(X1,X2),X3,X4) = k1_xboole_0
    | r2_hidden(k8_mcart_1(X1,X2,X3,X4,esk1_1(k3_zfmisc_1(k2_zfmisc_1(X1,X2),X3,X4))),X1)
    | v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_59,c_0_85])).

cnf(c_0_89,plain,
    ( k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(X1,X2,X3,X4,esk1_1(k3_zfmisc_1(k2_zfmisc_1(X1,X2),X3,X4))),k9_mcart_1(X1,X2,X3,X4,esk1_1(k3_zfmisc_1(k2_zfmisc_1(X1,X2),X3,X4)))),k10_mcart_1(X1,X2,X3,X4,esk1_1(k3_zfmisc_1(k2_zfmisc_1(X1,X2),X3,X4)))),k11_mcart_1(X1,X2,X3,X4,esk1_1(k3_zfmisc_1(k2_zfmisc_1(X1,X2),X3,X4)))) = esk1_1(k3_zfmisc_1(k2_zfmisc_1(X1,X2),X3,X4))
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_82]),c_0_86])).

cnf(c_0_90,negated_conjecture,
    ( k3_zfmisc_1(k2_zfmisc_1(esk2_0,X1),X2,X3) = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | v1_xboole_0(esk2_0)
    | m1_subset_1(k8_mcart_1(esk2_0,X1,X2,X3,esk1_1(k3_zfmisc_1(k2_zfmisc_1(esk2_0,X1),X2,X3))),k3_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_87,c_0_88])).

fof(c_0_91,plain,(
    ! [X56] :
      ( ~ v1_xboole_0(X56)
      | X56 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_92,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X5 = k1_xboole_0
    | esk1_1(X5) != esk1_1(k3_zfmisc_1(k2_zfmisc_1(X4,X3),X2,X1))
    | ~ r2_hidden(k8_mcart_1(X4,X3,X2,X1,esk1_1(k3_zfmisc_1(k2_zfmisc_1(X4,X3),X2,X1))),X5) ),
    inference(spm,[status(thm)],[c_0_70,c_0_89])).

cnf(c_0_93,negated_conjecture,
    ( k3_zfmisc_1(k2_zfmisc_1(esk2_0,X1),X2,X3) = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | r2_hidden(k8_mcart_1(esk2_0,X1,X2,X3,esk1_1(k3_zfmisc_1(k2_zfmisc_1(esk2_0,X1),X2,X3))),k3_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0,esk5_0))
    | v1_xboole_0(k3_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0,esk5_0))
    | v1_xboole_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_90])).

cnf(c_0_94,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_91])).

cnf(c_0_95,negated_conjecture,
    ( k3_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0,esk5_0) = k1_xboole_0
    | k3_zfmisc_1(k2_zfmisc_1(esk2_0,X1),X2,X3) = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | v1_xboole_0(esk2_0)
    | esk1_1(k3_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0,esk5_0)) != esk1_1(k3_zfmisc_1(k2_zfmisc_1(esk2_0,X1),X2,X3)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_33]),c_0_94])).

cnf(c_0_96,negated_conjecture,
    ( k3_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0,esk5_0) = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | v1_xboole_0(esk2_0) ),
    inference(ef,[status(thm)],[c_0_95])).

cnf(c_0_97,plain,
    ( k4_zfmisc_1(X2,X3,X4,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_98,plain,
    ( k4_zfmisc_1(X2,X3,X1,X4) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_99,plain,
    ( k4_zfmisc_1(X2,X1,X3,X4) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_100,plain,
    ( k4_zfmisc_1(X1,X2,X3,X4) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_101,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | v1_xboole_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_96]),c_0_33])).

cnf(c_0_102,plain,
    ( k3_zfmisc_1(k2_zfmisc_1(X2,X3),X4,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_97,c_0_25])).

cnf(c_0_103,plain,
    ( k3_zfmisc_1(k2_zfmisc_1(X2,X3),X1,X4) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_98,c_0_25])).

cnf(c_0_104,plain,
    ( k3_zfmisc_1(k2_zfmisc_1(X2,X1),X3,X4) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_99,c_0_25])).

cnf(c_0_105,plain,
    ( k3_zfmisc_1(k2_zfmisc_1(X1,X2),X3,X4) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_100,c_0_25])).

fof(c_0_106,plain,(
    ! [X36] :
      ( ~ r1_tarski(X36,k1_xboole_0)
      | X36 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).

cnf(c_0_107,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_101]),c_0_33])).

cnf(c_0_108,plain,
    ( k3_zfmisc_1(k2_zfmisc_1(X1,X2),X3,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_102])).

cnf(c_0_109,plain,
    ( k3_zfmisc_1(k2_zfmisc_1(X1,X2),k1_xboole_0,X3) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_103])).

cnf(c_0_110,plain,
    ( k3_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0),X2,X3) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_104])).

cnf(c_0_111,plain,
    ( k3_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1),X2,X3) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_105])).

cnf(c_0_112,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_106])).

cnf(c_0_113,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | r1_tarski(esk2_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_107]),c_0_108]),c_0_109]),c_0_110]),c_0_111])])).

cnf(c_0_114,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_113]),c_0_33])).

cnf(c_0_115,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | r1_tarski(esk2_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_114]),c_0_109]),c_0_110]),c_0_111]),c_0_108])])).

cnf(c_0_116,negated_conjecture,
    ( esk3_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_115]),c_0_33])).

cnf(c_0_117,negated_conjecture,
    ( r1_tarski(esk2_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_116]),c_0_110]),c_0_116]),c_0_111]),c_0_116]),c_0_108]),c_0_116]),c_0_109])])).

cnf(c_0_118,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_117]),c_0_33]),
    [proof]).

%------------------------------------------------------------------------------
