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
% DateTime   : Thu Dec  3 11:00:17 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 297 expanded)
%              Number of clauses        :   48 ( 135 expanded)
%              Number of leaves         :   11 (  72 expanded)
%              Depth                    :   14
%              Number of atoms          :  202 (1061 expanded)
%              Number of equality atoms :  124 ( 549 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   15 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t71_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5] :
      ( m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))
     => ( ! [X6] :
            ( m1_subset_1(X6,X1)
           => ! [X7] :
                ( m1_subset_1(X7,X2)
               => ! [X8] :
                    ( m1_subset_1(X8,X3)
                   => ( X5 = k3_mcart_1(X6,X7,X8)
                     => X4 = X8 ) ) ) )
       => ( X1 = k1_xboole_0
          | X2 = k1_xboole_0
          | X3 = k1_xboole_0
          | X4 = k7_mcart_1(X1,X2,X3,X5) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_mcart_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

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

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(t10_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
     => ( r2_hidden(k1_mcart_1(X1),X2)
        & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(l139_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
        & ! [X4,X5] : k4_tarski(X4,X5) != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l139_zfmisc_1)).

fof(t7_mcart_1,axiom,(
    ! [X1,X2] :
      ( k1_mcart_1(k4_tarski(X1,X2)) = X1
      & k2_mcart_1(k4_tarski(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

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
                       => X4 = X8 ) ) ) )
         => ( X1 = k1_xboole_0
            | X2 = k1_xboole_0
            | X3 = k1_xboole_0
            | X4 = k7_mcart_1(X1,X2,X3,X5) ) ) ) ),
    inference(assume_negation,[status(cth)],[t71_mcart_1])).

fof(c_0_12,negated_conjecture,(
    ! [X41,X42,X43] :
      ( m1_subset_1(esk7_0,k3_zfmisc_1(esk3_0,esk4_0,esk5_0))
      & ( ~ m1_subset_1(X41,esk3_0)
        | ~ m1_subset_1(X42,esk4_0)
        | ~ m1_subset_1(X43,esk5_0)
        | esk7_0 != k3_mcart_1(X41,X42,X43)
        | esk6_0 = X43 )
      & esk3_0 != k1_xboole_0
      & esk4_0 != k1_xboole_0
      & esk5_0 != k1_xboole_0
      & esk6_0 != k7_mcart_1(esk3_0,esk4_0,esk5_0,esk7_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])])).

fof(c_0_13,plain,(
    ! [X24,X25,X26] : k3_zfmisc_1(X24,X25,X26) = k2_zfmisc_1(k2_zfmisc_1(X24,X25),X26) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_14,plain,(
    ! [X21,X22,X23] : k3_mcart_1(X21,X22,X23) = k4_tarski(k4_tarski(X21,X22),X23) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

fof(c_0_15,plain,(
    ! [X19,X20] :
      ( ~ m1_subset_1(X19,X20)
      | v1_xboole_0(X20)
      | r2_hidden(X19,X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk7_0,k3_zfmisc_1(esk3_0,esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( esk6_0 = X3
    | ~ m1_subset_1(X1,esk3_0)
    | ~ m1_subset_1(X2,esk4_0)
    | ~ m1_subset_1(X3,esk5_0)
    | esk7_0 != k3_mcart_1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_20,plain,(
    ! [X17,X18] :
      ( ~ r2_hidden(X17,X18)
      | m1_subset_1(X17,X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

fof(c_0_21,plain,(
    ! [X30,X31,X32,X33] :
      ( ( k5_mcart_1(X30,X31,X32,X33) = k1_mcart_1(k1_mcart_1(X33))
        | ~ m1_subset_1(X33,k3_zfmisc_1(X30,X31,X32))
        | X30 = k1_xboole_0
        | X31 = k1_xboole_0
        | X32 = k1_xboole_0 )
      & ( k6_mcart_1(X30,X31,X32,X33) = k2_mcart_1(k1_mcart_1(X33))
        | ~ m1_subset_1(X33,k3_zfmisc_1(X30,X31,X32))
        | X30 = k1_xboole_0
        | X31 = k1_xboole_0
        | X32 = k1_xboole_0 )
      & ( k7_mcart_1(X30,X31,X32,X33) = k2_mcart_1(X33)
        | ~ m1_subset_1(X33,k3_zfmisc_1(X30,X31,X32))
        | X30 = k1_xboole_0
        | X31 = k1_xboole_0
        | X32 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_mcart_1])])])])).

fof(c_0_22,plain,(
    ! [X9] :
      ( ~ v1_xboole_0(X9)
      | X9 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_23,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk7_0,k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0)) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( esk6_0 = X3
    | esk7_0 != k4_tarski(k4_tarski(X1,X2),X3)
    | ~ m1_subset_1(X3,esk5_0)
    | ~ m1_subset_1(X2,esk4_0)
    | ~ m1_subset_1(X1,esk3_0) ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_26,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_28,plain,(
    ! [X27,X28,X29] :
      ( ( r2_hidden(k1_mcart_1(X27),X28)
        | ~ r2_hidden(X27,k2_zfmisc_1(X28,X29)) )
      & ( r2_hidden(k2_mcart_1(X27),X29)
        | ~ r2_hidden(X27,k2_zfmisc_1(X28,X29)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).

cnf(c_0_29,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk7_0,k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0))
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( esk6_0 = X1
    | esk7_0 != k4_tarski(k4_tarski(X2,X3),X1)
    | ~ m1_subset_1(X3,esk4_0)
    | ~ m1_subset_1(X2,esk3_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_32,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4)
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_27,c_0_17])).

cnf(c_0_33,negated_conjecture,
    ( esk5_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_34,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_35,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_36,plain,(
    ! [X10,X11,X12] :
      ( ~ r2_hidden(X10,k2_zfmisc_1(X11,X12))
      | k4_tarski(esk1_1(X10),esk2_1(X10)) = X10 ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[l139_zfmisc_1])])])])])).

cnf(c_0_37,plain,
    ( r2_hidden(k1_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_38,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0) = k1_xboole_0
    | r2_hidden(esk7_0,k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_39,negated_conjecture,
    ( esk6_0 = X1
    | esk7_0 != k4_tarski(k4_tarski(X2,X3),X1)
    | ~ m1_subset_1(X2,esk3_0)
    | ~ r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X3,esk4_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_26])).

cnf(c_0_40,plain,
    ( r2_hidden(k2_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_41,negated_conjecture,
    ( esk6_0 != k7_mcart_1(esk3_0,esk4_0,esk5_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_42,negated_conjecture,
    ( k7_mcart_1(esk3_0,esk4_0,esk5_0,esk7_0) = k2_mcart_1(esk7_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_24]),c_0_33]),c_0_34]),c_0_35])).

fof(c_0_43,plain,(
    ! [X34,X35] :
      ( k1_mcart_1(k4_tarski(X34,X35)) = X34
      & k2_mcart_1(k4_tarski(X34,X35)) = X35 ) ),
    inference(variable_rename,[status(thm)],[t7_mcart_1])).

cnf(c_0_44,plain,
    ( k4_tarski(esk1_1(X1),esk2_1(X1)) = X1
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_45,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0) = k1_xboole_0
    | r2_hidden(k1_mcart_1(esk7_0),k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_46,negated_conjecture,
    ( esk6_0 = X1
    | esk7_0 != k4_tarski(k4_tarski(X2,X3),X1)
    | ~ r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X3,esk4_0)
    | ~ r2_hidden(X2,esk3_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_26])).

cnf(c_0_47,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0) = k1_xboole_0
    | r2_hidden(k2_mcart_1(esk7_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_38])).

cnf(c_0_48,negated_conjecture,
    ( esk6_0 != k2_mcart_1(esk7_0) ),
    inference(rw,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_49,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_50,negated_conjecture,
    ( k4_tarski(esk1_1(k1_mcart_1(esk7_0)),esk2_1(k1_mcart_1(esk7_0))) = k1_mcart_1(esk7_0)
    | k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_51,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0) = k1_xboole_0
    | k4_tarski(esk1_1(esk7_0),esk2_1(esk7_0)) = esk7_0 ),
    inference(spm,[status(thm)],[c_0_44,c_0_38])).

cnf(c_0_52,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0) = k1_xboole_0
    | k4_tarski(k4_tarski(X1,X2),k2_mcart_1(esk7_0)) != esk7_0
    | ~ r2_hidden(X2,esk4_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48])).

cnf(c_0_53,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0) = k1_xboole_0
    | r2_hidden(k2_mcart_1(k1_mcart_1(esk7_0)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_45])).

cnf(c_0_54,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0) = k1_xboole_0
    | esk1_1(k1_mcart_1(esk7_0)) = k1_mcart_1(k1_mcart_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_55,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_56,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0) = k1_xboole_0
    | esk1_1(esk7_0) = k1_mcart_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_51])).

cnf(c_0_57,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0) = k1_xboole_0
    | k4_tarski(k4_tarski(X1,k2_mcart_1(k1_mcart_1(esk7_0))),k2_mcart_1(esk7_0)) != esk7_0
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_58,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0) = k1_xboole_0
    | r2_hidden(k1_mcart_1(k1_mcart_1(esk7_0)),esk3_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_45])).

cnf(c_0_59,negated_conjecture,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(esk7_0)),esk2_1(k1_mcart_1(esk7_0))) = k1_mcart_1(esk7_0)
    | k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_50,c_0_54])).

cnf(c_0_60,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0) = k1_xboole_0
    | esk2_1(k1_mcart_1(esk7_0)) = k2_mcart_1(k1_mcart_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_50])).

cnf(c_0_61,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk7_0),esk2_1(esk7_0)) = esk7_0
    | k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_51,c_0_56])).

cnf(c_0_62,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0) = k1_xboole_0
    | esk2_1(esk7_0) = k2_mcart_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_51])).

fof(c_0_63,plain,(
    ! [X15,X16] :
      ( ( k2_zfmisc_1(X15,X16) != k1_xboole_0
        | X15 = k1_xboole_0
        | X16 = k1_xboole_0 )
      & ( X15 != k1_xboole_0
        | k2_zfmisc_1(X15,X16) = k1_xboole_0 )
      & ( X16 != k1_xboole_0
        | k2_zfmisc_1(X15,X16) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_64,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0) = k1_xboole_0
    | k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(esk7_0)),k2_mcart_1(k1_mcart_1(esk7_0))),k2_mcart_1(esk7_0)) != esk7_0 ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_65,negated_conjecture,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(esk7_0)),k2_mcart_1(k1_mcart_1(esk7_0))) = k1_mcart_1(esk7_0)
    | k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_66,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0) = k1_xboole_0
    | k4_tarski(k1_mcart_1(esk7_0),k2_mcart_1(esk7_0)) = esk7_0 ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_67,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | k2_zfmisc_1(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_68,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0) = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_66])).

cnf(c_0_69,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,esk4_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_33])).

cnf(c_0_70,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_69]),c_0_34]),c_0_35]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:52:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.18/0.37  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S0YI
% 0.18/0.37  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.18/0.37  #
% 0.18/0.37  # Preprocessing time       : 0.029 s
% 0.18/0.37  # Presaturation interreduction done
% 0.18/0.37  
% 0.18/0.37  # Proof found!
% 0.18/0.37  # SZS status Theorem
% 0.18/0.37  # SZS output start CNFRefutation
% 0.18/0.37  fof(t71_mcart_1, conjecture, ![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))=>(![X6]:(m1_subset_1(X6,X1)=>![X7]:(m1_subset_1(X7,X2)=>![X8]:(m1_subset_1(X8,X3)=>(X5=k3_mcart_1(X6,X7,X8)=>X4=X8))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k7_mcart_1(X1,X2,X3,X5)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_mcart_1)).
% 0.18/0.37  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 0.18/0.37  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 0.18/0.37  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 0.18/0.37  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 0.18/0.37  fof(t50_mcart_1, axiom, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>((k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))&k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4)))&k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_mcart_1)).
% 0.18/0.37  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.18/0.37  fof(t10_mcart_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(X2,X3))=>(r2_hidden(k1_mcart_1(X1),X2)&r2_hidden(k2_mcart_1(X1),X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 0.18/0.37  fof(l139_zfmisc_1, axiom, ![X1, X2, X3]:~((r2_hidden(X1,k2_zfmisc_1(X2,X3))&![X4, X5]:k4_tarski(X4,X5)!=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l139_zfmisc_1)).
% 0.18/0.37  fof(t7_mcart_1, axiom, ![X1, X2]:(k1_mcart_1(k4_tarski(X1,X2))=X1&k2_mcart_1(k4_tarski(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 0.18/0.37  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.18/0.37  fof(c_0_11, negated_conjecture, ~(![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))=>(![X6]:(m1_subset_1(X6,X1)=>![X7]:(m1_subset_1(X7,X2)=>![X8]:(m1_subset_1(X8,X3)=>(X5=k3_mcart_1(X6,X7,X8)=>X4=X8))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k7_mcart_1(X1,X2,X3,X5))))), inference(assume_negation,[status(cth)],[t71_mcart_1])).
% 0.18/0.37  fof(c_0_12, negated_conjecture, ![X41, X42, X43]:(m1_subset_1(esk7_0,k3_zfmisc_1(esk3_0,esk4_0,esk5_0))&((~m1_subset_1(X41,esk3_0)|(~m1_subset_1(X42,esk4_0)|(~m1_subset_1(X43,esk5_0)|(esk7_0!=k3_mcart_1(X41,X42,X43)|esk6_0=X43))))&(((esk3_0!=k1_xboole_0&esk4_0!=k1_xboole_0)&esk5_0!=k1_xboole_0)&esk6_0!=k7_mcart_1(esk3_0,esk4_0,esk5_0,esk7_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])])).
% 0.18/0.37  fof(c_0_13, plain, ![X24, X25, X26]:k3_zfmisc_1(X24,X25,X26)=k2_zfmisc_1(k2_zfmisc_1(X24,X25),X26), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 0.18/0.37  fof(c_0_14, plain, ![X21, X22, X23]:k3_mcart_1(X21,X22,X23)=k4_tarski(k4_tarski(X21,X22),X23), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 0.18/0.37  fof(c_0_15, plain, ![X19, X20]:(~m1_subset_1(X19,X20)|(v1_xboole_0(X20)|r2_hidden(X19,X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.18/0.37  cnf(c_0_16, negated_conjecture, (m1_subset_1(esk7_0,k3_zfmisc_1(esk3_0,esk4_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.37  cnf(c_0_17, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.37  cnf(c_0_18, negated_conjecture, (esk6_0=X3|~m1_subset_1(X1,esk3_0)|~m1_subset_1(X2,esk4_0)|~m1_subset_1(X3,esk5_0)|esk7_0!=k3_mcart_1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.37  cnf(c_0_19, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.37  fof(c_0_20, plain, ![X17, X18]:(~r2_hidden(X17,X18)|m1_subset_1(X17,X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.18/0.37  fof(c_0_21, plain, ![X30, X31, X32, X33]:(((k5_mcart_1(X30,X31,X32,X33)=k1_mcart_1(k1_mcart_1(X33))|~m1_subset_1(X33,k3_zfmisc_1(X30,X31,X32))|(X30=k1_xboole_0|X31=k1_xboole_0|X32=k1_xboole_0))&(k6_mcart_1(X30,X31,X32,X33)=k2_mcart_1(k1_mcart_1(X33))|~m1_subset_1(X33,k3_zfmisc_1(X30,X31,X32))|(X30=k1_xboole_0|X31=k1_xboole_0|X32=k1_xboole_0)))&(k7_mcart_1(X30,X31,X32,X33)=k2_mcart_1(X33)|~m1_subset_1(X33,k3_zfmisc_1(X30,X31,X32))|(X30=k1_xboole_0|X31=k1_xboole_0|X32=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_mcart_1])])])])).
% 0.18/0.37  fof(c_0_22, plain, ![X9]:(~v1_xboole_0(X9)|X9=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.18/0.37  cnf(c_0_23, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.37  cnf(c_0_24, negated_conjecture, (m1_subset_1(esk7_0,k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0))), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 0.18/0.37  cnf(c_0_25, negated_conjecture, (esk6_0=X3|esk7_0!=k4_tarski(k4_tarski(X1,X2),X3)|~m1_subset_1(X3,esk5_0)|~m1_subset_1(X2,esk4_0)|~m1_subset_1(X1,esk3_0)), inference(rw,[status(thm)],[c_0_18, c_0_19])).
% 0.18/0.37  cnf(c_0_26, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.37  cnf(c_0_27, plain, (k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.18/0.37  fof(c_0_28, plain, ![X27, X28, X29]:((r2_hidden(k1_mcart_1(X27),X28)|~r2_hidden(X27,k2_zfmisc_1(X28,X29)))&(r2_hidden(k2_mcart_1(X27),X29)|~r2_hidden(X27,k2_zfmisc_1(X28,X29)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).
% 0.18/0.37  cnf(c_0_29, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.18/0.37  cnf(c_0_30, negated_conjecture, (r2_hidden(esk7_0,k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0))|v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.18/0.37  cnf(c_0_31, negated_conjecture, (esk6_0=X1|esk7_0!=k4_tarski(k4_tarski(X2,X3),X1)|~m1_subset_1(X3,esk4_0)|~m1_subset_1(X2,esk3_0)|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.18/0.37  cnf(c_0_32, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_27, c_0_17])).
% 0.18/0.37  cnf(c_0_33, negated_conjecture, (esk5_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.37  cnf(c_0_34, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.37  cnf(c_0_35, negated_conjecture, (esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.37  fof(c_0_36, plain, ![X10, X11, X12]:(~r2_hidden(X10,k2_zfmisc_1(X11,X12))|k4_tarski(esk1_1(X10),esk2_1(X10))=X10), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[l139_zfmisc_1])])])])])).
% 0.18/0.37  cnf(c_0_37, plain, (r2_hidden(k1_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.18/0.37  cnf(c_0_38, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0)=k1_xboole_0|r2_hidden(esk7_0,k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.18/0.37  cnf(c_0_39, negated_conjecture, (esk6_0=X1|esk7_0!=k4_tarski(k4_tarski(X2,X3),X1)|~m1_subset_1(X2,esk3_0)|~r2_hidden(X1,esk5_0)|~r2_hidden(X3,esk4_0)), inference(spm,[status(thm)],[c_0_31, c_0_26])).
% 0.18/0.37  cnf(c_0_40, plain, (r2_hidden(k2_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.18/0.37  cnf(c_0_41, negated_conjecture, (esk6_0!=k7_mcart_1(esk3_0,esk4_0,esk5_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.37  cnf(c_0_42, negated_conjecture, (k7_mcart_1(esk3_0,esk4_0,esk5_0,esk7_0)=k2_mcart_1(esk7_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_24]), c_0_33]), c_0_34]), c_0_35])).
% 0.18/0.37  fof(c_0_43, plain, ![X34, X35]:(k1_mcart_1(k4_tarski(X34,X35))=X34&k2_mcart_1(k4_tarski(X34,X35))=X35), inference(variable_rename,[status(thm)],[t7_mcart_1])).
% 0.18/0.37  cnf(c_0_44, plain, (k4_tarski(esk1_1(X1),esk2_1(X1))=X1|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.18/0.37  cnf(c_0_45, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0)=k1_xboole_0|r2_hidden(k1_mcart_1(esk7_0),k2_zfmisc_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.18/0.37  cnf(c_0_46, negated_conjecture, (esk6_0=X1|esk7_0!=k4_tarski(k4_tarski(X2,X3),X1)|~r2_hidden(X1,esk5_0)|~r2_hidden(X3,esk4_0)|~r2_hidden(X2,esk3_0)), inference(spm,[status(thm)],[c_0_39, c_0_26])).
% 0.18/0.37  cnf(c_0_47, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0)=k1_xboole_0|r2_hidden(k2_mcart_1(esk7_0),esk5_0)), inference(spm,[status(thm)],[c_0_40, c_0_38])).
% 0.18/0.37  cnf(c_0_48, negated_conjecture, (esk6_0!=k2_mcart_1(esk7_0)), inference(rw,[status(thm)],[c_0_41, c_0_42])).
% 0.18/0.37  cnf(c_0_49, plain, (k1_mcart_1(k4_tarski(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.18/0.37  cnf(c_0_50, negated_conjecture, (k4_tarski(esk1_1(k1_mcart_1(esk7_0)),esk2_1(k1_mcart_1(esk7_0)))=k1_mcart_1(esk7_0)|k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.18/0.37  cnf(c_0_51, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0)=k1_xboole_0|k4_tarski(esk1_1(esk7_0),esk2_1(esk7_0))=esk7_0), inference(spm,[status(thm)],[c_0_44, c_0_38])).
% 0.18/0.37  cnf(c_0_52, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0)=k1_xboole_0|k4_tarski(k4_tarski(X1,X2),k2_mcart_1(esk7_0))!=esk7_0|~r2_hidden(X2,esk4_0)|~r2_hidden(X1,esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48])).
% 0.18/0.37  cnf(c_0_53, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0)=k1_xboole_0|r2_hidden(k2_mcart_1(k1_mcart_1(esk7_0)),esk4_0)), inference(spm,[status(thm)],[c_0_40, c_0_45])).
% 0.18/0.37  cnf(c_0_54, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0)=k1_xboole_0|esk1_1(k1_mcart_1(esk7_0))=k1_mcart_1(k1_mcart_1(esk7_0))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.18/0.37  cnf(c_0_55, plain, (k2_mcart_1(k4_tarski(X1,X2))=X2), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.18/0.37  cnf(c_0_56, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0)=k1_xboole_0|esk1_1(esk7_0)=k1_mcart_1(esk7_0)), inference(spm,[status(thm)],[c_0_49, c_0_51])).
% 0.18/0.37  cnf(c_0_57, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0)=k1_xboole_0|k4_tarski(k4_tarski(X1,k2_mcart_1(k1_mcart_1(esk7_0))),k2_mcart_1(esk7_0))!=esk7_0|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.18/0.37  cnf(c_0_58, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0)=k1_xboole_0|r2_hidden(k1_mcart_1(k1_mcart_1(esk7_0)),esk3_0)), inference(spm,[status(thm)],[c_0_37, c_0_45])).
% 0.18/0.37  cnf(c_0_59, negated_conjecture, (k4_tarski(k1_mcart_1(k1_mcart_1(esk7_0)),esk2_1(k1_mcart_1(esk7_0)))=k1_mcart_1(esk7_0)|k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_50, c_0_54])).
% 0.18/0.37  cnf(c_0_60, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0)=k1_xboole_0|esk2_1(k1_mcart_1(esk7_0))=k2_mcart_1(k1_mcart_1(esk7_0))), inference(spm,[status(thm)],[c_0_55, c_0_50])).
% 0.18/0.37  cnf(c_0_61, negated_conjecture, (k4_tarski(k1_mcart_1(esk7_0),esk2_1(esk7_0))=esk7_0|k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_51, c_0_56])).
% 0.18/0.37  cnf(c_0_62, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0)=k1_xboole_0|esk2_1(esk7_0)=k2_mcart_1(esk7_0)), inference(spm,[status(thm)],[c_0_55, c_0_51])).
% 0.18/0.37  fof(c_0_63, plain, ![X15, X16]:((k2_zfmisc_1(X15,X16)!=k1_xboole_0|(X15=k1_xboole_0|X16=k1_xboole_0))&((X15!=k1_xboole_0|k2_zfmisc_1(X15,X16)=k1_xboole_0)&(X16!=k1_xboole_0|k2_zfmisc_1(X15,X16)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.18/0.37  cnf(c_0_64, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0)=k1_xboole_0|k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(esk7_0)),k2_mcart_1(k1_mcart_1(esk7_0))),k2_mcart_1(esk7_0))!=esk7_0), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.18/0.37  cnf(c_0_65, negated_conjecture, (k4_tarski(k1_mcart_1(k1_mcart_1(esk7_0)),k2_mcart_1(k1_mcart_1(esk7_0)))=k1_mcart_1(esk7_0)|k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.18/0.37  cnf(c_0_66, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0)=k1_xboole_0|k4_tarski(k1_mcart_1(esk7_0),k2_mcart_1(esk7_0))=esk7_0), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.18/0.37  cnf(c_0_67, plain, (X1=k1_xboole_0|X2=k1_xboole_0|k2_zfmisc_1(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.18/0.37  cnf(c_0_68, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0)=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_66])).
% 0.18/0.37  cnf(c_0_69, negated_conjecture, (k2_zfmisc_1(esk3_0,esk4_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_33])).
% 0.18/0.37  cnf(c_0_70, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_69]), c_0_34]), c_0_35]), ['proof']).
% 0.18/0.37  # SZS output end CNFRefutation
% 0.18/0.37  # Proof object total steps             : 71
% 0.18/0.37  # Proof object clause steps            : 48
% 0.18/0.37  # Proof object formula steps           : 23
% 0.18/0.37  # Proof object conjectures             : 38
% 0.18/0.37  # Proof object clause conjectures      : 35
% 0.18/0.37  # Proof object formula conjectures     : 3
% 0.18/0.37  # Proof object initial clauses used    : 18
% 0.18/0.37  # Proof object initial formulas used   : 11
% 0.18/0.37  # Proof object generating inferences   : 26
% 0.18/0.37  # Proof object simplifying inferences  : 12
% 0.18/0.37  # Training examples: 0 positive, 0 negative
% 0.18/0.37  # Parsed axioms                        : 11
% 0.18/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.37  # Initial clauses                      : 22
% 0.18/0.37  # Removed in clause preprocessing      : 2
% 0.18/0.37  # Initial clauses in saturation        : 20
% 0.18/0.37  # Processed clauses                    : 87
% 0.18/0.37  # ...of these trivial                  : 0
% 0.18/0.37  # ...subsumed                          : 8
% 0.18/0.37  # ...remaining for further processing  : 79
% 0.18/0.37  # Other redundant clauses eliminated   : 2
% 0.18/0.37  # Clauses deleted for lack of memory   : 0
% 0.18/0.37  # Backward-subsumed                    : 0
% 0.18/0.37  # Backward-rewritten                   : 24
% 0.18/0.37  # Generated clauses                    : 76
% 0.18/0.37  # ...of the previous two non-trivial   : 73
% 0.18/0.37  # Contextual simplify-reflections      : 1
% 0.18/0.37  # Paramodulations                      : 74
% 0.18/0.37  # Factorizations                       : 0
% 0.18/0.37  # Equation resolutions                 : 2
% 0.18/0.37  # Propositional unsat checks           : 0
% 0.18/0.37  #    Propositional check models        : 0
% 0.18/0.37  #    Propositional check unsatisfiable : 0
% 0.18/0.37  #    Propositional clauses             : 0
% 0.18/0.37  #    Propositional clauses after purity: 0
% 0.18/0.37  #    Propositional unsat core size     : 0
% 0.18/0.37  #    Propositional preprocessing time  : 0.000
% 0.18/0.37  #    Propositional encoding time       : 0.000
% 0.18/0.37  #    Propositional solver time         : 0.000
% 0.18/0.37  #    Success case prop preproc time    : 0.000
% 0.18/0.37  #    Success case prop encoding time   : 0.000
% 0.18/0.37  #    Success case prop solver time     : 0.000
% 0.18/0.37  # Current number of processed clauses  : 33
% 0.18/0.37  #    Positive orientable unit clauses  : 9
% 0.18/0.37  #    Positive unorientable unit clauses: 0
% 0.18/0.37  #    Negative unit clauses             : 4
% 0.18/0.37  #    Non-unit-clauses                  : 20
% 0.18/0.37  # Current number of unprocessed clauses: 18
% 0.18/0.37  # ...number of literals in the above   : 48
% 0.18/0.37  # Current number of archived formulas  : 0
% 0.18/0.37  # Current number of archived clauses   : 46
% 0.18/0.37  # Clause-clause subsumption calls (NU) : 234
% 0.18/0.37  # Rec. Clause-clause subsumption calls : 120
% 0.18/0.37  # Non-unit clause-clause subsumptions  : 9
% 0.18/0.37  # Unit Clause-clause subsumption calls : 8
% 0.18/0.37  # Rewrite failures with RHS unbound    : 0
% 0.18/0.37  # BW rewrite match attempts            : 3
% 0.18/0.37  # BW rewrite match successes           : 3
% 0.18/0.37  # Condensation attempts                : 0
% 0.18/0.37  # Condensation successes               : 0
% 0.18/0.37  # Termbank termtop insertions          : 2939
% 0.18/0.37  
% 0.18/0.37  # -------------------------------------------------
% 0.18/0.37  # User time                : 0.031 s
% 0.18/0.37  # System time              : 0.006 s
% 0.18/0.37  # Total time               : 0.037 s
% 0.18/0.37  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
