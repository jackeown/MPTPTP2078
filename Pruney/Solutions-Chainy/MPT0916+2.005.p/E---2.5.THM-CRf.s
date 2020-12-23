%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:21 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 216 expanded)
%              Number of clauses        :   50 ( 100 expanded)
%              Number of leaves         :    7 (  53 expanded)
%              Depth                    :   12
%              Number of atoms          :  174 ( 722 expanded)
%              Number of equality atoms :   72 ( 141 expanded)
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

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_7,negated_conjecture,(
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

fof(c_0_8,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(esk3_0))
    & m1_subset_1(esk7_0,k1_zfmisc_1(esk4_0))
    & m1_subset_1(esk8_0,k1_zfmisc_1(esk5_0))
    & m1_subset_1(esk9_0,k3_zfmisc_1(esk3_0,esk4_0,esk5_0))
    & r2_hidden(esk9_0,k3_zfmisc_1(esk6_0,esk7_0,esk8_0))
    & ( ~ r2_hidden(k5_mcart_1(esk3_0,esk4_0,esk5_0,esk9_0),esk6_0)
      | ~ r2_hidden(k6_mcart_1(esk3_0,esk4_0,esk5_0,esk9_0),esk7_0)
      | ~ r2_hidden(k7_mcart_1(esk3_0,esk4_0,esk5_0,esk9_0),esk8_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_9,plain,(
    ! [X24,X25,X26] : k3_zfmisc_1(X24,X25,X26) = k2_zfmisc_1(k2_zfmisc_1(X24,X25),X26) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_10,plain,(
    ! [X27,X28,X29] :
      ( ( r2_hidden(k1_mcart_1(X27),X28)
        | ~ r2_hidden(X27,k2_zfmisc_1(X28,X29)) )
      & ( r2_hidden(k2_mcart_1(X27),X29)
        | ~ r2_hidden(X27,k2_zfmisc_1(X28,X29)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).

cnf(c_0_11,negated_conjecture,
    ( r2_hidden(esk9_0,k3_zfmisc_1(esk6_0,esk7_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_13,plain,(
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

cnf(c_0_14,plain,
    ( r2_hidden(k1_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( r2_hidden(esk9_0,k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0)) ),
    inference(rw,[status(thm)],[c_0_11,c_0_12])).

fof(c_0_16,plain,(
    ! [X8,X9,X10] :
      ( ( ~ v1_xboole_0(X8)
        | ~ r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_1(X10),X10)
        | v1_xboole_0(X10) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_17,plain,
    ( r2_hidden(k2_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( k5_mcart_1(X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(X4))
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk9_0,k3_zfmisc_1(esk3_0,esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_20,plain,
    ( k6_mcart_1(X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk9_0),k2_zfmisc_1(esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

fof(c_0_22,plain,(
    ! [X16,X17,X18] :
      ( ~ m1_subset_1(X17,k1_zfmisc_1(X16))
      | ~ r2_hidden(X18,X17)
      | r2_hidden(X18,X16) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

cnf(c_0_23,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(k2_mcart_1(esk9_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_15])).

cnf(c_0_25,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k5_mcart_1(X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(X4))
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_18,c_0_12])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk9_0,k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0)) ),
    inference(rw,[status(thm)],[c_0_19,c_0_12])).

cnf(c_0_27,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k6_mcart_1(X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_20,c_0_12])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(esk9_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_21])).

cnf(c_0_29,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_31,negated_conjecture,
    ( ~ v1_xboole_0(esk8_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_32,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(esk9_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_21])).

cnf(c_0_34,negated_conjecture,
    ( k1_mcart_1(k1_mcart_1(esk9_0)) = k5_mcart_1(esk3_0,esk4_0,esk5_0,esk9_0)
    | esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_35,negated_conjecture,
    ( k2_mcart_1(k1_mcart_1(esk9_0)) = k6_mcart_1(esk3_0,esk4_0,esk5_0,esk9_0)
    | esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_27,c_0_26])).

cnf(c_0_36,plain,
    ( k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_38,negated_conjecture,
    ( ~ v1_xboole_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_28])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk1_1(esk8_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_41,negated_conjecture,
    ( ~ r2_hidden(k5_mcart_1(esk3_0,esk4_0,esk5_0,esk9_0),esk6_0)
    | ~ r2_hidden(k6_mcart_1(esk3_0,esk4_0,esk5_0,esk9_0),esk7_0)
    | ~ r2_hidden(k7_mcart_1(esk3_0,esk4_0,esk5_0,esk9_0),esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_42,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | r2_hidden(k5_mcart_1(esk3_0,esk4_0,esk5_0,esk9_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_43,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | r2_hidden(k6_mcart_1(esk3_0,esk4_0,esk5_0,esk9_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_35])).

cnf(c_0_44,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4)
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_36,c_0_12])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_46,negated_conjecture,
    ( ~ v1_xboole_0(esk6_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_33])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_37])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk1_1(esk7_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_32])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk1_1(esk8_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_50,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | ~ r2_hidden(k7_mcart_1(esk3_0,esk4_0,esk5_0,esk9_0),esk8_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43])).

cnf(c_0_51,negated_conjecture,
    ( k7_mcart_1(esk3_0,esk4_0,esk5_0,esk9_0) = k2_mcart_1(esk9_0)
    | esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_44,c_0_26])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_45])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(esk1_1(esk6_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_32])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk1_1(esk7_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_55,negated_conjecture,
    ( ~ v1_xboole_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_49])).

cnf(c_0_56,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_24])])).

cnf(c_0_57,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(esk1_1(esk6_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_59,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_54])).

cnf(c_0_60,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57])])).

cnf(c_0_61,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_58])).

cnf(c_0_62,negated_conjecture,
    ( esk3_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_57])])).

cnf(c_0_63,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_62]),c_0_57])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:26:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_SE_CS_SP_PI_PS_S2SI
% 0.14/0.38  # and selection function SelectNewComplexAHP.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.028 s
% 0.14/0.38  # Presaturation interreduction done
% 0.14/0.38  
% 0.14/0.38  # Proof found!
% 0.14/0.38  # SZS status Theorem
% 0.14/0.38  # SZS output start CNFRefutation
% 0.14/0.38  fof(t76_mcart_1, conjecture, ![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(X1))=>![X5]:(m1_subset_1(X5,k1_zfmisc_1(X2))=>![X6]:(m1_subset_1(X6,k1_zfmisc_1(X3))=>![X7]:(m1_subset_1(X7,k3_zfmisc_1(X1,X2,X3))=>(r2_hidden(X7,k3_zfmisc_1(X4,X5,X6))=>((r2_hidden(k5_mcart_1(X1,X2,X3,X7),X4)&r2_hidden(k6_mcart_1(X1,X2,X3,X7),X5))&r2_hidden(k7_mcart_1(X1,X2,X3,X7),X6))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_mcart_1)).
% 0.14/0.38  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 0.14/0.38  fof(t10_mcart_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(X2,X3))=>(r2_hidden(k1_mcart_1(X1),X2)&r2_hidden(k2_mcart_1(X1),X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 0.14/0.38  fof(t50_mcart_1, axiom, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>((k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))&k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4)))&k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_mcart_1)).
% 0.14/0.38  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.14/0.38  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 0.14/0.38  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.14/0.38  fof(c_0_7, negated_conjecture, ~(![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(X1))=>![X5]:(m1_subset_1(X5,k1_zfmisc_1(X2))=>![X6]:(m1_subset_1(X6,k1_zfmisc_1(X3))=>![X7]:(m1_subset_1(X7,k3_zfmisc_1(X1,X2,X3))=>(r2_hidden(X7,k3_zfmisc_1(X4,X5,X6))=>((r2_hidden(k5_mcart_1(X1,X2,X3,X7),X4)&r2_hidden(k6_mcart_1(X1,X2,X3,X7),X5))&r2_hidden(k7_mcart_1(X1,X2,X3,X7),X6)))))))), inference(assume_negation,[status(cth)],[t76_mcart_1])).
% 0.14/0.38  fof(c_0_8, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(esk3_0))&(m1_subset_1(esk7_0,k1_zfmisc_1(esk4_0))&(m1_subset_1(esk8_0,k1_zfmisc_1(esk5_0))&(m1_subset_1(esk9_0,k3_zfmisc_1(esk3_0,esk4_0,esk5_0))&(r2_hidden(esk9_0,k3_zfmisc_1(esk6_0,esk7_0,esk8_0))&(~r2_hidden(k5_mcart_1(esk3_0,esk4_0,esk5_0,esk9_0),esk6_0)|~r2_hidden(k6_mcart_1(esk3_0,esk4_0,esk5_0,esk9_0),esk7_0)|~r2_hidden(k7_mcart_1(esk3_0,esk4_0,esk5_0,esk9_0),esk8_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.14/0.38  fof(c_0_9, plain, ![X24, X25, X26]:k3_zfmisc_1(X24,X25,X26)=k2_zfmisc_1(k2_zfmisc_1(X24,X25),X26), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 0.14/0.38  fof(c_0_10, plain, ![X27, X28, X29]:((r2_hidden(k1_mcart_1(X27),X28)|~r2_hidden(X27,k2_zfmisc_1(X28,X29)))&(r2_hidden(k2_mcart_1(X27),X29)|~r2_hidden(X27,k2_zfmisc_1(X28,X29)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).
% 0.14/0.38  cnf(c_0_11, negated_conjecture, (r2_hidden(esk9_0,k3_zfmisc_1(esk6_0,esk7_0,esk8_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.38  cnf(c_0_12, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.38  fof(c_0_13, plain, ![X30, X31, X32, X33]:(((k5_mcart_1(X30,X31,X32,X33)=k1_mcart_1(k1_mcart_1(X33))|~m1_subset_1(X33,k3_zfmisc_1(X30,X31,X32))|(X30=k1_xboole_0|X31=k1_xboole_0|X32=k1_xboole_0))&(k6_mcart_1(X30,X31,X32,X33)=k2_mcart_1(k1_mcart_1(X33))|~m1_subset_1(X33,k3_zfmisc_1(X30,X31,X32))|(X30=k1_xboole_0|X31=k1_xboole_0|X32=k1_xboole_0)))&(k7_mcart_1(X30,X31,X32,X33)=k2_mcart_1(X33)|~m1_subset_1(X33,k3_zfmisc_1(X30,X31,X32))|(X30=k1_xboole_0|X31=k1_xboole_0|X32=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_mcart_1])])])])).
% 0.14/0.38  cnf(c_0_14, plain, (r2_hidden(k1_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.38  cnf(c_0_15, negated_conjecture, (r2_hidden(esk9_0,k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0))), inference(rw,[status(thm)],[c_0_11, c_0_12])).
% 0.14/0.38  fof(c_0_16, plain, ![X8, X9, X10]:((~v1_xboole_0(X8)|~r2_hidden(X9,X8))&(r2_hidden(esk1_1(X10),X10)|v1_xboole_0(X10))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.14/0.38  cnf(c_0_17, plain, (r2_hidden(k2_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.38  cnf(c_0_18, plain, (k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.38  cnf(c_0_19, negated_conjecture, (m1_subset_1(esk9_0,k3_zfmisc_1(esk3_0,esk4_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.38  cnf(c_0_20, plain, (k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4))|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.38  cnf(c_0_21, negated_conjecture, (r2_hidden(k1_mcart_1(esk9_0),k2_zfmisc_1(esk6_0,esk7_0))), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.14/0.38  fof(c_0_22, plain, ![X16, X17, X18]:(~m1_subset_1(X17,k1_zfmisc_1(X16))|(~r2_hidden(X18,X17)|r2_hidden(X18,X16))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.14/0.38  cnf(c_0_23, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.38  cnf(c_0_24, negated_conjecture, (r2_hidden(k2_mcart_1(esk9_0),esk8_0)), inference(spm,[status(thm)],[c_0_17, c_0_15])).
% 0.14/0.38  cnf(c_0_25, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_18, c_0_12])).
% 0.14/0.38  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk9_0,k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0))), inference(rw,[status(thm)],[c_0_19, c_0_12])).
% 0.14/0.38  cnf(c_0_27, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4))|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_20, c_0_12])).
% 0.14/0.38  cnf(c_0_28, negated_conjecture, (r2_hidden(k2_mcart_1(k1_mcart_1(esk9_0)),esk7_0)), inference(spm,[status(thm)],[c_0_17, c_0_21])).
% 0.14/0.38  cnf(c_0_29, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.38  cnf(c_0_30, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.38  cnf(c_0_31, negated_conjecture, (~v1_xboole_0(esk8_0)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.14/0.38  cnf(c_0_32, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.38  cnf(c_0_33, negated_conjecture, (r2_hidden(k1_mcart_1(k1_mcart_1(esk9_0)),esk6_0)), inference(spm,[status(thm)],[c_0_14, c_0_21])).
% 0.14/0.38  cnf(c_0_34, negated_conjecture, (k1_mcart_1(k1_mcart_1(esk9_0))=k5_mcart_1(esk3_0,esk4_0,esk5_0,esk9_0)|esk3_0=k1_xboole_0|esk4_0=k1_xboole_0|esk5_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.14/0.38  cnf(c_0_35, negated_conjecture, (k2_mcart_1(k1_mcart_1(esk9_0))=k6_mcart_1(esk3_0,esk4_0,esk5_0,esk9_0)|esk3_0=k1_xboole_0|esk4_0=k1_xboole_0|esk5_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_27, c_0_26])).
% 0.14/0.38  cnf(c_0_36, plain, (k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.38  cnf(c_0_37, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.38  cnf(c_0_38, negated_conjecture, (~v1_xboole_0(esk7_0)), inference(spm,[status(thm)],[c_0_23, c_0_28])).
% 0.14/0.38  cnf(c_0_39, negated_conjecture, (r2_hidden(X1,esk5_0)|~r2_hidden(X1,esk8_0)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.14/0.38  cnf(c_0_40, negated_conjecture, (r2_hidden(esk1_1(esk8_0),esk8_0)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.14/0.38  cnf(c_0_41, negated_conjecture, (~r2_hidden(k5_mcart_1(esk3_0,esk4_0,esk5_0,esk9_0),esk6_0)|~r2_hidden(k6_mcart_1(esk3_0,esk4_0,esk5_0,esk9_0),esk7_0)|~r2_hidden(k7_mcart_1(esk3_0,esk4_0,esk5_0,esk9_0),esk8_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.38  cnf(c_0_42, negated_conjecture, (esk5_0=k1_xboole_0|esk4_0=k1_xboole_0|esk3_0=k1_xboole_0|r2_hidden(k5_mcart_1(esk3_0,esk4_0,esk5_0,esk9_0),esk6_0)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.14/0.38  cnf(c_0_43, negated_conjecture, (esk5_0=k1_xboole_0|esk4_0=k1_xboole_0|esk3_0=k1_xboole_0|r2_hidden(k6_mcart_1(esk3_0,esk4_0,esk5_0,esk9_0),esk7_0)), inference(spm,[status(thm)],[c_0_28, c_0_35])).
% 0.14/0.38  cnf(c_0_44, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_36, c_0_12])).
% 0.14/0.38  cnf(c_0_45, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.38  cnf(c_0_46, negated_conjecture, (~v1_xboole_0(esk6_0)), inference(spm,[status(thm)],[c_0_23, c_0_33])).
% 0.14/0.38  cnf(c_0_47, negated_conjecture, (r2_hidden(X1,esk4_0)|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_29, c_0_37])).
% 0.14/0.38  cnf(c_0_48, negated_conjecture, (r2_hidden(esk1_1(esk7_0),esk7_0)), inference(spm,[status(thm)],[c_0_38, c_0_32])).
% 0.14/0.38  cnf(c_0_49, negated_conjecture, (r2_hidden(esk1_1(esk8_0),esk5_0)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.14/0.38  cnf(c_0_50, negated_conjecture, (esk3_0=k1_xboole_0|esk4_0=k1_xboole_0|esk5_0=k1_xboole_0|~r2_hidden(k7_mcart_1(esk3_0,esk4_0,esk5_0,esk9_0),esk8_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43])).
% 0.14/0.38  cnf(c_0_51, negated_conjecture, (k7_mcart_1(esk3_0,esk4_0,esk5_0,esk9_0)=k2_mcart_1(esk9_0)|esk3_0=k1_xboole_0|esk4_0=k1_xboole_0|esk5_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_44, c_0_26])).
% 0.14/0.38  cnf(c_0_52, negated_conjecture, (r2_hidden(X1,esk3_0)|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_29, c_0_45])).
% 0.14/0.38  cnf(c_0_53, negated_conjecture, (r2_hidden(esk1_1(esk6_0),esk6_0)), inference(spm,[status(thm)],[c_0_46, c_0_32])).
% 0.14/0.38  cnf(c_0_54, negated_conjecture, (r2_hidden(esk1_1(esk7_0),esk4_0)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.14/0.38  cnf(c_0_55, negated_conjecture, (~v1_xboole_0(esk5_0)), inference(spm,[status(thm)],[c_0_23, c_0_49])).
% 0.14/0.38  cnf(c_0_56, negated_conjecture, (esk5_0=k1_xboole_0|esk4_0=k1_xboole_0|esk3_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_24])])).
% 0.14/0.38  cnf(c_0_57, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.14/0.38  cnf(c_0_58, negated_conjecture, (r2_hidden(esk1_1(esk6_0),esk3_0)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.14/0.38  cnf(c_0_59, negated_conjecture, (~v1_xboole_0(esk4_0)), inference(spm,[status(thm)],[c_0_23, c_0_54])).
% 0.14/0.38  cnf(c_0_60, negated_conjecture, (esk3_0=k1_xboole_0|esk4_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_57])])).
% 0.14/0.38  cnf(c_0_61, negated_conjecture, (~v1_xboole_0(esk3_0)), inference(spm,[status(thm)],[c_0_23, c_0_58])).
% 0.14/0.38  cnf(c_0_62, negated_conjecture, (esk3_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_57])])).
% 0.14/0.38  cnf(c_0_63, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_62]), c_0_57])]), ['proof']).
% 0.14/0.38  # SZS output end CNFRefutation
% 0.14/0.38  # Proof object total steps             : 64
% 0.14/0.38  # Proof object clause steps            : 50
% 0.14/0.38  # Proof object formula steps           : 14
% 0.14/0.38  # Proof object conjectures             : 40
% 0.14/0.38  # Proof object clause conjectures      : 37
% 0.14/0.38  # Proof object formula conjectures     : 3
% 0.14/0.38  # Proof object initial clauses used    : 16
% 0.14/0.38  # Proof object initial formulas used   : 7
% 0.14/0.38  # Proof object generating inferences   : 28
% 0.14/0.38  # Proof object simplifying inferences  : 15
% 0.14/0.38  # Training examples: 0 positive, 0 negative
% 0.14/0.38  # Parsed axioms                        : 12
% 0.14/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.38  # Initial clauses                      : 25
% 0.14/0.38  # Removed in clause preprocessing      : 1
% 0.14/0.38  # Initial clauses in saturation        : 24
% 0.14/0.38  # Processed clauses                    : 194
% 0.14/0.38  # ...of these trivial                  : 1
% 0.14/0.38  # ...subsumed                          : 31
% 0.14/0.38  # ...remaining for further processing  : 162
% 0.14/0.38  # Other redundant clauses eliminated   : 2
% 0.14/0.38  # Clauses deleted for lack of memory   : 0
% 0.14/0.38  # Backward-subsumed                    : 12
% 0.14/0.38  # Backward-rewritten                   : 19
% 0.14/0.38  # Generated clauses                    : 344
% 0.14/0.38  # ...of the previous two non-trivial   : 323
% 0.14/0.38  # Contextual simplify-reflections      : 1
% 0.14/0.38  # Paramodulations                      : 342
% 0.14/0.38  # Factorizations                       : 0
% 0.14/0.38  # Equation resolutions                 : 2
% 0.14/0.38  # Propositional unsat checks           : 0
% 0.14/0.38  #    Propositional check models        : 0
% 0.14/0.38  #    Propositional check unsatisfiable : 0
% 0.14/0.38  #    Propositional clauses             : 0
% 0.14/0.38  #    Propositional clauses after purity: 0
% 0.14/0.38  #    Propositional unsat core size     : 0
% 0.14/0.38  #    Propositional preprocessing time  : 0.000
% 0.14/0.38  #    Propositional encoding time       : 0.000
% 0.14/0.38  #    Propositional solver time         : 0.000
% 0.14/0.38  #    Success case prop preproc time    : 0.000
% 0.14/0.38  #    Success case prop encoding time   : 0.000
% 0.14/0.38  #    Success case prop solver time     : 0.000
% 0.14/0.38  # Current number of processed clauses  : 106
% 0.14/0.38  #    Positive orientable unit clauses  : 51
% 0.14/0.38  #    Positive unorientable unit clauses: 0
% 0.14/0.38  #    Negative unit clauses             : 8
% 0.14/0.38  #    Non-unit-clauses                  : 47
% 0.14/0.38  # Current number of unprocessed clauses: 162
% 0.14/0.38  # ...number of literals in the above   : 366
% 0.14/0.38  # Current number of archived formulas  : 0
% 0.14/0.38  # Current number of archived clauses   : 55
% 0.14/0.38  # Clause-clause subsumption calls (NU) : 257
% 0.14/0.38  # Rec. Clause-clause subsumption calls : 98
% 0.14/0.38  # Non-unit clause-clause subsumptions  : 19
% 0.14/0.38  # Unit Clause-clause subsumption calls : 41
% 0.14/0.38  # Rewrite failures with RHS unbound    : 0
% 0.14/0.38  # BW rewrite match attempts            : 12
% 0.14/0.38  # BW rewrite match successes           : 3
% 0.14/0.38  # Condensation attempts                : 0
% 0.14/0.38  # Condensation successes               : 0
% 0.14/0.38  # Termbank termtop insertions          : 5575
% 0.14/0.38  
% 0.14/0.38  # -------------------------------------------------
% 0.14/0.38  # User time                : 0.036 s
% 0.14/0.38  # System time              : 0.005 s
% 0.14/0.38  # Total time               : 0.042 s
% 0.14/0.38  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
