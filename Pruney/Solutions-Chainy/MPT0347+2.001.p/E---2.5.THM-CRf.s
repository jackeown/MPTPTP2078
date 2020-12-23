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
% DateTime   : Thu Dec  3 10:45:11 EST 2020

% Result     : Theorem 26.48s
% Output     : CNFRefutation 26.48s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 582 expanded)
%              Number of clauses        :   70 ( 285 expanded)
%              Number of leaves         :    9 ( 140 expanded)
%              Depth                    :   20
%              Number of atoms          :  284 (2582 expanded)
%              Number of equality atoms :   60 ( 513 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t17_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ! [X4] :
              ( m1_subset_1(X4,k1_zfmisc_1(X1))
             => ( ! [X5] :
                    ( m1_subset_1(X5,X1)
                   => ( r2_hidden(X5,X2)
                    <=> ( r2_hidden(X5,X3)
                        & ~ r2_hidden(X5,X4) ) ) )
               => X2 = k7_subset_1(X1,X3,X4) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_subset_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

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

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(X1))
           => ! [X4] :
                ( m1_subset_1(X4,k1_zfmisc_1(X1))
               => ( ! [X5] :
                      ( m1_subset_1(X5,X1)
                     => ( r2_hidden(X5,X2)
                      <=> ( r2_hidden(X5,X3)
                          & ~ r2_hidden(X5,X4) ) ) )
                 => X2 = k7_subset_1(X1,X3,X4) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t17_subset_1])).

fof(c_0_10,plain,(
    ! [X34,X35] :
      ( ( ~ m1_subset_1(X35,X34)
        | r2_hidden(X35,X34)
        | v1_xboole_0(X34) )
      & ( ~ r2_hidden(X35,X34)
        | m1_subset_1(X35,X34)
        | v1_xboole_0(X34) )
      & ( ~ m1_subset_1(X35,X34)
        | v1_xboole_0(X35)
        | ~ v1_xboole_0(X34) )
      & ( ~ v1_xboole_0(X35)
        | m1_subset_1(X35,X34)
        | ~ v1_xboole_0(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_11,negated_conjecture,(
    ! [X44] :
      ( m1_subset_1(esk6_0,k1_zfmisc_1(esk5_0))
      & m1_subset_1(esk7_0,k1_zfmisc_1(esk5_0))
      & m1_subset_1(esk8_0,k1_zfmisc_1(esk5_0))
      & ( r2_hidden(X44,esk7_0)
        | ~ r2_hidden(X44,esk6_0)
        | ~ m1_subset_1(X44,esk5_0) )
      & ( ~ r2_hidden(X44,esk8_0)
        | ~ r2_hidden(X44,esk6_0)
        | ~ m1_subset_1(X44,esk5_0) )
      & ( ~ r2_hidden(X44,esk7_0)
        | r2_hidden(X44,esk8_0)
        | r2_hidden(X44,esk6_0)
        | ~ m1_subset_1(X44,esk5_0) )
      & esk6_0 != k7_subset_1(esk5_0,esk7_0,esk8_0) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])])])).

fof(c_0_12,plain,(
    ! [X36] : ~ v1_xboole_0(k1_zfmisc_1(X36)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

fof(c_0_13,plain,(
    ! [X27,X28,X29,X30,X31,X32] :
      ( ( ~ r2_hidden(X29,X28)
        | r1_tarski(X29,X27)
        | X28 != k1_zfmisc_1(X27) )
      & ( ~ r1_tarski(X30,X27)
        | r2_hidden(X30,X28)
        | X28 != k1_zfmisc_1(X27) )
      & ( ~ r2_hidden(esk4_2(X31,X32),X32)
        | ~ r1_tarski(esk4_2(X31,X32),X31)
        | X32 = k1_zfmisc_1(X31) )
      & ( r2_hidden(esk4_2(X31,X32),X32)
        | r1_tarski(esk4_2(X31,X32),X31)
        | X32 = k1_zfmisc_1(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

cnf(c_0_14,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_17,plain,(
    ! [X10,X11,X12,X13,X14] :
      ( ( ~ r1_tarski(X10,X11)
        | ~ r2_hidden(X12,X10)
        | r2_hidden(X12,X11) )
      & ( r2_hidden(esk2_2(X13,X14),X13)
        | r1_tarski(X13,X14) )
      & ( ~ r2_hidden(esk2_2(X13,X14),X14)
        | r1_tarski(X13,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_18,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(esk6_0,k1_zfmisc_1(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16])).

cnf(c_0_20,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( r1_tarski(esk6_0,X1)
    | k1_zfmisc_1(esk5_0) != k1_zfmisc_1(X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(X1,X2)
    | k1_zfmisc_1(esk5_0) != k1_zfmisc_1(X2)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_23,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_24,plain,(
    ! [X6,X7,X8] :
      ( ( ~ v1_xboole_0(X6)
        | ~ r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_1(X8),X8)
        | v1_xboole_0(X8) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_25,plain,(
    ! [X16,X17,X18,X19,X20,X21,X22,X23] :
      ( ( r2_hidden(X19,X16)
        | ~ r2_hidden(X19,X18)
        | X18 != k4_xboole_0(X16,X17) )
      & ( ~ r2_hidden(X19,X17)
        | ~ r2_hidden(X19,X18)
        | X18 != k4_xboole_0(X16,X17) )
      & ( ~ r2_hidden(X20,X16)
        | r2_hidden(X20,X17)
        | r2_hidden(X20,X18)
        | X18 != k4_xboole_0(X16,X17) )
      & ( ~ r2_hidden(esk3_3(X21,X22,X23),X23)
        | ~ r2_hidden(esk3_3(X21,X22,X23),X21)
        | r2_hidden(esk3_3(X21,X22,X23),X22)
        | X23 = k4_xboole_0(X21,X22) )
      & ( r2_hidden(esk3_3(X21,X22,X23),X21)
        | r2_hidden(esk3_3(X21,X22,X23),X23)
        | X23 = k4_xboole_0(X21,X22) )
      & ( ~ r2_hidden(esk3_3(X21,X22,X23),X22)
        | r2_hidden(esk3_3(X21,X22,X23),X23)
        | X23 = k4_xboole_0(X21,X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_26,plain,(
    ! [X25,X26] : k4_xboole_0(X25,X26) = k5_xboole_0(X25,k3_xboole_0(X25,X26)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_27,negated_conjecture,
    ( r1_tarski(esk6_0,X1)
    | r2_hidden(esk2_2(esk6_0,X1),X2)
    | k1_zfmisc_1(esk5_0) != k1_zfmisc_1(X2) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_28,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_29,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),X1)
    | r2_hidden(esk3_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk2_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(esk6_0,X1)
    | r2_hidden(esk2_2(esk6_0,X1),esk5_0) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(X1,esk7_0)
    | ~ r2_hidden(X1,esk6_0)
    | ~ m1_subset_1(X1,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_35,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_36,negated_conjecture,
    ( ~ r2_hidden(X1,esk8_0)
    | ~ r2_hidden(X1,esk6_0)
    | ~ m1_subset_1(X1,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_37,plain,
    ( X3 = k5_xboole_0(X1,k3_xboole_0(X1,X2))
    | r2_hidden(esk3_3(X1,X2,X3),X3)
    | r2_hidden(esk3_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( r1_tarski(esk6_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_39,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),X2)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk3_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk3_3(X1,X2,X3),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(X1,esk7_0)
    | ~ r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_42,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_43,negated_conjecture,
    ( ~ r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X1,esk8_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_35])).

cnf(c_0_44,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = X1
    | r2_hidden(esk3_3(X1,X2,X1),X1) ),
    inference(ef,[status(thm)],[c_0_37])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_38])).

cnf(c_0_46,plain,
    ( X3 = k5_xboole_0(X1,k3_xboole_0(X1,X2))
    | r2_hidden(esk3_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk3_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk3_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_39,c_0_31])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk7_0,k1_zfmisc_1(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_40]),c_0_16])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X4 != k4_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(X1,esk7_0)
    | ~ r2_hidden(esk2_2(X1,esk7_0),esk6_0)
    | ~ r2_hidden(esk2_2(X1,esk7_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_41])).

cnf(c_0_50,plain,
    ( X3 != k5_xboole_0(X4,k3_xboole_0(X4,X2))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_42,c_0_31])).

cnf(c_0_51,negated_conjecture,
    ( k5_xboole_0(esk8_0,k3_xboole_0(esk8_0,X1)) = esk8_0
    | ~ r2_hidden(esk3_3(esk8_0,X1,esk8_0),esk6_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45])).

cnf(c_0_52,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = X1
    | r2_hidden(esk3_3(X1,X2,X1),X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_44]),c_0_44])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(esk7_0,X1)
    | k1_zfmisc_1(esk5_0) != k1_zfmisc_1(X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_47])).

cnf(c_0_54,plain,
    ( r2_hidden(X1,X4)
    | r2_hidden(X1,X3)
    | X4 != k5_xboole_0(X2,k3_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_48,c_0_31])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(esk6_0,esk7_0)
    | ~ r2_hidden(esk2_2(esk6_0,esk7_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_23])).

cnf(c_0_56,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_50])).

cnf(c_0_57,negated_conjecture,
    ( k5_xboole_0(esk8_0,k3_xboole_0(esk8_0,esk6_0)) = esk8_0 ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_58,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk3_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(X1,esk8_0)
    | r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X1,esk7_0)
    | ~ m1_subset_1(X1,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(X1,X2)
    | k1_zfmisc_1(esk5_0) != k1_zfmisc_1(X2)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_53])).

fof(c_0_61,plain,(
    ! [X37,X38,X39] :
      ( ~ m1_subset_1(X38,k1_zfmisc_1(X37))
      | k7_subset_1(X37,X38,X39) = k4_xboole_0(X38,X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

cnf(c_0_62,plain,
    ( r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_54])).

cnf(c_0_63,negated_conjecture,
    ( r1_tarski(esk6_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_33])).

cnf(c_0_64,negated_conjecture,
    ( ~ r2_hidden(X1,esk8_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_65,plain,
    ( X3 = k5_xboole_0(X1,k3_xboole_0(X1,X2))
    | r2_hidden(esk3_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk3_3(X1,X2,X3),X2) ),
    inference(rw,[status(thm)],[c_0_58,c_0_31])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(X1,esk8_0)
    | r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X1,esk7_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_35])).

cnf(c_0_67,negated_conjecture,
    ( X1 = k5_xboole_0(esk7_0,k3_xboole_0(esk7_0,X2))
    | r2_hidden(esk3_3(esk7_0,X2,X1),X1)
    | r2_hidden(esk3_3(esk7_0,X2,X1),X3)
    | k1_zfmisc_1(esk5_0) != k1_zfmisc_1(X3) ),
    inference(spm,[status(thm)],[c_0_60,c_0_37])).

cnf(c_0_68,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_69,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k5_xboole_0(X3,k3_xboole_0(X3,X4))
    | r2_hidden(esk3_3(X3,X4,k5_xboole_0(X1,k3_xboole_0(X1,X2))),X2)
    | r2_hidden(esk3_3(X3,X4,k5_xboole_0(X1,k3_xboole_0(X1,X2))),X4)
    | ~ r2_hidden(esk3_3(X3,X4,k5_xboole_0(X1,k3_xboole_0(X1,X2))),X3)
    | ~ r2_hidden(esk3_3(X3,X4,k5_xboole_0(X1,k3_xboole_0(X1,X2))),X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_62])).

cnf(c_0_70,negated_conjecture,
    ( r2_hidden(X1,esk7_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_63])).

cnf(c_0_71,negated_conjecture,
    ( k5_xboole_0(X1,k3_xboole_0(X1,esk8_0)) = X1
    | ~ r2_hidden(esk3_3(X1,esk8_0,X1),esk6_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_52])).

cnf(c_0_72,negated_conjecture,
    ( X1 = k5_xboole_0(X2,k3_xboole_0(X2,esk8_0))
    | r2_hidden(esk3_3(X2,esk8_0,X1),esk6_0)
    | r2_hidden(esk3_3(X2,esk8_0,X1),X1)
    | ~ r2_hidden(esk3_3(X2,esk8_0,X1),esk7_0)
    | ~ r2_hidden(esk3_3(X2,esk8_0,X1),esk5_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_73,negated_conjecture,
    ( X1 = k5_xboole_0(esk7_0,k3_xboole_0(esk7_0,X2))
    | r2_hidden(esk3_3(esk7_0,X2,X1),esk5_0)
    | r2_hidden(esk3_3(esk7_0,X2,X1),X1) ),
    inference(er,[status(thm)],[c_0_67])).

cnf(c_0_74,plain,
    ( k7_subset_1(X2,X1,X3) = k5_xboole_0(X1,k3_xboole_0(X1,X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_68,c_0_31])).

cnf(c_0_75,negated_conjecture,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k5_xboole_0(esk7_0,k3_xboole_0(esk7_0,X3))
    | r2_hidden(esk3_3(esk7_0,X3,k5_xboole_0(X1,k3_xboole_0(X1,X2))),X3)
    | r2_hidden(esk3_3(esk7_0,X3,k5_xboole_0(X1,k3_xboole_0(X1,X2))),X2)
    | ~ r2_hidden(esk3_3(esk7_0,X3,k5_xboole_0(X1,k3_xboole_0(X1,X2))),esk6_0)
    | ~ r2_hidden(esk3_3(esk7_0,X3,k5_xboole_0(X1,k3_xboole_0(X1,X2))),X1) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_76,negated_conjecture,
    ( k5_xboole_0(esk6_0,k3_xboole_0(esk6_0,esk8_0)) = esk6_0 ),
    inference(spm,[status(thm)],[c_0_71,c_0_44])).

cnf(c_0_77,negated_conjecture,
    ( X1 = k5_xboole_0(esk7_0,k3_xboole_0(esk7_0,esk8_0))
    | r2_hidden(esk3_3(esk7_0,esk8_0,X1),esk6_0)
    | r2_hidden(esk3_3(esk7_0,esk8_0,X1),X1)
    | ~ r2_hidden(esk3_3(esk7_0,esk8_0,X1),esk5_0) ),
    inference(spm,[status(thm)],[c_0_72,c_0_37])).

cnf(c_0_78,negated_conjecture,
    ( k5_xboole_0(esk7_0,k3_xboole_0(esk7_0,X1)) = esk6_0
    | r2_hidden(esk3_3(esk7_0,X1,esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_73])).

cnf(c_0_79,negated_conjecture,
    ( esk6_0 != k7_subset_1(esk5_0,esk7_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_80,plain,
    ( k7_subset_1(X1,X2,X3) = k7_subset_1(X4,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_74])).

cnf(c_0_81,negated_conjecture,
    ( k5_xboole_0(esk7_0,k3_xboole_0(esk7_0,X1)) = esk6_0
    | r2_hidden(esk3_3(esk7_0,X1,esk6_0),X1)
    | ~ r2_hidden(esk3_3(esk7_0,X1,esk6_0),esk6_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_64])).

cnf(c_0_82,negated_conjecture,
    ( k5_xboole_0(esk7_0,k3_xboole_0(esk7_0,esk8_0)) = esk6_0
    | r2_hidden(esk3_3(esk7_0,esk8_0,esk6_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_83,negated_conjecture,
    ( k7_subset_1(X1,esk7_0,esk8_0) != esk6_0
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_40])])).

cnf(c_0_84,negated_conjecture,
    ( k5_xboole_0(esk7_0,k3_xboole_0(esk7_0,esk8_0)) = esk6_0
    | r2_hidden(esk3_3(esk7_0,esk8_0,esk6_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_85,negated_conjecture,
    ( k5_xboole_0(esk7_0,k3_xboole_0(esk7_0,esk8_0)) != esk6_0
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_83,c_0_74])).

cnf(c_0_86,negated_conjecture,
    ( k5_xboole_0(esk7_0,k3_xboole_0(esk7_0,esk8_0)) = esk6_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_84]),c_0_82])).

cnf(c_0_87,negated_conjecture,
    ( ~ m1_subset_1(esk7_0,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_85,c_0_86])])).

cnf(c_0_88,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_40,c_0_87]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:01:15 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  # Version: 2.5pre002
% 0.13/0.36  # No SInE strategy applied
% 0.13/0.36  # Trying AutoSched0 for 299 seconds
% 26.48/26.68  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 26.48/26.68  # and selection function SelectMaxLComplexAvoidPosPred.
% 26.48/26.68  #
% 26.48/26.68  # Preprocessing time       : 0.028 s
% 26.48/26.68  # Presaturation interreduction done
% 26.48/26.68  
% 26.48/26.68  # Proof found!
% 26.48/26.68  # SZS status Theorem
% 26.48/26.68  # SZS output start CNFRefutation
% 26.48/26.68  fof(t17_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(X1))=>(![X5]:(m1_subset_1(X5,X1)=>(r2_hidden(X5,X2)<=>(r2_hidden(X5,X3)&~(r2_hidden(X5,X4)))))=>X2=k7_subset_1(X1,X3,X4))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_subset_1)).
% 26.48/26.68  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 26.48/26.68  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 26.48/26.68  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 26.48/26.68  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 26.48/26.68  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 26.48/26.68  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 26.48/26.68  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 26.48/26.68  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 26.48/26.68  fof(c_0_9, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(X1))=>(![X5]:(m1_subset_1(X5,X1)=>(r2_hidden(X5,X2)<=>(r2_hidden(X5,X3)&~(r2_hidden(X5,X4)))))=>X2=k7_subset_1(X1,X3,X4)))))), inference(assume_negation,[status(cth)],[t17_subset_1])).
% 26.48/26.68  fof(c_0_10, plain, ![X34, X35]:(((~m1_subset_1(X35,X34)|r2_hidden(X35,X34)|v1_xboole_0(X34))&(~r2_hidden(X35,X34)|m1_subset_1(X35,X34)|v1_xboole_0(X34)))&((~m1_subset_1(X35,X34)|v1_xboole_0(X35)|~v1_xboole_0(X34))&(~v1_xboole_0(X35)|m1_subset_1(X35,X34)|~v1_xboole_0(X34)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 26.48/26.68  fof(c_0_11, negated_conjecture, ![X44]:(m1_subset_1(esk6_0,k1_zfmisc_1(esk5_0))&(m1_subset_1(esk7_0,k1_zfmisc_1(esk5_0))&(m1_subset_1(esk8_0,k1_zfmisc_1(esk5_0))&((((r2_hidden(X44,esk7_0)|~r2_hidden(X44,esk6_0)|~m1_subset_1(X44,esk5_0))&(~r2_hidden(X44,esk8_0)|~r2_hidden(X44,esk6_0)|~m1_subset_1(X44,esk5_0)))&(~r2_hidden(X44,esk7_0)|r2_hidden(X44,esk8_0)|r2_hidden(X44,esk6_0)|~m1_subset_1(X44,esk5_0)))&esk6_0!=k7_subset_1(esk5_0,esk7_0,esk8_0))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])])])).
% 26.48/26.68  fof(c_0_12, plain, ![X36]:~v1_xboole_0(k1_zfmisc_1(X36)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 26.48/26.68  fof(c_0_13, plain, ![X27, X28, X29, X30, X31, X32]:(((~r2_hidden(X29,X28)|r1_tarski(X29,X27)|X28!=k1_zfmisc_1(X27))&(~r1_tarski(X30,X27)|r2_hidden(X30,X28)|X28!=k1_zfmisc_1(X27)))&((~r2_hidden(esk4_2(X31,X32),X32)|~r1_tarski(esk4_2(X31,X32),X31)|X32=k1_zfmisc_1(X31))&(r2_hidden(esk4_2(X31,X32),X32)|r1_tarski(esk4_2(X31,X32),X31)|X32=k1_zfmisc_1(X31)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 26.48/26.68  cnf(c_0_14, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 26.48/26.68  cnf(c_0_15, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 26.48/26.68  cnf(c_0_16, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 26.48/26.68  fof(c_0_17, plain, ![X10, X11, X12, X13, X14]:((~r1_tarski(X10,X11)|(~r2_hidden(X12,X10)|r2_hidden(X12,X11)))&((r2_hidden(esk2_2(X13,X14),X13)|r1_tarski(X13,X14))&(~r2_hidden(esk2_2(X13,X14),X14)|r1_tarski(X13,X14)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 26.48/26.68  cnf(c_0_18, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 26.48/26.68  cnf(c_0_19, negated_conjecture, (r2_hidden(esk6_0,k1_zfmisc_1(esk5_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16])).
% 26.48/26.68  cnf(c_0_20, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 26.48/26.68  cnf(c_0_21, negated_conjecture, (r1_tarski(esk6_0,X1)|k1_zfmisc_1(esk5_0)!=k1_zfmisc_1(X1)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 26.48/26.68  cnf(c_0_22, negated_conjecture, (r2_hidden(X1,X2)|k1_zfmisc_1(esk5_0)!=k1_zfmisc_1(X2)|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 26.48/26.68  cnf(c_0_23, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 26.48/26.68  fof(c_0_24, plain, ![X6, X7, X8]:((~v1_xboole_0(X6)|~r2_hidden(X7,X6))&(r2_hidden(esk1_1(X8),X8)|v1_xboole_0(X8))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 26.48/26.68  fof(c_0_25, plain, ![X16, X17, X18, X19, X20, X21, X22, X23]:((((r2_hidden(X19,X16)|~r2_hidden(X19,X18)|X18!=k4_xboole_0(X16,X17))&(~r2_hidden(X19,X17)|~r2_hidden(X19,X18)|X18!=k4_xboole_0(X16,X17)))&(~r2_hidden(X20,X16)|r2_hidden(X20,X17)|r2_hidden(X20,X18)|X18!=k4_xboole_0(X16,X17)))&((~r2_hidden(esk3_3(X21,X22,X23),X23)|(~r2_hidden(esk3_3(X21,X22,X23),X21)|r2_hidden(esk3_3(X21,X22,X23),X22))|X23=k4_xboole_0(X21,X22))&((r2_hidden(esk3_3(X21,X22,X23),X21)|r2_hidden(esk3_3(X21,X22,X23),X23)|X23=k4_xboole_0(X21,X22))&(~r2_hidden(esk3_3(X21,X22,X23),X22)|r2_hidden(esk3_3(X21,X22,X23),X23)|X23=k4_xboole_0(X21,X22))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 26.48/26.68  fof(c_0_26, plain, ![X25, X26]:k4_xboole_0(X25,X26)=k5_xboole_0(X25,k3_xboole_0(X25,X26)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 26.48/26.68  cnf(c_0_27, negated_conjecture, (r1_tarski(esk6_0,X1)|r2_hidden(esk2_2(esk6_0,X1),X2)|k1_zfmisc_1(esk5_0)!=k1_zfmisc_1(X2)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 26.48/26.68  cnf(c_0_28, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 26.48/26.68  cnf(c_0_29, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 26.48/26.68  cnf(c_0_30, plain, (r2_hidden(esk3_3(X1,X2,X3),X1)|r2_hidden(esk3_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 26.48/26.68  cnf(c_0_31, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 26.48/26.68  cnf(c_0_32, plain, (r1_tarski(X1,X2)|~r2_hidden(esk2_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 26.48/26.68  cnf(c_0_33, negated_conjecture, (r1_tarski(esk6_0,X1)|r2_hidden(esk2_2(esk6_0,X1),esk5_0)), inference(er,[status(thm)],[c_0_27])).
% 26.48/26.68  cnf(c_0_34, negated_conjecture, (r2_hidden(X1,esk7_0)|~r2_hidden(X1,esk6_0)|~m1_subset_1(X1,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 26.48/26.68  cnf(c_0_35, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(csr,[status(thm)],[c_0_28, c_0_29])).
% 26.48/26.68  cnf(c_0_36, negated_conjecture, (~r2_hidden(X1,esk8_0)|~r2_hidden(X1,esk6_0)|~m1_subset_1(X1,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 26.48/26.68  cnf(c_0_37, plain, (X3=k5_xboole_0(X1,k3_xboole_0(X1,X2))|r2_hidden(esk3_3(X1,X2,X3),X3)|r2_hidden(esk3_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_30, c_0_31])).
% 26.48/26.68  cnf(c_0_38, negated_conjecture, (r1_tarski(esk6_0,esk5_0)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 26.48/26.68  cnf(c_0_39, plain, (r2_hidden(esk3_3(X1,X2,X3),X2)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk3_3(X1,X2,X3),X3)|~r2_hidden(esk3_3(X1,X2,X3),X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 26.48/26.68  cnf(c_0_40, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 26.48/26.68  cnf(c_0_41, negated_conjecture, (r2_hidden(X1,esk7_0)|~r2_hidden(X1,esk6_0)|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 26.48/26.68  cnf(c_0_42, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 26.48/26.68  cnf(c_0_43, negated_conjecture, (~r2_hidden(X1,esk6_0)|~r2_hidden(X1,esk8_0)|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_36, c_0_35])).
% 26.48/26.68  cnf(c_0_44, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=X1|r2_hidden(esk3_3(X1,X2,X1),X1)), inference(ef,[status(thm)],[c_0_37])).
% 26.48/26.68  cnf(c_0_45, negated_conjecture, (r2_hidden(X1,esk5_0)|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_20, c_0_38])).
% 26.48/26.68  cnf(c_0_46, plain, (X3=k5_xboole_0(X1,k3_xboole_0(X1,X2))|r2_hidden(esk3_3(X1,X2,X3),X2)|~r2_hidden(esk3_3(X1,X2,X3),X3)|~r2_hidden(esk3_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_39, c_0_31])).
% 26.48/26.68  cnf(c_0_47, negated_conjecture, (r2_hidden(esk7_0,k1_zfmisc_1(esk5_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_40]), c_0_16])).
% 26.48/26.68  cnf(c_0_48, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X4!=k4_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 26.48/26.68  cnf(c_0_49, negated_conjecture, (r1_tarski(X1,esk7_0)|~r2_hidden(esk2_2(X1,esk7_0),esk6_0)|~r2_hidden(esk2_2(X1,esk7_0),esk5_0)), inference(spm,[status(thm)],[c_0_32, c_0_41])).
% 26.48/26.68  cnf(c_0_50, plain, (X3!=k5_xboole_0(X4,k3_xboole_0(X4,X2))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_42, c_0_31])).
% 26.48/26.68  cnf(c_0_51, negated_conjecture, (k5_xboole_0(esk8_0,k3_xboole_0(esk8_0,X1))=esk8_0|~r2_hidden(esk3_3(esk8_0,X1,esk8_0),esk6_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45])).
% 26.48/26.68  cnf(c_0_52, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=X1|r2_hidden(esk3_3(X1,X2,X1),X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_44]), c_0_44])).
% 26.48/26.68  cnf(c_0_53, negated_conjecture, (r1_tarski(esk7_0,X1)|k1_zfmisc_1(esk5_0)!=k1_zfmisc_1(X1)), inference(spm,[status(thm)],[c_0_18, c_0_47])).
% 26.48/26.68  cnf(c_0_54, plain, (r2_hidden(X1,X4)|r2_hidden(X1,X3)|X4!=k5_xboole_0(X2,k3_xboole_0(X2,X3))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_48, c_0_31])).
% 26.48/26.68  cnf(c_0_55, negated_conjecture, (r1_tarski(esk6_0,esk7_0)|~r2_hidden(esk2_2(esk6_0,esk7_0),esk5_0)), inference(spm,[status(thm)],[c_0_49, c_0_23])).
% 26.48/26.68  cnf(c_0_56, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_50])).
% 26.48/26.68  cnf(c_0_57, negated_conjecture, (k5_xboole_0(esk8_0,k3_xboole_0(esk8_0,esk6_0))=esk8_0), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 26.48/26.68  cnf(c_0_58, plain, (r2_hidden(esk3_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk3_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 26.48/26.68  cnf(c_0_59, negated_conjecture, (r2_hidden(X1,esk8_0)|r2_hidden(X1,esk6_0)|~r2_hidden(X1,esk7_0)|~m1_subset_1(X1,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 26.48/26.68  cnf(c_0_60, negated_conjecture, (r2_hidden(X1,X2)|k1_zfmisc_1(esk5_0)!=k1_zfmisc_1(X2)|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_20, c_0_53])).
% 26.48/26.68  fof(c_0_61, plain, ![X37, X38, X39]:(~m1_subset_1(X38,k1_zfmisc_1(X37))|k7_subset_1(X37,X38,X39)=k4_xboole_0(X38,X39)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 26.48/26.68  cnf(c_0_62, plain, (r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))|r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_54])).
% 26.48/26.68  cnf(c_0_63, negated_conjecture, (r1_tarski(esk6_0,esk7_0)), inference(spm,[status(thm)],[c_0_55, c_0_33])).
% 26.48/26.68  cnf(c_0_64, negated_conjecture, (~r2_hidden(X1,esk8_0)|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 26.48/26.68  cnf(c_0_65, plain, (X3=k5_xboole_0(X1,k3_xboole_0(X1,X2))|r2_hidden(esk3_3(X1,X2,X3),X3)|~r2_hidden(esk3_3(X1,X2,X3),X2)), inference(rw,[status(thm)],[c_0_58, c_0_31])).
% 26.48/26.68  cnf(c_0_66, negated_conjecture, (r2_hidden(X1,esk8_0)|r2_hidden(X1,esk6_0)|~r2_hidden(X1,esk7_0)|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_59, c_0_35])).
% 26.48/26.68  cnf(c_0_67, negated_conjecture, (X1=k5_xboole_0(esk7_0,k3_xboole_0(esk7_0,X2))|r2_hidden(esk3_3(esk7_0,X2,X1),X1)|r2_hidden(esk3_3(esk7_0,X2,X1),X3)|k1_zfmisc_1(esk5_0)!=k1_zfmisc_1(X3)), inference(spm,[status(thm)],[c_0_60, c_0_37])).
% 26.48/26.68  cnf(c_0_68, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_61])).
% 26.48/26.68  cnf(c_0_69, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=k5_xboole_0(X3,k3_xboole_0(X3,X4))|r2_hidden(esk3_3(X3,X4,k5_xboole_0(X1,k3_xboole_0(X1,X2))),X2)|r2_hidden(esk3_3(X3,X4,k5_xboole_0(X1,k3_xboole_0(X1,X2))),X4)|~r2_hidden(esk3_3(X3,X4,k5_xboole_0(X1,k3_xboole_0(X1,X2))),X3)|~r2_hidden(esk3_3(X3,X4,k5_xboole_0(X1,k3_xboole_0(X1,X2))),X1)), inference(spm,[status(thm)],[c_0_46, c_0_62])).
% 26.48/26.68  cnf(c_0_70, negated_conjecture, (r2_hidden(X1,esk7_0)|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_20, c_0_63])).
% 26.48/26.68  cnf(c_0_71, negated_conjecture, (k5_xboole_0(X1,k3_xboole_0(X1,esk8_0))=X1|~r2_hidden(esk3_3(X1,esk8_0,X1),esk6_0)), inference(spm,[status(thm)],[c_0_64, c_0_52])).
% 26.48/26.68  cnf(c_0_72, negated_conjecture, (X1=k5_xboole_0(X2,k3_xboole_0(X2,esk8_0))|r2_hidden(esk3_3(X2,esk8_0,X1),esk6_0)|r2_hidden(esk3_3(X2,esk8_0,X1),X1)|~r2_hidden(esk3_3(X2,esk8_0,X1),esk7_0)|~r2_hidden(esk3_3(X2,esk8_0,X1),esk5_0)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 26.48/26.68  cnf(c_0_73, negated_conjecture, (X1=k5_xboole_0(esk7_0,k3_xboole_0(esk7_0,X2))|r2_hidden(esk3_3(esk7_0,X2,X1),esk5_0)|r2_hidden(esk3_3(esk7_0,X2,X1),X1)), inference(er,[status(thm)],[c_0_67])).
% 26.48/26.68  cnf(c_0_74, plain, (k7_subset_1(X2,X1,X3)=k5_xboole_0(X1,k3_xboole_0(X1,X3))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_68, c_0_31])).
% 26.48/26.68  cnf(c_0_75, negated_conjecture, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=k5_xboole_0(esk7_0,k3_xboole_0(esk7_0,X3))|r2_hidden(esk3_3(esk7_0,X3,k5_xboole_0(X1,k3_xboole_0(X1,X2))),X3)|r2_hidden(esk3_3(esk7_0,X3,k5_xboole_0(X1,k3_xboole_0(X1,X2))),X2)|~r2_hidden(esk3_3(esk7_0,X3,k5_xboole_0(X1,k3_xboole_0(X1,X2))),esk6_0)|~r2_hidden(esk3_3(esk7_0,X3,k5_xboole_0(X1,k3_xboole_0(X1,X2))),X1)), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 26.48/26.68  cnf(c_0_76, negated_conjecture, (k5_xboole_0(esk6_0,k3_xboole_0(esk6_0,esk8_0))=esk6_0), inference(spm,[status(thm)],[c_0_71, c_0_44])).
% 26.48/26.68  cnf(c_0_77, negated_conjecture, (X1=k5_xboole_0(esk7_0,k3_xboole_0(esk7_0,esk8_0))|r2_hidden(esk3_3(esk7_0,esk8_0,X1),esk6_0)|r2_hidden(esk3_3(esk7_0,esk8_0,X1),X1)|~r2_hidden(esk3_3(esk7_0,esk8_0,X1),esk5_0)), inference(spm,[status(thm)],[c_0_72, c_0_37])).
% 26.48/26.68  cnf(c_0_78, negated_conjecture, (k5_xboole_0(esk7_0,k3_xboole_0(esk7_0,X1))=esk6_0|r2_hidden(esk3_3(esk7_0,X1,esk6_0),esk5_0)), inference(spm,[status(thm)],[c_0_45, c_0_73])).
% 26.48/26.68  cnf(c_0_79, negated_conjecture, (esk6_0!=k7_subset_1(esk5_0,esk7_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 26.48/26.68  cnf(c_0_80, plain, (k7_subset_1(X1,X2,X3)=k7_subset_1(X4,X2,X3)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X4))), inference(spm,[status(thm)],[c_0_74, c_0_74])).
% 26.48/26.68  cnf(c_0_81, negated_conjecture, (k5_xboole_0(esk7_0,k3_xboole_0(esk7_0,X1))=esk6_0|r2_hidden(esk3_3(esk7_0,X1,esk6_0),X1)|~r2_hidden(esk3_3(esk7_0,X1,esk6_0),esk6_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_64])).
% 26.48/26.68  cnf(c_0_82, negated_conjecture, (k5_xboole_0(esk7_0,k3_xboole_0(esk7_0,esk8_0))=esk6_0|r2_hidden(esk3_3(esk7_0,esk8_0,esk6_0),esk6_0)), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 26.48/26.68  cnf(c_0_83, negated_conjecture, (k7_subset_1(X1,esk7_0,esk8_0)!=esk6_0|~m1_subset_1(esk7_0,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_40])])).
% 26.48/26.68  cnf(c_0_84, negated_conjecture, (k5_xboole_0(esk7_0,k3_xboole_0(esk7_0,esk8_0))=esk6_0|r2_hidden(esk3_3(esk7_0,esk8_0,esk6_0),esk8_0)), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 26.48/26.68  cnf(c_0_85, negated_conjecture, (k5_xboole_0(esk7_0,k3_xboole_0(esk7_0,esk8_0))!=esk6_0|~m1_subset_1(esk7_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_83, c_0_74])).
% 26.48/26.68  cnf(c_0_86, negated_conjecture, (k5_xboole_0(esk7_0,k3_xboole_0(esk7_0,esk8_0))=esk6_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_84]), c_0_82])).
% 26.48/26.68  cnf(c_0_87, negated_conjecture, (~m1_subset_1(esk7_0,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_85, c_0_86])])).
% 26.48/26.68  cnf(c_0_88, negated_conjecture, ($false), inference(sr,[status(thm)],[c_0_40, c_0_87]), ['proof']).
% 26.48/26.68  # SZS output end CNFRefutation
% 26.48/26.68  # Proof object total steps             : 89
% 26.48/26.68  # Proof object clause steps            : 70
% 26.48/26.68  # Proof object formula steps           : 19
% 26.48/26.68  # Proof object conjectures             : 45
% 26.48/26.68  # Proof object clause conjectures      : 42
% 26.48/26.68  # Proof object formula conjectures     : 3
% 26.48/26.68  # Proof object initial clauses used    : 21
% 26.48/26.68  # Proof object initial formulas used   : 9
% 26.48/26.68  # Proof object generating inferences   : 40
% 26.48/26.68  # Proof object simplifying inferences  : 18
% 26.48/26.68  # Training examples: 0 positive, 0 negative
% 26.48/26.68  # Parsed axioms                        : 9
% 26.48/26.68  # Removed by relevancy pruning/SinE    : 0
% 26.48/26.68  # Initial clauses                      : 29
% 26.48/26.68  # Removed in clause preprocessing      : 1
% 26.48/26.68  # Initial clauses in saturation        : 28
% 26.48/26.68  # Processed clauses                    : 190927
% 26.48/26.68  # ...of these trivial                  : 1033
% 26.48/26.68  # ...subsumed                          : 172291
% 26.48/26.68  # ...remaining for further processing  : 17603
% 26.48/26.68  # Other redundant clauses eliminated   : 167
% 26.48/26.68  # Clauses deleted for lack of memory   : 0
% 26.48/26.68  # Backward-subsumed                    : 2912
% 26.48/26.68  # Backward-rewritten                   : 641
% 26.48/26.68  # Generated clauses                    : 1479320
% 26.48/26.68  # ...of the previous two non-trivial   : 1456695
% 26.48/26.68  # Contextual simplify-reflections      : 737
% 26.48/26.68  # Paramodulations                      : 1475731
% 26.48/26.68  # Factorizations                       : 852
% 26.48/26.68  # Equation resolutions                 : 2729
% 26.48/26.68  # Propositional unsat checks           : 0
% 26.48/26.68  #    Propositional check models        : 0
% 26.48/26.68  #    Propositional check unsatisfiable : 0
% 26.48/26.68  #    Propositional clauses             : 0
% 26.48/26.68  #    Propositional clauses after purity: 0
% 26.48/26.68  #    Propositional unsat core size     : 0
% 26.48/26.68  #    Propositional preprocessing time  : 0.000
% 26.48/26.68  #    Propositional encoding time       : 0.000
% 26.48/26.68  #    Propositional solver time         : 0.000
% 26.48/26.68  #    Success case prop preproc time    : 0.000
% 26.48/26.68  #    Success case prop encoding time   : 0.000
% 26.48/26.68  #    Success case prop solver time     : 0.000
% 26.48/26.68  # Current number of processed clauses  : 14014
% 26.48/26.68  #    Positive orientable unit clauses  : 63
% 26.48/26.68  #    Positive unorientable unit clauses: 1
% 26.48/26.68  #    Negative unit clauses             : 30
% 26.48/26.68  #    Non-unit-clauses                  : 13920
% 26.48/26.68  # Current number of unprocessed clauses: 1241822
% 26.48/26.68  # ...number of literals in the above   : 6833440
% 26.48/26.68  # Current number of archived formulas  : 0
% 26.48/26.68  # Current number of archived clauses   : 3590
% 26.48/26.68  # Clause-clause subsumption calls (NU) : 78425423
% 26.48/26.68  # Rec. Clause-clause subsumption calls : 8468326
% 26.48/26.68  # Non-unit clause-clause subsumptions  : 116550
% 26.48/26.68  # Unit Clause-clause subsumption calls : 151448
% 26.48/26.68  # Rewrite failures with RHS unbound    : 296
% 26.48/26.68  # BW rewrite match attempts            : 660
% 26.48/26.68  # BW rewrite match successes           : 28
% 26.48/26.68  # Condensation attempts                : 0
% 26.48/26.68  # Condensation successes               : 0
% 26.48/26.68  # Termbank termtop insertions          : 41183700
% 26.48/26.74  
% 26.48/26.74  # -------------------------------------------------
% 26.48/26.74  # User time                : 25.734 s
% 26.48/26.74  # System time              : 0.614 s
% 26.48/26.74  # Total time               : 26.348 s
% 26.48/26.74  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
