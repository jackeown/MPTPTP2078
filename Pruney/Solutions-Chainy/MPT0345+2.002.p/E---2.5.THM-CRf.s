%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:45:11 EST 2020

% Result     : Theorem 9.73s
% Output     : CNFRefutation 9.73s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 990 expanded)
%              Number of clauses        :   98 ( 472 expanded)
%              Number of leaves         :    9 ( 241 expanded)
%              Depth                    :   19
%              Number of atoms          :  337 (4414 expanded)
%              Number of equality atoms :   61 ( 566 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(t15_subset_1,conjecture,(
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
                        | r2_hidden(X5,X4) ) ) )
               => X2 = k4_subset_1(X1,X3,X4) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_subset_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(c_0_9,plain,(
    ! [X25,X26,X27,X28,X29,X30] :
      ( ( ~ r2_hidden(X27,X26)
        | r1_tarski(X27,X25)
        | X26 != k1_zfmisc_1(X25) )
      & ( ~ r1_tarski(X28,X25)
        | r2_hidden(X28,X26)
        | X26 != k1_zfmisc_1(X25) )
      & ( ~ r2_hidden(esk4_2(X29,X30),X30)
        | ~ r1_tarski(esk4_2(X29,X30),X29)
        | X30 = k1_zfmisc_1(X29) )
      & ( r2_hidden(esk4_2(X29,X30),X30)
        | r1_tarski(esk4_2(X29,X30),X29)
        | X30 = k1_zfmisc_1(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

cnf(c_0_10,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_11,plain,(
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

fof(c_0_12,plain,(
    ! [X36] : ~ v1_xboole_0(k1_zfmisc_1(X36)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

fof(c_0_13,negated_conjecture,(
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
                          | r2_hidden(X5,X4) ) ) )
                 => X2 = k4_subset_1(X1,X3,X4) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t15_subset_1])).

cnf(c_0_14,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_17,negated_conjecture,(
    ! [X44] :
      ( m1_subset_1(esk6_0,k1_zfmisc_1(esk5_0))
      & m1_subset_1(esk7_0,k1_zfmisc_1(esk5_0))
      & m1_subset_1(esk8_0,k1_zfmisc_1(esk5_0))
      & ( ~ r2_hidden(X44,esk6_0)
        | r2_hidden(X44,esk7_0)
        | r2_hidden(X44,esk8_0)
        | ~ m1_subset_1(X44,esk5_0) )
      & ( ~ r2_hidden(X44,esk7_0)
        | r2_hidden(X44,esk6_0)
        | ~ m1_subset_1(X44,esk5_0) )
      & ( ~ r2_hidden(X44,esk8_0)
        | r2_hidden(X44,esk6_0)
        | ~ m1_subset_1(X44,esk5_0) )
      & esk6_0 != k4_subset_1(esk5_0,esk7_0,esk8_0) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])])])).

fof(c_0_18,plain,(
    ! [X10,X11,X12,X13,X14] :
      ( ( ~ r1_tarski(X10,X11)
        | ~ r2_hidden(X12,X10)
        | r2_hidden(X12,X11) )
      & ( r2_hidden(esk2_2(X13,X14),X13)
        | r1_tarski(X13,X14) )
      & ( ~ r2_hidden(esk2_2(X13,X14),X14)
        | r1_tarski(X13,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_19,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_22,plain,(
    ! [X6,X7,X8] :
      ( ( ~ v1_xboole_0(X6)
        | ~ r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_1(X8),X8)
        | v1_xboole_0(X8) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_23,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( r1_tarski(esk7_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( r1_tarski(esk8_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_21])).

cnf(c_0_26,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_27,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_29,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_30,plain,(
    ! [X16,X17,X18,X19,X20,X21,X22,X23] :
      ( ( ~ r2_hidden(X19,X18)
        | r2_hidden(X19,X16)
        | r2_hidden(X19,X17)
        | X18 != k2_xboole_0(X16,X17) )
      & ( ~ r2_hidden(X20,X16)
        | r2_hidden(X20,X18)
        | X18 != k2_xboole_0(X16,X17) )
      & ( ~ r2_hidden(X20,X17)
        | r2_hidden(X20,X18)
        | X18 != k2_xboole_0(X16,X17) )
      & ( ~ r2_hidden(esk3_3(X21,X22,X23),X21)
        | ~ r2_hidden(esk3_3(X21,X22,X23),X23)
        | X23 = k2_xboole_0(X21,X22) )
      & ( ~ r2_hidden(esk3_3(X21,X22,X23),X22)
        | ~ r2_hidden(esk3_3(X21,X22,X23),X23)
        | X23 = k2_xboole_0(X21,X22) )
      & ( r2_hidden(esk3_3(X21,X22,X23),X23)
        | r2_hidden(esk3_3(X21,X22,X23),X21)
        | r2_hidden(esk3_3(X21,X22,X23),X22)
        | X23 = k2_xboole_0(X21,X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

fof(c_0_31,plain,(
    ! [X32,X33] : k3_tarski(k2_tarski(X32,X33)) = k2_xboole_0(X32,X33) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X1,esk8_0)
    | ~ m1_subset_1(X1,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_25])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X1,esk7_0)
    | ~ m1_subset_1(X1,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_35,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(esk7_0,X1)
    | r2_hidden(esk2_2(esk7_0,X1),esk5_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

fof(c_0_37,plain,(
    ! [X37,X38,X39] :
      ( ~ m1_subset_1(X38,k1_zfmisc_1(X37))
      | ~ m1_subset_1(X39,k1_zfmisc_1(X37))
      | k4_subset_1(X37,X38,X39) = k2_xboole_0(X38,X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

cnf(c_0_38,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),X3)
    | r2_hidden(esk3_3(X1,X2,X3),X1)
    | r2_hidden(esk3_3(X1,X2,X3),X2)
    | X3 = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk2_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_41,negated_conjecture,
    ( r1_tarski(esk8_0,X1)
    | r2_hidden(esk2_2(esk8_0,X1),esk6_0)
    | ~ m1_subset_1(esk2_2(esk8_0,X1),esk5_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_29])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(esk8_0,X1)
    | r2_hidden(esk2_2(esk8_0,X1),esk5_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_29])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(esk7_0,X1)
    | r2_hidden(esk2_2(esk7_0,X1),esk6_0)
    | ~ m1_subset_1(esk2_2(esk7_0,X1),esk5_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_29])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(esk2_2(esk7_0,X1),esk5_0)
    | r1_tarski(esk7_0,X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_46,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_47,plain,
    ( X3 = k3_tarski(k2_tarski(X1,X2))
    | r2_hidden(esk3_3(X1,X2,X3),X3)
    | r2_hidden(esk3_3(X1,X2,X3),X2)
    | r2_hidden(esk3_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_48,negated_conjecture,
    ( r1_tarski(esk8_0,esk6_0)
    | ~ m1_subset_1(esk2_2(esk8_0,esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(esk2_2(esk8_0,X1),esk5_0)
    | r1_tarski(esk8_0,X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_42])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(esk7_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_43]),c_0_44])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(esk6_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_45])).

cnf(c_0_52,plain,
    ( k4_subset_1(X2,X1,X3) = k3_tarski(k2_tarski(X1,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_46,c_0_39])).

cnf(c_0_53,plain,
    ( X3 = k2_xboole_0(X1,X2)
    | ~ r2_hidden(esk3_3(X1,X2,X3),X1)
    | ~ r2_hidden(esk3_3(X1,X2,X3),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_54,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_55,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = X1
    | r2_hidden(esk3_3(X1,X2,X1),X1)
    | r2_hidden(esk3_3(X1,X2,X1),X2) ),
    inference(ef,[status(thm)],[c_0_47])).

cnf(c_0_56,negated_conjecture,
    ( r1_tarski(esk8_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_50])).

cnf(c_0_58,plain,
    ( X1 = k3_tarski(k2_tarski(X2,X2))
    | r2_hidden(esk3_3(X2,X2,X1),X1)
    | r2_hidden(esk3_3(X2,X2,X1),X2) ),
    inference(ef,[status(thm)],[c_0_47])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_51])).

cnf(c_0_60,negated_conjecture,
    ( esk6_0 != k4_subset_1(esk5_0,esk7_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_61,plain,
    ( k4_subset_1(X1,X2,X3) = k4_subset_1(X4,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_52])).

cnf(c_0_62,plain,
    ( X3 = k3_tarski(k2_tarski(X1,X2))
    | ~ r2_hidden(esk3_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk3_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_53,c_0_39])).

cnf(c_0_63,plain,
    ( r2_hidden(X1,X3)
    | X3 != k3_tarski(k2_tarski(X4,X2))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_54,c_0_39])).

cnf(c_0_64,plain,
    ( X3 = k2_xboole_0(X1,X2)
    | ~ r2_hidden(esk3_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk3_3(X1,X2,X3),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_65,negated_conjecture,
    ( k3_tarski(k2_tarski(X1,esk8_0)) = X1
    | r2_hidden(esk3_3(X1,esk8_0,X1),esk5_0)
    | r2_hidden(esk3_3(X1,esk8_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_55])).

cnf(c_0_66,plain,
    ( m1_subset_1(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_35,c_0_29])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_56])).

cnf(c_0_68,negated_conjecture,
    ( X1 = k3_tarski(k2_tarski(esk7_0,esk7_0))
    | r2_hidden(esk3_3(esk7_0,esk7_0,X1),esk6_0)
    | r2_hidden(esk3_3(esk7_0,esk7_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_69,negated_conjecture,
    ( r2_hidden(X1,esk7_0)
    | r2_hidden(X1,esk8_0)
    | ~ r2_hidden(X1,esk6_0)
    | ~ m1_subset_1(X1,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_70,negated_conjecture,
    ( m1_subset_1(X1,esk5_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_59])).

cnf(c_0_71,negated_conjecture,
    ( k4_subset_1(X1,esk7_0,esk8_0) != esk6_0
    | ~ m1_subset_1(esk8_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_21]),c_0_20])])).

cnf(c_0_72,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = X1
    | r2_hidden(esk3_3(X1,X2,X1),X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_55]),c_0_55])).

cnf(c_0_73,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_74,plain,
    ( r2_hidden(X1,k3_tarski(k2_tarski(X2,X3)))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_63])).

cnf(c_0_75,plain,
    ( X3 = k3_tarski(k2_tarski(X1,X2))
    | ~ r2_hidden(esk3_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk3_3(X1,X2,X3),X2) ),
    inference(rw,[status(thm)],[c_0_64,c_0_39])).

cnf(c_0_76,negated_conjecture,
    ( k3_tarski(k2_tarski(esk5_0,esk8_0)) = esk5_0
    | r2_hidden(esk3_3(esk5_0,esk8_0,esk5_0),esk5_0) ),
    inference(ef,[status(thm)],[c_0_65])).

cnf(c_0_77,plain,
    ( r1_tarski(esk2_2(k1_zfmisc_1(X1),X2),X1)
    | r1_tarski(k1_zfmisc_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_19,c_0_66])).

cnf(c_0_78,negated_conjecture,
    ( X1 = k3_tarski(k2_tarski(X2,esk8_0))
    | r2_hidden(esk3_3(X2,esk8_0,X1),esk6_0)
    | r2_hidden(esk3_3(X2,esk8_0,X1),X1)
    | r2_hidden(esk3_3(X2,esk8_0,X1),X2) ),
    inference(spm,[status(thm)],[c_0_67,c_0_47])).

cnf(c_0_79,negated_conjecture,
    ( k3_tarski(k2_tarski(esk7_0,esk7_0)) = esk6_0
    | r2_hidden(esk3_3(esk7_0,esk7_0,esk6_0),esk6_0) ),
    inference(ef,[status(thm)],[c_0_68])).

cnf(c_0_80,negated_conjecture,
    ( r2_hidden(X1,esk7_0)
    | ~ r2_hidden(X1,esk6_0)
    | ~ v1_xboole_0(esk8_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_69]),c_0_70])).

cnf(c_0_81,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = X2
    | r2_hidden(esk3_3(X1,X2,X2),X2)
    | r2_hidden(esk3_3(X1,X2,X2),X1) ),
    inference(ef,[status(thm)],[c_0_47])).

cnf(c_0_82,negated_conjecture,
    ( k3_tarski(k2_tarski(esk7_0,esk8_0)) != esk6_0
    | ~ m1_subset_1(esk8_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_71,c_0_52])).

cnf(c_0_83,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = X1
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_72])).

cnf(c_0_84,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_73])).

cnf(c_0_85,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))
    | ~ r2_hidden(esk2_2(X1,k3_tarski(k2_tarski(X2,X3))),X3) ),
    inference(spm,[status(thm)],[c_0_40,c_0_74])).

cnf(c_0_86,negated_conjecture,
    ( k3_tarski(k2_tarski(esk5_0,esk8_0)) = esk5_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_72])).

cnf(c_0_87,plain,
    ( r1_tarski(k1_zfmisc_1(X1),X2)
    | r2_hidden(X3,X1)
    | ~ r2_hidden(X3,esk2_2(k1_zfmisc_1(X1),X2)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_77])).

cnf(c_0_88,negated_conjecture,
    ( k3_tarski(k2_tarski(X1,esk8_0)) = esk6_0
    | r2_hidden(esk3_3(X1,esk8_0,esk6_0),esk6_0)
    | r2_hidden(esk3_3(X1,esk8_0,esk6_0),X1) ),
    inference(ef,[status(thm)],[c_0_78])).

cnf(c_0_89,negated_conjecture,
    ( k3_tarski(k2_tarski(esk7_0,esk7_0)) = esk6_0
    | ~ r2_hidden(esk3_3(esk7_0,esk7_0,esk6_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_75,c_0_79])).

cnf(c_0_90,negated_conjecture,
    ( k3_tarski(k2_tarski(X1,X2)) = esk7_0
    | ~ r2_hidden(esk3_3(X1,X2,esk7_0),esk6_0)
    | ~ r2_hidden(esk3_3(X1,X2,esk7_0),X2)
    | ~ v1_xboole_0(esk8_0) ),
    inference(spm,[status(thm)],[c_0_75,c_0_80])).

cnf(c_0_91,negated_conjecture,
    ( k3_tarski(k2_tarski(esk7_0,esk7_0)) = esk7_0
    | r2_hidden(esk3_3(esk7_0,esk7_0,esk7_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_68])).

cnf(c_0_92,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = X2
    | r2_hidden(esk3_3(X1,X2,X2),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_81]),c_0_81])).

cnf(c_0_93,negated_conjecture,
    ( esk7_0 != esk6_0
    | ~ m1_subset_1(esk8_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(esk8_0) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_94,plain,
    ( r1_tarski(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(esk2_2(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_15])).

cnf(c_0_95,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_35,c_0_84])).

cnf(c_0_96,negated_conjecture,
    ( r1_tarski(X1,esk5_0)
    | ~ r2_hidden(esk2_2(X1,esk5_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_97,plain,
    ( r1_tarski(esk2_2(k1_zfmisc_1(X1),X2),X3)
    | r1_tarski(k1_zfmisc_1(X1),X2)
    | r2_hidden(esk2_2(esk2_2(k1_zfmisc_1(X1),X2),X3),X1) ),
    inference(spm,[status(thm)],[c_0_87,c_0_29])).

cnf(c_0_98,negated_conjecture,
    ( k3_tarski(k2_tarski(esk7_0,esk8_0)) = esk6_0
    | r2_hidden(esk3_3(esk7_0,esk8_0,esk6_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_88])).

cnf(c_0_99,negated_conjecture,
    ( k3_tarski(k2_tarski(esk7_0,esk7_0)) = esk6_0
    | ~ v1_xboole_0(esk8_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_80]),c_0_79])).

cnf(c_0_100,negated_conjecture,
    ( k3_tarski(k2_tarski(esk7_0,esk7_0)) = esk7_0
    | ~ v1_xboole_0(esk8_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_92])).

cnf(c_0_101,negated_conjecture,
    ( esk7_0 != esk6_0
    | ~ v1_xboole_0(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_21]),c_0_20])])).

cnf(c_0_102,plain,
    ( r1_tarski(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(esk2_2(X1,k1_zfmisc_1(X2)),X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_16])).

cnf(c_0_103,negated_conjecture,
    ( r1_tarski(esk2_2(k1_zfmisc_1(esk8_0),X1),esk5_0)
    | r1_tarski(k1_zfmisc_1(esk8_0),X1) ),
    inference(spm,[status(thm)],[c_0_96,c_0_97])).

cnf(c_0_104,negated_conjecture,
    ( k3_tarski(k2_tarski(esk7_0,esk8_0)) = esk6_0
    | ~ r2_hidden(esk3_3(esk7_0,esk8_0,esk6_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_75,c_0_98])).

cnf(c_0_105,negated_conjecture,
    ( ~ v1_xboole_0(esk8_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_100]),c_0_101])).

cnf(c_0_106,negated_conjecture,
    ( r1_tarski(k1_zfmisc_1(esk8_0),k1_zfmisc_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_102,c_0_103])).

cnf(c_0_107,negated_conjecture,
    ( k3_tarski(k2_tarski(esk7_0,esk8_0)) = esk6_0
    | ~ r2_hidden(esk3_3(esk7_0,esk8_0,esk6_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_98])).

cnf(c_0_108,negated_conjecture,
    ( m1_subset_1(X1,esk8_0)
    | r2_hidden(X1,esk7_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_69]),c_0_70])).

cnf(c_0_109,negated_conjecture,
    ( k3_tarski(k2_tarski(esk7_0,esk8_0)) = esk6_0
    | ~ m1_subset_1(esk3_3(esk7_0,esk8_0,esk6_0),esk8_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_15]),c_0_105])).

cnf(c_0_110,negated_conjecture,
    ( r2_hidden(X1,k1_zfmisc_1(esk5_0))
    | ~ r2_hidden(X1,k1_zfmisc_1(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_106])).

cnf(c_0_111,negated_conjecture,
    ( k3_tarski(k2_tarski(esk7_0,esk8_0)) = esk6_0 ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_108]),c_0_98]),c_0_109])).

cnf(c_0_112,negated_conjecture,
    ( r2_hidden(X1,k1_zfmisc_1(esk5_0))
    | ~ r1_tarski(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_110,c_0_84])).

cnf(c_0_113,negated_conjecture,
    ( ~ m1_subset_1(esk8_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_82,c_0_111])])).

cnf(c_0_114,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(esk5_0))
    | ~ r1_tarski(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_112])).

cnf(c_0_115,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_29])).

cnf(c_0_116,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_114]),c_0_20]),c_0_115])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:48:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 9.73/9.96  # AutoSched0-Mode selected heuristic G_E___207_C01_F1_SE_CS_SP_PI_S5PRR_S0Y
% 9.73/9.96  # and selection function SelectMaxLComplexAvoidPosPred.
% 9.73/9.96  #
% 9.73/9.96  # Preprocessing time       : 0.039 s
% 9.73/9.96  
% 9.73/9.96  # Proof found!
% 9.73/9.96  # SZS status Theorem
% 9.73/9.96  # SZS output start CNFRefutation
% 9.73/9.96  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 9.73/9.96  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 9.73/9.96  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 9.73/9.96  fof(t15_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(X1))=>(![X5]:(m1_subset_1(X5,X1)=>(r2_hidden(X5,X2)<=>(r2_hidden(X5,X3)|r2_hidden(X5,X4))))=>X2=k4_subset_1(X1,X3,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_subset_1)).
% 9.73/9.96  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 9.73/9.96  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 9.73/9.96  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 9.73/9.96  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 9.73/9.96  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 9.73/9.96  fof(c_0_9, plain, ![X25, X26, X27, X28, X29, X30]:(((~r2_hidden(X27,X26)|r1_tarski(X27,X25)|X26!=k1_zfmisc_1(X25))&(~r1_tarski(X28,X25)|r2_hidden(X28,X26)|X26!=k1_zfmisc_1(X25)))&((~r2_hidden(esk4_2(X29,X30),X30)|~r1_tarski(esk4_2(X29,X30),X29)|X30=k1_zfmisc_1(X29))&(r2_hidden(esk4_2(X29,X30),X30)|r1_tarski(esk4_2(X29,X30),X29)|X30=k1_zfmisc_1(X29)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 9.73/9.96  cnf(c_0_10, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 9.73/9.96  fof(c_0_11, plain, ![X34, X35]:(((~m1_subset_1(X35,X34)|r2_hidden(X35,X34)|v1_xboole_0(X34))&(~r2_hidden(X35,X34)|m1_subset_1(X35,X34)|v1_xboole_0(X34)))&((~m1_subset_1(X35,X34)|v1_xboole_0(X35)|~v1_xboole_0(X34))&(~v1_xboole_0(X35)|m1_subset_1(X35,X34)|~v1_xboole_0(X34)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 9.73/9.96  fof(c_0_12, plain, ![X36]:~v1_xboole_0(k1_zfmisc_1(X36)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 9.73/9.96  fof(c_0_13, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(X1))=>(![X5]:(m1_subset_1(X5,X1)=>(r2_hidden(X5,X2)<=>(r2_hidden(X5,X3)|r2_hidden(X5,X4))))=>X2=k4_subset_1(X1,X3,X4)))))), inference(assume_negation,[status(cth)],[t15_subset_1])).
% 9.73/9.96  cnf(c_0_14, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_10])).
% 9.73/9.96  cnf(c_0_15, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 9.73/9.96  cnf(c_0_16, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 9.73/9.96  fof(c_0_17, negated_conjecture, ![X44]:(m1_subset_1(esk6_0,k1_zfmisc_1(esk5_0))&(m1_subset_1(esk7_0,k1_zfmisc_1(esk5_0))&(m1_subset_1(esk8_0,k1_zfmisc_1(esk5_0))&(((~r2_hidden(X44,esk6_0)|(r2_hidden(X44,esk7_0)|r2_hidden(X44,esk8_0))|~m1_subset_1(X44,esk5_0))&((~r2_hidden(X44,esk7_0)|r2_hidden(X44,esk6_0)|~m1_subset_1(X44,esk5_0))&(~r2_hidden(X44,esk8_0)|r2_hidden(X44,esk6_0)|~m1_subset_1(X44,esk5_0))))&esk6_0!=k4_subset_1(esk5_0,esk7_0,esk8_0))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])])])).
% 9.73/9.96  fof(c_0_18, plain, ![X10, X11, X12, X13, X14]:((~r1_tarski(X10,X11)|(~r2_hidden(X12,X10)|r2_hidden(X12,X11)))&((r2_hidden(esk2_2(X13,X14),X13)|r1_tarski(X13,X14))&(~r2_hidden(esk2_2(X13,X14),X14)|r1_tarski(X13,X14)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 9.73/9.96  cnf(c_0_19, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16])).
% 9.73/9.96  cnf(c_0_20, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 9.73/9.96  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 9.73/9.96  fof(c_0_22, plain, ![X6, X7, X8]:((~v1_xboole_0(X6)|~r2_hidden(X7,X6))&(r2_hidden(esk1_1(X8),X8)|v1_xboole_0(X8))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 9.73/9.96  cnf(c_0_23, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 9.73/9.96  cnf(c_0_24, negated_conjecture, (r1_tarski(esk7_0,esk5_0)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 9.73/9.96  cnf(c_0_25, negated_conjecture, (r1_tarski(esk8_0,esk5_0)), inference(spm,[status(thm)],[c_0_19, c_0_21])).
% 9.73/9.96  cnf(c_0_26, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 9.73/9.96  cnf(c_0_27, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 9.73/9.96  cnf(c_0_28, negated_conjecture, (r2_hidden(X1,esk5_0)|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 9.73/9.96  cnf(c_0_29, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 9.73/9.96  fof(c_0_30, plain, ![X16, X17, X18, X19, X20, X21, X22, X23]:(((~r2_hidden(X19,X18)|(r2_hidden(X19,X16)|r2_hidden(X19,X17))|X18!=k2_xboole_0(X16,X17))&((~r2_hidden(X20,X16)|r2_hidden(X20,X18)|X18!=k2_xboole_0(X16,X17))&(~r2_hidden(X20,X17)|r2_hidden(X20,X18)|X18!=k2_xboole_0(X16,X17))))&(((~r2_hidden(esk3_3(X21,X22,X23),X21)|~r2_hidden(esk3_3(X21,X22,X23),X23)|X23=k2_xboole_0(X21,X22))&(~r2_hidden(esk3_3(X21,X22,X23),X22)|~r2_hidden(esk3_3(X21,X22,X23),X23)|X23=k2_xboole_0(X21,X22)))&(r2_hidden(esk3_3(X21,X22,X23),X23)|(r2_hidden(esk3_3(X21,X22,X23),X21)|r2_hidden(esk3_3(X21,X22,X23),X22))|X23=k2_xboole_0(X21,X22)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 9.73/9.96  fof(c_0_31, plain, ![X32, X33]:k3_tarski(k2_tarski(X32,X33))=k2_xboole_0(X32,X33), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 9.73/9.96  cnf(c_0_32, negated_conjecture, (r2_hidden(X1,esk6_0)|~r2_hidden(X1,esk8_0)|~m1_subset_1(X1,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 9.73/9.96  cnf(c_0_33, negated_conjecture, (r2_hidden(X1,esk5_0)|~r2_hidden(X1,esk8_0)), inference(spm,[status(thm)],[c_0_23, c_0_25])).
% 9.73/9.96  cnf(c_0_34, negated_conjecture, (r2_hidden(X1,esk6_0)|~r2_hidden(X1,esk7_0)|~m1_subset_1(X1,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 9.73/9.96  cnf(c_0_35, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(csr,[status(thm)],[c_0_26, c_0_27])).
% 9.73/9.96  cnf(c_0_36, negated_conjecture, (r1_tarski(esk7_0,X1)|r2_hidden(esk2_2(esk7_0,X1),esk5_0)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 9.73/9.96  fof(c_0_37, plain, ![X37, X38, X39]:(~m1_subset_1(X38,k1_zfmisc_1(X37))|~m1_subset_1(X39,k1_zfmisc_1(X37))|k4_subset_1(X37,X38,X39)=k2_xboole_0(X38,X39)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 9.73/9.96  cnf(c_0_38, plain, (r2_hidden(esk3_3(X1,X2,X3),X3)|r2_hidden(esk3_3(X1,X2,X3),X1)|r2_hidden(esk3_3(X1,X2,X3),X2)|X3=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 9.73/9.96  cnf(c_0_39, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 9.73/9.96  cnf(c_0_40, plain, (r1_tarski(X1,X2)|~r2_hidden(esk2_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 9.73/9.96  cnf(c_0_41, negated_conjecture, (r1_tarski(esk8_0,X1)|r2_hidden(esk2_2(esk8_0,X1),esk6_0)|~m1_subset_1(esk2_2(esk8_0,X1),esk5_0)), inference(spm,[status(thm)],[c_0_32, c_0_29])).
% 9.73/9.96  cnf(c_0_42, negated_conjecture, (r1_tarski(esk8_0,X1)|r2_hidden(esk2_2(esk8_0,X1),esk5_0)), inference(spm,[status(thm)],[c_0_33, c_0_29])).
% 9.73/9.96  cnf(c_0_43, negated_conjecture, (r1_tarski(esk7_0,X1)|r2_hidden(esk2_2(esk7_0,X1),esk6_0)|~m1_subset_1(esk2_2(esk7_0,X1),esk5_0)), inference(spm,[status(thm)],[c_0_34, c_0_29])).
% 9.73/9.96  cnf(c_0_44, negated_conjecture, (m1_subset_1(esk2_2(esk7_0,X1),esk5_0)|r1_tarski(esk7_0,X1)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 9.73/9.96  cnf(c_0_45, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 9.73/9.96  cnf(c_0_46, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 9.73/9.96  cnf(c_0_47, plain, (X3=k3_tarski(k2_tarski(X1,X2))|r2_hidden(esk3_3(X1,X2,X3),X3)|r2_hidden(esk3_3(X1,X2,X3),X2)|r2_hidden(esk3_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_38, c_0_39])).
% 9.73/9.96  cnf(c_0_48, negated_conjecture, (r1_tarski(esk8_0,esk6_0)|~m1_subset_1(esk2_2(esk8_0,esk6_0),esk5_0)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 9.73/9.96  cnf(c_0_49, negated_conjecture, (m1_subset_1(esk2_2(esk8_0,X1),esk5_0)|r1_tarski(esk8_0,X1)), inference(spm,[status(thm)],[c_0_35, c_0_42])).
% 9.73/9.96  cnf(c_0_50, negated_conjecture, (r1_tarski(esk7_0,esk6_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_43]), c_0_44])).
% 9.73/9.96  cnf(c_0_51, negated_conjecture, (r1_tarski(esk6_0,esk5_0)), inference(spm,[status(thm)],[c_0_19, c_0_45])).
% 9.73/9.96  cnf(c_0_52, plain, (k4_subset_1(X2,X1,X3)=k3_tarski(k2_tarski(X1,X3))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_46, c_0_39])).
% 9.73/9.96  cnf(c_0_53, plain, (X3=k2_xboole_0(X1,X2)|~r2_hidden(esk3_3(X1,X2,X3),X1)|~r2_hidden(esk3_3(X1,X2,X3),X3)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 9.73/9.96  cnf(c_0_54, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 9.73/9.96  cnf(c_0_55, plain, (k3_tarski(k2_tarski(X1,X2))=X1|r2_hidden(esk3_3(X1,X2,X1),X1)|r2_hidden(esk3_3(X1,X2,X1),X2)), inference(ef,[status(thm)],[c_0_47])).
% 9.73/9.96  cnf(c_0_56, negated_conjecture, (r1_tarski(esk8_0,esk6_0)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 9.73/9.96  cnf(c_0_57, negated_conjecture, (r2_hidden(X1,esk6_0)|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_23, c_0_50])).
% 9.73/9.96  cnf(c_0_58, plain, (X1=k3_tarski(k2_tarski(X2,X2))|r2_hidden(esk3_3(X2,X2,X1),X1)|r2_hidden(esk3_3(X2,X2,X1),X2)), inference(ef,[status(thm)],[c_0_47])).
% 9.73/9.96  cnf(c_0_59, negated_conjecture, (r2_hidden(X1,esk5_0)|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_23, c_0_51])).
% 9.73/9.96  cnf(c_0_60, negated_conjecture, (esk6_0!=k4_subset_1(esk5_0,esk7_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 9.73/9.96  cnf(c_0_61, plain, (k4_subset_1(X1,X2,X3)=k4_subset_1(X4,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X4))|~m1_subset_1(X2,k1_zfmisc_1(X4))), inference(spm,[status(thm)],[c_0_52, c_0_52])).
% 9.73/9.96  cnf(c_0_62, plain, (X3=k3_tarski(k2_tarski(X1,X2))|~r2_hidden(esk3_3(X1,X2,X3),X3)|~r2_hidden(esk3_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_53, c_0_39])).
% 9.73/9.96  cnf(c_0_63, plain, (r2_hidden(X1,X3)|X3!=k3_tarski(k2_tarski(X4,X2))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_54, c_0_39])).
% 9.73/9.96  cnf(c_0_64, plain, (X3=k2_xboole_0(X1,X2)|~r2_hidden(esk3_3(X1,X2,X3),X2)|~r2_hidden(esk3_3(X1,X2,X3),X3)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 9.73/9.96  cnf(c_0_65, negated_conjecture, (k3_tarski(k2_tarski(X1,esk8_0))=X1|r2_hidden(esk3_3(X1,esk8_0,X1),esk5_0)|r2_hidden(esk3_3(X1,esk8_0,X1),X1)), inference(spm,[status(thm)],[c_0_33, c_0_55])).
% 9.73/9.96  cnf(c_0_66, plain, (m1_subset_1(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_35, c_0_29])).
% 9.73/9.96  cnf(c_0_67, negated_conjecture, (r2_hidden(X1,esk6_0)|~r2_hidden(X1,esk8_0)), inference(spm,[status(thm)],[c_0_23, c_0_56])).
% 9.73/9.96  cnf(c_0_68, negated_conjecture, (X1=k3_tarski(k2_tarski(esk7_0,esk7_0))|r2_hidden(esk3_3(esk7_0,esk7_0,X1),esk6_0)|r2_hidden(esk3_3(esk7_0,esk7_0,X1),X1)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 9.73/9.96  cnf(c_0_69, negated_conjecture, (r2_hidden(X1,esk7_0)|r2_hidden(X1,esk8_0)|~r2_hidden(X1,esk6_0)|~m1_subset_1(X1,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 9.73/9.96  cnf(c_0_70, negated_conjecture, (m1_subset_1(X1,esk5_0)|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_35, c_0_59])).
% 9.73/9.96  cnf(c_0_71, negated_conjecture, (k4_subset_1(X1,esk7_0,esk8_0)!=esk6_0|~m1_subset_1(esk8_0,k1_zfmisc_1(X1))|~m1_subset_1(esk7_0,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_21]), c_0_20])])).
% 9.73/9.96  cnf(c_0_72, plain, (k3_tarski(k2_tarski(X1,X2))=X1|r2_hidden(esk3_3(X1,X2,X1),X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_55]), c_0_55])).
% 9.73/9.96  cnf(c_0_73, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 9.73/9.96  cnf(c_0_74, plain, (r2_hidden(X1,k3_tarski(k2_tarski(X2,X3)))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_63])).
% 9.73/9.96  cnf(c_0_75, plain, (X3=k3_tarski(k2_tarski(X1,X2))|~r2_hidden(esk3_3(X1,X2,X3),X3)|~r2_hidden(esk3_3(X1,X2,X3),X2)), inference(rw,[status(thm)],[c_0_64, c_0_39])).
% 9.73/9.96  cnf(c_0_76, negated_conjecture, (k3_tarski(k2_tarski(esk5_0,esk8_0))=esk5_0|r2_hidden(esk3_3(esk5_0,esk8_0,esk5_0),esk5_0)), inference(ef,[status(thm)],[c_0_65])).
% 9.73/9.96  cnf(c_0_77, plain, (r1_tarski(esk2_2(k1_zfmisc_1(X1),X2),X1)|r1_tarski(k1_zfmisc_1(X1),X2)), inference(spm,[status(thm)],[c_0_19, c_0_66])).
% 9.73/9.96  cnf(c_0_78, negated_conjecture, (X1=k3_tarski(k2_tarski(X2,esk8_0))|r2_hidden(esk3_3(X2,esk8_0,X1),esk6_0)|r2_hidden(esk3_3(X2,esk8_0,X1),X1)|r2_hidden(esk3_3(X2,esk8_0,X1),X2)), inference(spm,[status(thm)],[c_0_67, c_0_47])).
% 9.73/9.96  cnf(c_0_79, negated_conjecture, (k3_tarski(k2_tarski(esk7_0,esk7_0))=esk6_0|r2_hidden(esk3_3(esk7_0,esk7_0,esk6_0),esk6_0)), inference(ef,[status(thm)],[c_0_68])).
% 9.73/9.96  cnf(c_0_80, negated_conjecture, (r2_hidden(X1,esk7_0)|~r2_hidden(X1,esk6_0)|~v1_xboole_0(esk8_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_69]), c_0_70])).
% 9.73/9.96  cnf(c_0_81, plain, (k3_tarski(k2_tarski(X1,X2))=X2|r2_hidden(esk3_3(X1,X2,X2),X2)|r2_hidden(esk3_3(X1,X2,X2),X1)), inference(ef,[status(thm)],[c_0_47])).
% 9.73/9.96  cnf(c_0_82, negated_conjecture, (k3_tarski(k2_tarski(esk7_0,esk8_0))!=esk6_0|~m1_subset_1(esk8_0,k1_zfmisc_1(X1))|~m1_subset_1(esk7_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_71, c_0_52])).
% 9.73/9.96  cnf(c_0_83, plain, (k3_tarski(k2_tarski(X1,X2))=X1|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_27, c_0_72])).
% 9.73/9.96  cnf(c_0_84, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_73])).
% 9.73/9.96  cnf(c_0_85, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))|~r2_hidden(esk2_2(X1,k3_tarski(k2_tarski(X2,X3))),X3)), inference(spm,[status(thm)],[c_0_40, c_0_74])).
% 9.73/9.96  cnf(c_0_86, negated_conjecture, (k3_tarski(k2_tarski(esk5_0,esk8_0))=esk5_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_72])).
% 9.73/9.96  cnf(c_0_87, plain, (r1_tarski(k1_zfmisc_1(X1),X2)|r2_hidden(X3,X1)|~r2_hidden(X3,esk2_2(k1_zfmisc_1(X1),X2))), inference(spm,[status(thm)],[c_0_23, c_0_77])).
% 9.73/9.96  cnf(c_0_88, negated_conjecture, (k3_tarski(k2_tarski(X1,esk8_0))=esk6_0|r2_hidden(esk3_3(X1,esk8_0,esk6_0),esk6_0)|r2_hidden(esk3_3(X1,esk8_0,esk6_0),X1)), inference(ef,[status(thm)],[c_0_78])).
% 9.73/9.96  cnf(c_0_89, negated_conjecture, (k3_tarski(k2_tarski(esk7_0,esk7_0))=esk6_0|~r2_hidden(esk3_3(esk7_0,esk7_0,esk6_0),esk7_0)), inference(spm,[status(thm)],[c_0_75, c_0_79])).
% 9.73/9.96  cnf(c_0_90, negated_conjecture, (k3_tarski(k2_tarski(X1,X2))=esk7_0|~r2_hidden(esk3_3(X1,X2,esk7_0),esk6_0)|~r2_hidden(esk3_3(X1,X2,esk7_0),X2)|~v1_xboole_0(esk8_0)), inference(spm,[status(thm)],[c_0_75, c_0_80])).
% 9.73/9.96  cnf(c_0_91, negated_conjecture, (k3_tarski(k2_tarski(esk7_0,esk7_0))=esk7_0|r2_hidden(esk3_3(esk7_0,esk7_0,esk7_0),esk6_0)), inference(spm,[status(thm)],[c_0_57, c_0_68])).
% 9.73/9.96  cnf(c_0_92, plain, (k3_tarski(k2_tarski(X1,X2))=X2|r2_hidden(esk3_3(X1,X2,X2),X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_81]), c_0_81])).
% 9.73/9.96  cnf(c_0_93, negated_conjecture, (esk7_0!=esk6_0|~m1_subset_1(esk8_0,k1_zfmisc_1(X1))|~m1_subset_1(esk7_0,k1_zfmisc_1(X1))|~v1_xboole_0(esk8_0)), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 9.73/9.96  cnf(c_0_94, plain, (r1_tarski(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(esk2_2(X1,X2),X2)), inference(spm,[status(thm)],[c_0_40, c_0_15])).
% 9.73/9.96  cnf(c_0_95, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_35, c_0_84])).
% 9.73/9.96  cnf(c_0_96, negated_conjecture, (r1_tarski(X1,esk5_0)|~r2_hidden(esk2_2(X1,esk5_0),esk8_0)), inference(spm,[status(thm)],[c_0_85, c_0_86])).
% 9.73/9.96  cnf(c_0_97, plain, (r1_tarski(esk2_2(k1_zfmisc_1(X1),X2),X3)|r1_tarski(k1_zfmisc_1(X1),X2)|r2_hidden(esk2_2(esk2_2(k1_zfmisc_1(X1),X2),X3),X1)), inference(spm,[status(thm)],[c_0_87, c_0_29])).
% 9.73/9.96  cnf(c_0_98, negated_conjecture, (k3_tarski(k2_tarski(esk7_0,esk8_0))=esk6_0|r2_hidden(esk3_3(esk7_0,esk8_0,esk6_0),esk6_0)), inference(spm,[status(thm)],[c_0_57, c_0_88])).
% 9.73/9.97  cnf(c_0_99, negated_conjecture, (k3_tarski(k2_tarski(esk7_0,esk7_0))=esk6_0|~v1_xboole_0(esk8_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_80]), c_0_79])).
% 9.73/9.97  cnf(c_0_100, negated_conjecture, (k3_tarski(k2_tarski(esk7_0,esk7_0))=esk7_0|~v1_xboole_0(esk8_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_91]), c_0_92])).
% 9.73/9.97  cnf(c_0_101, negated_conjecture, (esk7_0!=esk6_0|~v1_xboole_0(esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_21]), c_0_20])])).
% 9.73/9.97  cnf(c_0_102, plain, (r1_tarski(X1,k1_zfmisc_1(X2))|~r1_tarski(esk2_2(X1,k1_zfmisc_1(X2)),X2)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_95]), c_0_16])).
% 9.73/9.97  cnf(c_0_103, negated_conjecture, (r1_tarski(esk2_2(k1_zfmisc_1(esk8_0),X1),esk5_0)|r1_tarski(k1_zfmisc_1(esk8_0),X1)), inference(spm,[status(thm)],[c_0_96, c_0_97])).
% 9.73/9.97  cnf(c_0_104, negated_conjecture, (k3_tarski(k2_tarski(esk7_0,esk8_0))=esk6_0|~r2_hidden(esk3_3(esk7_0,esk8_0,esk6_0),esk8_0)), inference(spm,[status(thm)],[c_0_75, c_0_98])).
% 9.73/9.97  cnf(c_0_105, negated_conjecture, (~v1_xboole_0(esk8_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_100]), c_0_101])).
% 9.73/9.97  cnf(c_0_106, negated_conjecture, (r1_tarski(k1_zfmisc_1(esk8_0),k1_zfmisc_1(esk5_0))), inference(spm,[status(thm)],[c_0_102, c_0_103])).
% 9.73/9.97  cnf(c_0_107, negated_conjecture, (k3_tarski(k2_tarski(esk7_0,esk8_0))=esk6_0|~r2_hidden(esk3_3(esk7_0,esk8_0,esk6_0),esk7_0)), inference(spm,[status(thm)],[c_0_62, c_0_98])).
% 9.73/9.97  cnf(c_0_108, negated_conjecture, (m1_subset_1(X1,esk8_0)|r2_hidden(X1,esk7_0)|~r2_hidden(X1,esk6_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_69]), c_0_70])).
% 9.73/9.97  cnf(c_0_109, negated_conjecture, (k3_tarski(k2_tarski(esk7_0,esk8_0))=esk6_0|~m1_subset_1(esk3_3(esk7_0,esk8_0,esk6_0),esk8_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_15]), c_0_105])).
% 9.73/9.97  cnf(c_0_110, negated_conjecture, (r2_hidden(X1,k1_zfmisc_1(esk5_0))|~r2_hidden(X1,k1_zfmisc_1(esk8_0))), inference(spm,[status(thm)],[c_0_23, c_0_106])).
% 9.73/9.97  cnf(c_0_111, negated_conjecture, (k3_tarski(k2_tarski(esk7_0,esk8_0))=esk6_0), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_108]), c_0_98]), c_0_109])).
% 9.73/9.97  cnf(c_0_112, negated_conjecture, (r2_hidden(X1,k1_zfmisc_1(esk5_0))|~r1_tarski(X1,esk8_0)), inference(spm,[status(thm)],[c_0_110, c_0_84])).
% 9.73/9.97  cnf(c_0_113, negated_conjecture, (~m1_subset_1(esk8_0,k1_zfmisc_1(X1))|~m1_subset_1(esk7_0,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_82, c_0_111])])).
% 9.73/9.97  cnf(c_0_114, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(esk5_0))|~r1_tarski(X1,esk8_0)), inference(spm,[status(thm)],[c_0_35, c_0_112])).
% 9.73/9.97  cnf(c_0_115, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_40, c_0_29])).
% 9.73/9.97  cnf(c_0_116, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_114]), c_0_20]), c_0_115])]), ['proof']).
% 9.73/9.97  # SZS output end CNFRefutation
% 9.73/9.97  # Proof object total steps             : 117
% 9.73/9.97  # Proof object clause steps            : 98
% 9.73/9.97  # Proof object formula steps           : 19
% 9.73/9.97  # Proof object conjectures             : 60
% 9.73/9.97  # Proof object clause conjectures      : 57
% 9.73/9.97  # Proof object formula conjectures     : 3
% 9.73/9.97  # Proof object initial clauses used    : 22
% 9.73/9.97  # Proof object initial formulas used   : 9
% 9.73/9.97  # Proof object generating inferences   : 66
% 9.73/9.97  # Proof object simplifying inferences  : 33
% 9.73/9.97  # Training examples: 0 positive, 0 negative
% 9.73/9.97  # Parsed axioms                        : 9
% 9.73/9.97  # Removed by relevancy pruning/SinE    : 0
% 9.73/9.97  # Initial clauses                      : 29
% 9.73/9.97  # Removed in clause preprocessing      : 1
% 9.73/9.97  # Initial clauses in saturation        : 28
% 9.73/9.97  # Processed clauses                    : 32338
% 9.73/9.97  # ...of these trivial                  : 129
% 9.73/9.97  # ...subsumed                          : 27286
% 9.73/9.97  # ...remaining for further processing  : 4923
% 9.73/9.97  # Other redundant clauses eliminated   : 5
% 9.73/9.97  # Clauses deleted for lack of memory   : 0
% 9.73/9.97  # Backward-subsumed                    : 401
% 9.73/9.97  # Backward-rewritten                   : 154
% 9.73/9.97  # Generated clauses                    : 789885
% 9.73/9.97  # ...of the previous two non-trivial   : 779435
% 9.73/9.97  # Contextual simplify-reflections      : 202
% 9.73/9.97  # Paramodulations                      : 786392
% 9.73/9.97  # Factorizations                       : 3476
% 9.73/9.97  # Equation resolutions                 : 5
% 9.73/9.97  # Propositional unsat checks           : 0
% 9.73/9.97  #    Propositional check models        : 0
% 9.73/9.97  #    Propositional check unsatisfiable : 0
% 9.73/9.97  #    Propositional clauses             : 0
% 9.73/9.97  #    Propositional clauses after purity: 0
% 9.73/9.97  #    Propositional unsat core size     : 0
% 9.73/9.97  #    Propositional preprocessing time  : 0.000
% 9.73/9.97  #    Propositional encoding time       : 0.000
% 9.73/9.97  #    Propositional solver time         : 0.000
% 9.73/9.97  #    Success case prop preproc time    : 0.000
% 9.73/9.97  #    Success case prop encoding time   : 0.000
% 9.73/9.97  #    Success case prop solver time     : 0.000
% 9.73/9.97  # Current number of processed clauses  : 4351
% 9.73/9.97  #    Positive orientable unit clauses  : 224
% 9.73/9.97  #    Positive unorientable unit clauses: 0
% 9.73/9.97  #    Negative unit clauses             : 6
% 9.73/9.97  #    Non-unit-clauses                  : 4121
% 9.73/9.97  # Current number of unprocessed clauses: 743266
% 9.73/9.97  # ...number of literals in the above   : 4102848
% 9.73/9.97  # Current number of archived formulas  : 0
% 9.73/9.97  # Current number of archived clauses   : 568
% 9.73/9.97  # Clause-clause subsumption calls (NU) : 3417297
% 9.73/9.97  # Rec. Clause-clause subsumption calls : 955496
% 9.73/9.97  # Non-unit clause-clause subsumptions  : 11795
% 9.73/9.97  # Unit Clause-clause subsumption calls : 45015
% 9.73/9.97  # Rewrite failures with RHS unbound    : 0
% 9.73/9.97  # BW rewrite match attempts            : 2106
% 9.73/9.97  # BW rewrite match successes           : 22
% 9.73/9.97  # Condensation attempts                : 0
% 9.73/9.97  # Condensation successes               : 0
% 9.73/9.97  # Termbank termtop insertions          : 25569824
% 9.82/10.00  
% 9.82/10.00  # -------------------------------------------------
% 9.82/10.00  # User time                : 9.238 s
% 9.82/10.00  # System time              : 0.422 s
% 9.82/10.00  # Total time               : 9.660 s
% 9.82/10.00  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
