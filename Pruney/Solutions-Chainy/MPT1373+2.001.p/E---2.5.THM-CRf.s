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
% DateTime   : Thu Dec  3 11:14:16 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 617 expanded)
%              Number of clauses        :   35 ( 234 expanded)
%              Number of leaves         :    6 ( 147 expanded)
%              Depth                    :   12
%              Number of atoms          :  256 (3487 expanded)
%              Number of equality atoms :   26 ( 403 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal clause size      :   61 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t28_compts_1,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                 => ( X3 = X4
                   => ( v2_compts_1(X3,X1)
                    <=> v2_compts_1(X4,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_compts_1)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(d9_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ( m1_pre_topc(X2,X1)
          <=> ( r1_tarski(k2_struct_0(X2),k2_struct_0(X1))
              & ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                 => ( r2_hidden(X3,u1_pre_topc(X2))
                  <=> ? [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                        & r2_hidden(X4,u1_pre_topc(X1))
                        & X3 = k9_subset_1(u1_struct_0(X2),X4,k2_struct_0(X2)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_pre_topc)).

fof(dt_k1_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( v1_pre_topc(k1_pre_topc(X1,X2))
        & m1_pre_topc(k1_pre_topc(X1,X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_pre_topc)).

fof(d10_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( ( v1_pre_topc(X3)
                & m1_pre_topc(X3,X1) )
             => ( X3 = k1_pre_topc(X1,X2)
              <=> k2_struct_0(X3) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_pre_topc)).

fof(t11_compts_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( r1_tarski(X3,k2_struct_0(X2))
               => ( v2_compts_1(X3,X1)
                <=> ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                     => ( X4 = X3
                       => v2_compts_1(X4,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_compts_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_pre_topc(X2,X1)
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( X3 = X4
                     => ( v2_compts_1(X3,X1)
                      <=> v2_compts_1(X4,X2) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t28_compts_1])).

fof(c_0_7,negated_conjecture,
    ( l1_pre_topc(esk5_0)
    & m1_pre_topc(esk6_0,esk5_0)
    & m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk5_0)))
    & m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(esk6_0)))
    & esk7_0 = esk8_0
    & ( ~ v2_compts_1(esk7_0,esk5_0)
      | ~ v2_compts_1(esk8_0,esk6_0) )
    & ( v2_compts_1(esk7_0,esk5_0)
      | v2_compts_1(esk8_0,esk6_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

fof(c_0_8,plain,(
    ! [X18,X19] :
      ( ~ l1_pre_topc(X18)
      | ~ m1_pre_topc(X19,X18)
      | l1_pre_topc(X19) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_9,plain,(
    ! [X8,X9,X10,X12,X14] :
      ( ( r1_tarski(k2_struct_0(X9),k2_struct_0(X8))
        | ~ m1_pre_topc(X9,X8)
        | ~ l1_pre_topc(X9)
        | ~ l1_pre_topc(X8) )
      & ( m1_subset_1(esk1_3(X8,X9,X10),k1_zfmisc_1(u1_struct_0(X8)))
        | ~ r2_hidden(X10,u1_pre_topc(X9))
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
        | ~ m1_pre_topc(X9,X8)
        | ~ l1_pre_topc(X9)
        | ~ l1_pre_topc(X8) )
      & ( r2_hidden(esk1_3(X8,X9,X10),u1_pre_topc(X8))
        | ~ r2_hidden(X10,u1_pre_topc(X9))
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
        | ~ m1_pre_topc(X9,X8)
        | ~ l1_pre_topc(X9)
        | ~ l1_pre_topc(X8) )
      & ( X10 = k9_subset_1(u1_struct_0(X9),esk1_3(X8,X9,X10),k2_struct_0(X9))
        | ~ r2_hidden(X10,u1_pre_topc(X9))
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
        | ~ m1_pre_topc(X9,X8)
        | ~ l1_pre_topc(X9)
        | ~ l1_pre_topc(X8) )
      & ( ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ r2_hidden(X12,u1_pre_topc(X8))
        | X10 != k9_subset_1(u1_struct_0(X9),X12,k2_struct_0(X9))
        | r2_hidden(X10,u1_pre_topc(X9))
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
        | ~ m1_pre_topc(X9,X8)
        | ~ l1_pre_topc(X9)
        | ~ l1_pre_topc(X8) )
      & ( m1_subset_1(esk2_2(X8,X9),k1_zfmisc_1(u1_struct_0(X9)))
        | ~ r1_tarski(k2_struct_0(X9),k2_struct_0(X8))
        | m1_pre_topc(X9,X8)
        | ~ l1_pre_topc(X9)
        | ~ l1_pre_topc(X8) )
      & ( ~ r2_hidden(esk2_2(X8,X9),u1_pre_topc(X9))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ r2_hidden(X14,u1_pre_topc(X8))
        | esk2_2(X8,X9) != k9_subset_1(u1_struct_0(X9),X14,k2_struct_0(X9))
        | ~ r1_tarski(k2_struct_0(X9),k2_struct_0(X8))
        | m1_pre_topc(X9,X8)
        | ~ l1_pre_topc(X9)
        | ~ l1_pre_topc(X8) )
      & ( m1_subset_1(esk3_2(X8,X9),k1_zfmisc_1(u1_struct_0(X8)))
        | r2_hidden(esk2_2(X8,X9),u1_pre_topc(X9))
        | ~ r1_tarski(k2_struct_0(X9),k2_struct_0(X8))
        | m1_pre_topc(X9,X8)
        | ~ l1_pre_topc(X9)
        | ~ l1_pre_topc(X8) )
      & ( r2_hidden(esk3_2(X8,X9),u1_pre_topc(X8))
        | r2_hidden(esk2_2(X8,X9),u1_pre_topc(X9))
        | ~ r1_tarski(k2_struct_0(X9),k2_struct_0(X8))
        | m1_pre_topc(X9,X8)
        | ~ l1_pre_topc(X9)
        | ~ l1_pre_topc(X8) )
      & ( esk2_2(X8,X9) = k9_subset_1(u1_struct_0(X9),esk3_2(X8,X9),k2_struct_0(X9))
        | r2_hidden(esk2_2(X8,X9),u1_pre_topc(X9))
        | ~ r1_tarski(k2_struct_0(X9),k2_struct_0(X8))
        | m1_pre_topc(X9,X8)
        | ~ l1_pre_topc(X9)
        | ~ l1_pre_topc(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_pre_topc])])])])])).

fof(c_0_10,plain,(
    ! [X16,X17] :
      ( ( v1_pre_topc(k1_pre_topc(X16,X17))
        | ~ l1_pre_topc(X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16))) )
      & ( m1_pre_topc(k1_pre_topc(X16,X17),X16)
        | ~ l1_pre_topc(X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_pre_topc])])])).

cnf(c_0_11,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( esk7_0 = esk8_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( m1_pre_topc(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_15,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_16,plain,(
    ! [X5,X6,X7] :
      ( ( X7 != k1_pre_topc(X5,X6)
        | k2_struct_0(X7) = X6
        | ~ v1_pre_topc(X7)
        | ~ m1_pre_topc(X7,X5)
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
        | ~ l1_pre_topc(X5) )
      & ( k2_struct_0(X7) != X6
        | X7 = k1_pre_topc(X5,X6)
        | ~ v1_pre_topc(X7)
        | ~ m1_pre_topc(X7,X5)
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
        | ~ l1_pre_topc(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_pre_topc])])])])).

cnf(c_0_17,plain,
    ( r1_tarski(k2_struct_0(X1),k2_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_18,plain,
    ( m1_pre_topc(k1_pre_topc(X1,X2),X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(rw,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_20,negated_conjecture,
    ( l1_pre_topc(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15])])).

cnf(c_0_21,plain,
    ( k2_struct_0(X1) = X3
    | X1 != k1_pre_topc(X2,X3)
    | ~ v1_pre_topc(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( v1_pre_topc(k1_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_23,plain,(
    ! [X20,X21,X22,X23] :
      ( ( ~ v2_compts_1(X22,X20)
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X21)))
        | X23 != X22
        | v2_compts_1(X23,X21)
        | ~ r1_tarski(X22,k2_struct_0(X21))
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X20)))
        | ~ m1_pre_topc(X21,X20)
        | ~ l1_pre_topc(X20) )
      & ( m1_subset_1(esk4_3(X20,X21,X22),k1_zfmisc_1(u1_struct_0(X21)))
        | v2_compts_1(X22,X20)
        | ~ r1_tarski(X22,k2_struct_0(X21))
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X20)))
        | ~ m1_pre_topc(X21,X20)
        | ~ l1_pre_topc(X20) )
      & ( esk4_3(X20,X21,X22) = X22
        | v2_compts_1(X22,X20)
        | ~ r1_tarski(X22,k2_struct_0(X21))
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X20)))
        | ~ m1_pre_topc(X21,X20)
        | ~ l1_pre_topc(X20) )
      & ( ~ v2_compts_1(esk4_3(X20,X21,X22),X21)
        | v2_compts_1(X22,X20)
        | ~ r1_tarski(X22,k2_struct_0(X21))
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X20)))
        | ~ m1_pre_topc(X21,X20)
        | ~ l1_pre_topc(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_compts_1])])])])])).

cnf(c_0_24,plain,
    ( r1_tarski(k2_struct_0(X1),k2_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_17,c_0_13])).

cnf(c_0_25,negated_conjecture,
    ( m1_pre_topc(k1_pre_topc(esk6_0,esk7_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])])).

cnf(c_0_26,plain,
    ( k2_struct_0(k1_pre_topc(X1,X2)) = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_21]),c_0_22]),c_0_18])).

cnf(c_0_27,plain,
    ( v2_compts_1(X3,X4)
    | ~ v2_compts_1(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
    | X3 != X1
    | ~ r1_tarski(X1,k2_struct_0(X4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X4,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(k2_struct_0(k1_pre_topc(esk6_0,esk7_0)),k2_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_20])])).

cnf(c_0_29,negated_conjecture,
    ( k2_struct_0(k1_pre_topc(esk6_0,esk7_0)) = esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_19]),c_0_20])])).

cnf(c_0_30,plain,
    ( v2_compts_1(X1,X2)
    | ~ v2_compts_1(X1,X3)
    | ~ r1_tarski(X1,k2_struct_0(X2))
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_pre_topc(X3) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(esk7_0,k2_struct_0(esk6_0)) ),
    inference(rw,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_32,negated_conjecture,
    ( v2_compts_1(esk7_0,esk5_0)
    | v2_compts_1(esk8_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_33,plain,
    ( v2_compts_1(X3,X1)
    | ~ v2_compts_1(esk4_3(X1,X2,X3),X2)
    | ~ r1_tarski(X3,k2_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,negated_conjecture,
    ( ~ v2_compts_1(esk7_0,esk5_0)
    | ~ v2_compts_1(esk8_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_35,negated_conjecture,
    ( v2_compts_1(esk7_0,esk6_0)
    | ~ v2_compts_1(esk7_0,X1)
    | ~ m1_pre_topc(esk6_0,X1)
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_19])])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_37,negated_conjecture,
    ( v2_compts_1(esk7_0,esk6_0)
    | v2_compts_1(esk7_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_32,c_0_12])).

cnf(c_0_38,negated_conjecture,
    ( v2_compts_1(k2_struct_0(k1_pre_topc(esk6_0,esk7_0)),X1)
    | ~ v2_compts_1(esk4_3(X1,esk6_0,k2_struct_0(k1_pre_topc(esk6_0,esk7_0))),esk6_0)
    | ~ m1_pre_topc(esk6_0,X1)
    | ~ m1_subset_1(k2_struct_0(k1_pre_topc(esk6_0,esk7_0)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_28])).

cnf(c_0_39,plain,
    ( esk4_3(X1,X2,X3) = X3
    | v2_compts_1(X3,X1)
    | ~ r1_tarski(X3,k2_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_40,negated_conjecture,
    ( ~ v2_compts_1(esk7_0,esk5_0)
    | ~ v2_compts_1(esk7_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_34,c_0_12])).

cnf(c_0_41,negated_conjecture,
    ( v2_compts_1(esk7_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_14]),c_0_36]),c_0_15])]),c_0_37])).

cnf(c_0_42,negated_conjecture,
    ( v2_compts_1(k2_struct_0(k1_pre_topc(esk6_0,esk7_0)),esk5_0)
    | ~ v2_compts_1(esk4_3(esk5_0,esk6_0,k2_struct_0(k1_pre_topc(esk6_0,esk7_0))),esk6_0)
    | ~ m1_subset_1(k2_struct_0(k1_pre_topc(esk6_0,esk7_0)),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_14]),c_0_15])])).

cnf(c_0_43,negated_conjecture,
    ( esk4_3(X1,esk6_0,esk7_0) = esk7_0
    | v2_compts_1(esk7_0,X1)
    | ~ m1_pre_topc(esk6_0,X1)
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_31])).

cnf(c_0_44,negated_conjecture,
    ( ~ v2_compts_1(esk7_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_41])])).

cnf(c_0_45,negated_conjecture,
    ( v2_compts_1(esk7_0,esk5_0)
    | ~ v2_compts_1(esk4_3(esk5_0,esk6_0,esk7_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_29]),c_0_29]),c_0_29]),c_0_36])])).

cnf(c_0_46,negated_conjecture,
    ( esk4_3(esk5_0,esk6_0,esk7_0) = esk7_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_14]),c_0_36]),c_0_15])]),c_0_44])).

cnf(c_0_47,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_46]),c_0_41])]),c_0_44]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:07:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___008_C18_F1_PI_SE_CS_SP_CO_S4S
% 0.13/0.38  # and selection function SelectNewComplexAHPNS.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.028 s
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t28_compts_1, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>(X3=X4=>(v2_compts_1(X3,X1)<=>v2_compts_1(X4,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_compts_1)).
% 0.13/0.38  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.13/0.38  fof(d9_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>(m1_pre_topc(X2,X1)<=>(r1_tarski(k2_struct_0(X2),k2_struct_0(X1))&![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))=>(r2_hidden(X3,u1_pre_topc(X2))<=>?[X4]:((m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))&r2_hidden(X4,u1_pre_topc(X1)))&X3=k9_subset_1(u1_struct_0(X2),X4,k2_struct_0(X2))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_pre_topc)).
% 0.13/0.38  fof(dt_k1_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v1_pre_topc(k1_pre_topc(X1,X2))&m1_pre_topc(k1_pre_topc(X1,X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_pre_topc)).
% 0.13/0.38  fof(d10_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:((v1_pre_topc(X3)&m1_pre_topc(X3,X1))=>(X3=k1_pre_topc(X1,X2)<=>k2_struct_0(X3)=X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_pre_topc)).
% 0.13/0.38  fof(t11_compts_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r1_tarski(X3,k2_struct_0(X2))=>(v2_compts_1(X3,X1)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>(X4=X3=>v2_compts_1(X4,X2)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_compts_1)).
% 0.13/0.38  fof(c_0_6, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>(X3=X4=>(v2_compts_1(X3,X1)<=>v2_compts_1(X4,X2)))))))), inference(assume_negation,[status(cth)],[t28_compts_1])).
% 0.13/0.38  fof(c_0_7, negated_conjecture, (l1_pre_topc(esk5_0)&(m1_pre_topc(esk6_0,esk5_0)&(m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk5_0)))&(m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(esk6_0)))&(esk7_0=esk8_0&((~v2_compts_1(esk7_0,esk5_0)|~v2_compts_1(esk8_0,esk6_0))&(v2_compts_1(esk7_0,esk5_0)|v2_compts_1(esk8_0,esk6_0)))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).
% 0.13/0.38  fof(c_0_8, plain, ![X18, X19]:(~l1_pre_topc(X18)|(~m1_pre_topc(X19,X18)|l1_pre_topc(X19))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.13/0.38  fof(c_0_9, plain, ![X8, X9, X10, X12, X14]:(((r1_tarski(k2_struct_0(X9),k2_struct_0(X8))|~m1_pre_topc(X9,X8)|~l1_pre_topc(X9)|~l1_pre_topc(X8))&((((m1_subset_1(esk1_3(X8,X9,X10),k1_zfmisc_1(u1_struct_0(X8)))|~r2_hidden(X10,u1_pre_topc(X9))|~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))|~m1_pre_topc(X9,X8)|~l1_pre_topc(X9)|~l1_pre_topc(X8))&(r2_hidden(esk1_3(X8,X9,X10),u1_pre_topc(X8))|~r2_hidden(X10,u1_pre_topc(X9))|~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))|~m1_pre_topc(X9,X8)|~l1_pre_topc(X9)|~l1_pre_topc(X8)))&(X10=k9_subset_1(u1_struct_0(X9),esk1_3(X8,X9,X10),k2_struct_0(X9))|~r2_hidden(X10,u1_pre_topc(X9))|~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))|~m1_pre_topc(X9,X8)|~l1_pre_topc(X9)|~l1_pre_topc(X8)))&(~m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X8)))|~r2_hidden(X12,u1_pre_topc(X8))|X10!=k9_subset_1(u1_struct_0(X9),X12,k2_struct_0(X9))|r2_hidden(X10,u1_pre_topc(X9))|~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))|~m1_pre_topc(X9,X8)|~l1_pre_topc(X9)|~l1_pre_topc(X8))))&((m1_subset_1(esk2_2(X8,X9),k1_zfmisc_1(u1_struct_0(X9)))|~r1_tarski(k2_struct_0(X9),k2_struct_0(X8))|m1_pre_topc(X9,X8)|~l1_pre_topc(X9)|~l1_pre_topc(X8))&((~r2_hidden(esk2_2(X8,X9),u1_pre_topc(X9))|(~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X8)))|~r2_hidden(X14,u1_pre_topc(X8))|esk2_2(X8,X9)!=k9_subset_1(u1_struct_0(X9),X14,k2_struct_0(X9)))|~r1_tarski(k2_struct_0(X9),k2_struct_0(X8))|m1_pre_topc(X9,X8)|~l1_pre_topc(X9)|~l1_pre_topc(X8))&(((m1_subset_1(esk3_2(X8,X9),k1_zfmisc_1(u1_struct_0(X8)))|r2_hidden(esk2_2(X8,X9),u1_pre_topc(X9))|~r1_tarski(k2_struct_0(X9),k2_struct_0(X8))|m1_pre_topc(X9,X8)|~l1_pre_topc(X9)|~l1_pre_topc(X8))&(r2_hidden(esk3_2(X8,X9),u1_pre_topc(X8))|r2_hidden(esk2_2(X8,X9),u1_pre_topc(X9))|~r1_tarski(k2_struct_0(X9),k2_struct_0(X8))|m1_pre_topc(X9,X8)|~l1_pre_topc(X9)|~l1_pre_topc(X8)))&(esk2_2(X8,X9)=k9_subset_1(u1_struct_0(X9),esk3_2(X8,X9),k2_struct_0(X9))|r2_hidden(esk2_2(X8,X9),u1_pre_topc(X9))|~r1_tarski(k2_struct_0(X9),k2_struct_0(X8))|m1_pre_topc(X9,X8)|~l1_pre_topc(X9)|~l1_pre_topc(X8)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_pre_topc])])])])])).
% 0.13/0.38  fof(c_0_10, plain, ![X16, X17]:((v1_pre_topc(k1_pre_topc(X16,X17))|(~l1_pre_topc(X16)|~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))))&(m1_pre_topc(k1_pre_topc(X16,X17),X16)|(~l1_pre_topc(X16)|~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_pre_topc])])])).
% 0.13/0.38  cnf(c_0_11, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.38  cnf(c_0_12, negated_conjecture, (esk7_0=esk8_0), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.38  cnf(c_0_13, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.38  cnf(c_0_14, negated_conjecture, (m1_pre_topc(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.38  cnf(c_0_15, negated_conjecture, (l1_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.38  fof(c_0_16, plain, ![X5, X6, X7]:((X7!=k1_pre_topc(X5,X6)|k2_struct_0(X7)=X6|(~v1_pre_topc(X7)|~m1_pre_topc(X7,X5))|~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))|~l1_pre_topc(X5))&(k2_struct_0(X7)!=X6|X7=k1_pre_topc(X5,X6)|(~v1_pre_topc(X7)|~m1_pre_topc(X7,X5))|~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))|~l1_pre_topc(X5))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_pre_topc])])])])).
% 0.13/0.38  cnf(c_0_17, plain, (r1_tarski(k2_struct_0(X1),k2_struct_0(X2))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X1)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.38  cnf(c_0_18, plain, (m1_pre_topc(k1_pre_topc(X1,X2),X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.38  cnf(c_0_19, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk6_0)))), inference(rw,[status(thm)],[c_0_11, c_0_12])).
% 0.13/0.38  cnf(c_0_20, negated_conjecture, (l1_pre_topc(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_15])])).
% 0.13/0.38  cnf(c_0_21, plain, (k2_struct_0(X1)=X3|X1!=k1_pre_topc(X2,X3)|~v1_pre_topc(X1)|~m1_pre_topc(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  cnf(c_0_22, plain, (v1_pre_topc(k1_pre_topc(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.38  fof(c_0_23, plain, ![X20, X21, X22, X23]:((~v2_compts_1(X22,X20)|(~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X21)))|(X23!=X22|v2_compts_1(X23,X21)))|~r1_tarski(X22,k2_struct_0(X21))|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X20)))|~m1_pre_topc(X21,X20)|~l1_pre_topc(X20))&((m1_subset_1(esk4_3(X20,X21,X22),k1_zfmisc_1(u1_struct_0(X21)))|v2_compts_1(X22,X20)|~r1_tarski(X22,k2_struct_0(X21))|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X20)))|~m1_pre_topc(X21,X20)|~l1_pre_topc(X20))&((esk4_3(X20,X21,X22)=X22|v2_compts_1(X22,X20)|~r1_tarski(X22,k2_struct_0(X21))|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X20)))|~m1_pre_topc(X21,X20)|~l1_pre_topc(X20))&(~v2_compts_1(esk4_3(X20,X21,X22),X21)|v2_compts_1(X22,X20)|~r1_tarski(X22,k2_struct_0(X21))|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X20)))|~m1_pre_topc(X21,X20)|~l1_pre_topc(X20))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_compts_1])])])])])).
% 0.13/0.38  cnf(c_0_24, plain, (r1_tarski(k2_struct_0(X1),k2_struct_0(X2))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[c_0_17, c_0_13])).
% 0.13/0.38  cnf(c_0_25, negated_conjecture, (m1_pre_topc(k1_pre_topc(esk6_0,esk7_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20])])).
% 0.13/0.38  cnf(c_0_26, plain, (k2_struct_0(k1_pre_topc(X1,X2))=X2|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_21]), c_0_22]), c_0_18])).
% 0.13/0.38  cnf(c_0_27, plain, (v2_compts_1(X3,X4)|~v2_compts_1(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))|X3!=X1|~r1_tarski(X1,k2_struct_0(X4))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_pre_topc(X4,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.38  cnf(c_0_28, negated_conjecture, (r1_tarski(k2_struct_0(k1_pre_topc(esk6_0,esk7_0)),k2_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_20])])).
% 0.13/0.38  cnf(c_0_29, negated_conjecture, (k2_struct_0(k1_pre_topc(esk6_0,esk7_0))=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_19]), c_0_20])])).
% 0.13/0.38  cnf(c_0_30, plain, (v2_compts_1(X1,X2)|~v2_compts_1(X1,X3)|~r1_tarski(X1,k2_struct_0(X2))|~m1_pre_topc(X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X3)))|~l1_pre_topc(X3)), inference(er,[status(thm)],[c_0_27])).
% 0.13/0.38  cnf(c_0_31, negated_conjecture, (r1_tarski(esk7_0,k2_struct_0(esk6_0))), inference(rw,[status(thm)],[c_0_28, c_0_29])).
% 0.13/0.38  cnf(c_0_32, negated_conjecture, (v2_compts_1(esk7_0,esk5_0)|v2_compts_1(esk8_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.38  cnf(c_0_33, plain, (v2_compts_1(X3,X1)|~v2_compts_1(esk4_3(X1,X2,X3),X2)|~r1_tarski(X3,k2_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.38  cnf(c_0_34, negated_conjecture, (~v2_compts_1(esk7_0,esk5_0)|~v2_compts_1(esk8_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.38  cnf(c_0_35, negated_conjecture, (v2_compts_1(esk7_0,esk6_0)|~v2_compts_1(esk7_0,X1)|~m1_pre_topc(esk6_0,X1)|~m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_19])])).
% 0.13/0.38  cnf(c_0_36, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.38  cnf(c_0_37, negated_conjecture, (v2_compts_1(esk7_0,esk6_0)|v2_compts_1(esk7_0,esk5_0)), inference(rw,[status(thm)],[c_0_32, c_0_12])).
% 0.13/0.38  cnf(c_0_38, negated_conjecture, (v2_compts_1(k2_struct_0(k1_pre_topc(esk6_0,esk7_0)),X1)|~v2_compts_1(esk4_3(X1,esk6_0,k2_struct_0(k1_pre_topc(esk6_0,esk7_0))),esk6_0)|~m1_pre_topc(esk6_0,X1)|~m1_subset_1(k2_struct_0(k1_pre_topc(esk6_0,esk7_0)),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_33, c_0_28])).
% 0.13/0.38  cnf(c_0_39, plain, (esk4_3(X1,X2,X3)=X3|v2_compts_1(X3,X1)|~r1_tarski(X3,k2_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.38  cnf(c_0_40, negated_conjecture, (~v2_compts_1(esk7_0,esk5_0)|~v2_compts_1(esk7_0,esk6_0)), inference(rw,[status(thm)],[c_0_34, c_0_12])).
% 0.13/0.38  cnf(c_0_41, negated_conjecture, (v2_compts_1(esk7_0,esk6_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_14]), c_0_36]), c_0_15])]), c_0_37])).
% 0.13/0.38  cnf(c_0_42, negated_conjecture, (v2_compts_1(k2_struct_0(k1_pre_topc(esk6_0,esk7_0)),esk5_0)|~v2_compts_1(esk4_3(esk5_0,esk6_0,k2_struct_0(k1_pre_topc(esk6_0,esk7_0))),esk6_0)|~m1_subset_1(k2_struct_0(k1_pre_topc(esk6_0,esk7_0)),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_14]), c_0_15])])).
% 0.13/0.38  cnf(c_0_43, negated_conjecture, (esk4_3(X1,esk6_0,esk7_0)=esk7_0|v2_compts_1(esk7_0,X1)|~m1_pre_topc(esk6_0,X1)|~m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_39, c_0_31])).
% 0.13/0.38  cnf(c_0_44, negated_conjecture, (~v2_compts_1(esk7_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_41])])).
% 0.13/0.38  cnf(c_0_45, negated_conjecture, (v2_compts_1(esk7_0,esk5_0)|~v2_compts_1(esk4_3(esk5_0,esk6_0,esk7_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_29]), c_0_29]), c_0_29]), c_0_36])])).
% 0.13/0.38  cnf(c_0_46, negated_conjecture, (esk4_3(esk5_0,esk6_0,esk7_0)=esk7_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_14]), c_0_36]), c_0_15])]), c_0_44])).
% 0.13/0.38  cnf(c_0_47, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_46]), c_0_41])]), c_0_44]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 48
% 0.13/0.38  # Proof object clause steps            : 35
% 0.13/0.38  # Proof object formula steps           : 13
% 0.13/0.38  # Proof object conjectures             : 27
% 0.13/0.38  # Proof object clause conjectures      : 24
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 15
% 0.13/0.38  # Proof object initial formulas used   : 6
% 0.13/0.38  # Proof object generating inferences   : 10
% 0.13/0.38  # Proof object simplifying inferences  : 40
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 6
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 26
% 0.13/0.38  # Removed in clause preprocessing      : 0
% 0.13/0.38  # Initial clauses in saturation        : 26
% 0.13/0.38  # Processed clauses                    : 63
% 0.13/0.38  # ...of these trivial                  : 0
% 0.13/0.38  # ...subsumed                          : 3
% 0.13/0.38  # ...remaining for further processing  : 60
% 0.13/0.38  # Other redundant clauses eliminated   : 4
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 1
% 0.13/0.38  # Backward-rewritten                   : 8
% 0.13/0.38  # Generated clauses                    : 77
% 0.13/0.38  # ...of the previous two non-trivial   : 71
% 0.13/0.38  # Contextual simplify-reflections      : 9
% 0.13/0.38  # Paramodulations                      : 73
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 4
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
% 0.13/0.38  # Current number of processed clauses  : 47
% 0.13/0.38  #    Positive orientable unit clauses  : 19
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 2
% 0.13/0.38  #    Non-unit-clauses                  : 26
% 0.13/0.38  # Current number of unprocessed clauses: 34
% 0.13/0.38  # ...number of literals in the above   : 176
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 9
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 419
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 24
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 12
% 0.13/0.38  # Unit Clause-clause subsumption calls : 60
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 5
% 0.13/0.38  # BW rewrite match successes           : 4
% 0.13/0.38  # Condensation attempts                : 63
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 5154
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.035 s
% 0.13/0.38  # System time              : 0.001 s
% 0.13/0.38  # Total time               : 0.036 s
% 0.13/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
