%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:09:14 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 336 expanded)
%              Number of clauses        :   51 ( 126 expanded)
%              Number of leaves         :    9 (  80 expanded)
%              Depth                    :   16
%              Number of atoms          :  327 (2490 expanded)
%              Number of equality atoms :   25 ( 508 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   28 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t44_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ( ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( r2_hidden(X3,X2)
                 => v4_pre_topc(X3,X1) ) )
           => v4_pre_topc(k6_setfam_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_pre_topc)).

fof(t46_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ? [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
              & ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( r2_hidden(X4,X3)
                  <=> ( v4_pre_topc(X4,X1)
                      & r1_tarski(X2,X4) ) ) )
              & k2_pre_topc(X1,X2) = k6_setfam_1(u1_struct_0(X1),X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_pre_topc)).

fof(t52_pre_topc,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( ( v4_pre_topc(X2,X1)
             => k2_pre_topc(X1,X2) = X2 )
            & ( ( v2_pre_topc(X1)
                & k2_pre_topc(X1,X2) = X2 )
             => v4_pre_topc(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

fof(t45_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( r2_hidden(X3,u1_struct_0(X1))
             => ( r2_hidden(X3,k2_pre_topc(X1,X2))
              <=> ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( ( v4_pre_topc(X4,X1)
                        & r1_tarski(X2,X4) )
                     => r2_hidden(X3,X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_pre_topc)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(dt_k2_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(t7_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( ! [X4] :
                ( m1_subset_1(X4,X1)
               => ( r2_hidden(X4,X2)
                 => r2_hidden(X4,X3) ) )
           => r1_tarski(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_subset_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t48_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(X2,k2_pre_topc(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

fof(c_0_9,plain,(
    ! [X16,X17] :
      ( ( m1_subset_1(esk2_2(X16,X17),k1_zfmisc_1(u1_struct_0(X16)))
        | v4_pre_topc(k6_setfam_1(u1_struct_0(X16),X17),X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X16))))
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16) )
      & ( r2_hidden(esk2_2(X16,X17),X17)
        | v4_pre_topc(k6_setfam_1(u1_struct_0(X16),X17),X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X16))))
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16) )
      & ( ~ v4_pre_topc(esk2_2(X16,X17),X16)
        | v4_pre_topc(k6_setfam_1(u1_struct_0(X16),X17),X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X16))))
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_pre_topc])])])])])).

fof(c_0_10,plain,(
    ! [X24,X25,X27] :
      ( ( m1_subset_1(esk4_2(X24,X25),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X24))))
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
        | ~ v2_pre_topc(X24)
        | ~ l1_pre_topc(X24) )
      & ( v4_pre_topc(X27,X24)
        | ~ r2_hidden(X27,esk4_2(X24,X25))
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X24)))
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
        | ~ v2_pre_topc(X24)
        | ~ l1_pre_topc(X24) )
      & ( r1_tarski(X25,X27)
        | ~ r2_hidden(X27,esk4_2(X24,X25))
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X24)))
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
        | ~ v2_pre_topc(X24)
        | ~ l1_pre_topc(X24) )
      & ( ~ v4_pre_topc(X27,X24)
        | ~ r1_tarski(X25,X27)
        | r2_hidden(X27,esk4_2(X24,X25))
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X24)))
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
        | ~ v2_pre_topc(X24)
        | ~ l1_pre_topc(X24) )
      & ( k2_pre_topc(X24,X25) = k6_setfam_1(u1_struct_0(X24),esk4_2(X24,X25))
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
        | ~ v2_pre_topc(X24)
        | ~ l1_pre_topc(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t46_pre_topc])])])])])).

cnf(c_0_11,plain,
    ( m1_subset_1(esk2_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v4_pre_topc(k6_setfam_1(u1_struct_0(X1),X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,plain,
    ( m1_subset_1(esk4_2(X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( ( v4_pre_topc(X2,X1)
               => k2_pre_topc(X1,X2) = X2 )
              & ( ( v2_pre_topc(X1)
                  & k2_pre_topc(X1,X2) = X2 )
               => v4_pre_topc(X2,X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t52_pre_topc])).

cnf(c_0_14,plain,
    ( v4_pre_topc(k6_setfam_1(u1_struct_0(X1),esk4_2(X1,X2)),X1)
    | m1_subset_1(esk2_2(X1,esk4_2(X1,X2)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_15,plain,
    ( k2_pre_topc(X1,X2) = k6_setfam_1(u1_struct_0(X1),esk4_2(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_16,negated_conjecture,
    ( l1_pre_topc(esk5_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))
    & ( v2_pre_topc(esk5_0)
      | v4_pre_topc(esk6_0,esk5_0) )
    & ( k2_pre_topc(esk5_0,esk6_0) = esk6_0
      | v4_pre_topc(esk6_0,esk5_0) )
    & ( ~ v4_pre_topc(esk6_0,esk5_0)
      | v4_pre_topc(esk6_0,esk5_0) )
    & ( v2_pre_topc(esk5_0)
      | k2_pre_topc(esk5_0,esk6_0) != esk6_0 )
    & ( k2_pre_topc(esk5_0,esk6_0) = esk6_0
      | k2_pre_topc(esk5_0,esk6_0) != esk6_0 )
    & ( ~ v4_pre_topc(esk6_0,esk5_0)
      | k2_pre_topc(esk5_0,esk6_0) != esk6_0 ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])])).

cnf(c_0_17,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | v4_pre_topc(k6_setfam_1(u1_struct_0(X1),X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_18,plain,
    ( v4_pre_topc(k2_pre_topc(X1,X2),X1)
    | m1_subset_1(esk2_2(X1,esk4_2(X1,X2)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( v4_pre_topc(X1,X2)
    | ~ r2_hidden(X1,esk4_2(X2,X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_22,plain,
    ( v4_pre_topc(k6_setfam_1(u1_struct_0(X1),esk4_2(X1,X2)),X1)
    | r2_hidden(esk2_2(X1,esk4_2(X1,X2)),esk4_2(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_17,c_0_12])).

cnf(c_0_23,negated_conjecture,
    ( v4_pre_topc(k2_pre_topc(esk5_0,esk6_0),esk5_0)
    | m1_subset_1(esk2_2(esk5_0,esk4_2(esk5_0,esk6_0)),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ v2_pre_topc(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])])).

cnf(c_0_24,negated_conjecture,
    ( v2_pre_topc(esk5_0)
    | k2_pre_topc(esk5_0,esk6_0) != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( v4_pre_topc(k6_setfam_1(u1_struct_0(X1),X2),X1)
    | ~ v4_pre_topc(esk2_2(X1,X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_26,negated_conjecture,
    ( v4_pre_topc(X1,esk5_0)
    | ~ v2_pre_topc(esk5_0)
    | ~ r2_hidden(X1,esk4_2(esk5_0,esk6_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_19]),c_0_20])])).

cnf(c_0_27,negated_conjecture,
    ( v2_pre_topc(esk5_0)
    | v4_pre_topc(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_28,negated_conjecture,
    ( v4_pre_topc(k6_setfam_1(u1_struct_0(esk5_0),esk4_2(esk5_0,esk6_0)),esk5_0)
    | r2_hidden(esk2_2(esk5_0,esk4_2(esk5_0,esk6_0)),esk4_2(esk5_0,esk6_0))
    | ~ v2_pre_topc(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_19]),c_0_20])])).

cnf(c_0_29,negated_conjecture,
    ( v4_pre_topc(k2_pre_topc(esk5_0,esk6_0),esk5_0)
    | m1_subset_1(esk2_2(esk5_0,esk4_2(esk5_0,esk6_0)),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | k2_pre_topc(esk5_0,esk6_0) != esk6_0 ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( k2_pre_topc(esk5_0,esk6_0) = esk6_0
    | v4_pre_topc(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_31,plain,
    ( v4_pre_topc(k2_pre_topc(X1,X2),X1)
    | ~ v4_pre_topc(esk2_2(X1,esk4_2(X1,X2)),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_15]),c_0_12])).

cnf(c_0_32,negated_conjecture,
    ( v4_pre_topc(esk6_0,esk5_0)
    | v4_pre_topc(X1,esk5_0)
    | ~ r2_hidden(X1,esk4_2(esk5_0,esk6_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( v4_pre_topc(k6_setfam_1(u1_struct_0(esk5_0),esk4_2(esk5_0,esk6_0)),esk5_0)
    | v4_pre_topc(esk6_0,esk5_0)
    | r2_hidden(esk2_2(esk5_0,esk4_2(esk5_0,esk6_0)),esk4_2(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( v4_pre_topc(esk6_0,esk5_0)
    | m1_subset_1(esk2_2(esk5_0,esk4_2(esk5_0,esk6_0)),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_35,negated_conjecture,
    ( v4_pre_topc(esk6_0,esk5_0)
    | ~ v4_pre_topc(esk2_2(esk5_0,esk4_2(esk5_0,esk6_0)),esk5_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_30]),c_0_20]),c_0_19])]),c_0_27])).

fof(c_0_36,plain,(
    ! [X19,X20,X21,X22] :
      ( ( ~ r2_hidden(X21,k2_pre_topc(X19,X20))
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ v4_pre_topc(X22,X19)
        | ~ r1_tarski(X20,X22)
        | r2_hidden(X21,X22)
        | ~ r2_hidden(X21,u1_struct_0(X19))
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ l1_pre_topc(X19) )
      & ( m1_subset_1(esk3_3(X19,X20,X21),k1_zfmisc_1(u1_struct_0(X19)))
        | r2_hidden(X21,k2_pre_topc(X19,X20))
        | ~ r2_hidden(X21,u1_struct_0(X19))
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ l1_pre_topc(X19) )
      & ( v4_pre_topc(esk3_3(X19,X20,X21),X19)
        | r2_hidden(X21,k2_pre_topc(X19,X20))
        | ~ r2_hidden(X21,u1_struct_0(X19))
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ l1_pre_topc(X19) )
      & ( r1_tarski(X20,esk3_3(X19,X20,X21))
        | r2_hidden(X21,k2_pre_topc(X19,X20))
        | ~ r2_hidden(X21,u1_struct_0(X19))
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ l1_pre_topc(X19) )
      & ( ~ r2_hidden(X21,esk3_3(X19,X20,X21))
        | r2_hidden(X21,k2_pre_topc(X19,X20))
        | ~ r2_hidden(X21,u1_struct_0(X19))
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ l1_pre_topc(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_pre_topc])])])])])).

cnf(c_0_37,negated_conjecture,
    ( v4_pre_topc(k6_setfam_1(u1_struct_0(esk5_0),esk4_2(esk5_0,esk6_0)),esk5_0)
    | v4_pre_topc(esk6_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_35])).

fof(c_0_38,plain,(
    ! [X7,X8,X9] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(X7))
      | ~ r2_hidden(X9,X8)
      | r2_hidden(X9,X7) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

fof(c_0_39,plain,(
    ! [X14,X15] :
      ( ~ l1_pre_topc(X14)
      | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
      | m1_subset_1(k2_pre_topc(X14,X15),k1_zfmisc_1(u1_struct_0(X14))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).

fof(c_0_40,plain,(
    ! [X10,X11,X12] :
      ( ( m1_subset_1(esk1_3(X10,X11,X12),X10)
        | r1_tarski(X11,X12)
        | ~ m1_subset_1(X12,k1_zfmisc_1(X10))
        | ~ m1_subset_1(X11,k1_zfmisc_1(X10)) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X11)
        | r1_tarski(X11,X12)
        | ~ m1_subset_1(X12,k1_zfmisc_1(X10))
        | ~ m1_subset_1(X11,k1_zfmisc_1(X10)) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | r1_tarski(X11,X12)
        | ~ m1_subset_1(X12,k1_zfmisc_1(X10))
        | ~ m1_subset_1(X11,k1_zfmisc_1(X10)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_subset_1])])])])])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,k2_pre_topc(X2,X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v4_pre_topc(X4,X2)
    | ~ r1_tarski(X3,X4)
    | ~ r2_hidden(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_42,negated_conjecture,
    ( v4_pre_topc(k2_pre_topc(esk5_0,esk6_0),esk5_0)
    | v4_pre_topc(esk6_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_15]),c_0_20]),c_0_19])]),c_0_27])).

fof(c_0_43,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_44,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_45,plain,
    ( m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_46,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r1_tarski(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | ~ v4_pre_topc(esk6_0,esk5_0)
    | ~ r2_hidden(X1,k2_pre_topc(esk5_0,X2))
    | ~ r2_hidden(X1,u1_struct_0(esk5_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ r1_tarski(X2,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_19]),c_0_20])])).

cnf(c_0_48,negated_conjecture,
    ( v4_pre_topc(esk6_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_30])).

cnf(c_0_49,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_50,plain,
    ( r2_hidden(X1,u1_struct_0(X2))
    | ~ l1_pre_topc(X2)
    | ~ r2_hidden(X1,k2_pre_topc(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(esk1_3(u1_struct_0(esk5_0),X1,esk6_0),X1)
    | r1_tarski(X1,esk6_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_46,c_0_19])).

fof(c_0_52,plain,(
    ! [X28,X29] :
      ( ~ l1_pre_topc(X28)
      | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))
      | r1_tarski(X29,k2_pre_topc(X28,X29)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_pre_topc])])])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X1,k2_pre_topc(esk5_0,X2))
    | ~ r2_hidden(X1,u1_struct_0(esk5_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ r1_tarski(X2,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_48])])).

cnf(c_0_54,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_49])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(X1,u1_struct_0(esk5_0))
    | ~ r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_19]),c_0_20])])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk1_3(u1_struct_0(esk5_0),k2_pre_topc(esk5_0,X1),esk6_0),k2_pre_topc(esk5_0,X1))
    | r1_tarski(k2_pre_topc(esk5_0,X1),esk6_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_45]),c_0_20])])).

cnf(c_0_57,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_58,plain,
    ( r1_tarski(X2,k2_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_19]),c_0_54])]),c_0_55])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(esk1_3(u1_struct_0(esk5_0),k2_pre_topc(esk5_0,esk6_0),esk6_0),k2_pre_topc(esk5_0,esk6_0))
    | r1_tarski(k2_pre_topc(esk5_0,esk6_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_19])).

cnf(c_0_61,plain,
    ( k2_pre_topc(X1,X2) = X2
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k2_pre_topc(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_62,plain,
    ( r1_tarski(X2,X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(esk1_3(u1_struct_0(esk5_0),k2_pre_topc(esk5_0,esk6_0),esk6_0),esk6_0)
    | r1_tarski(k2_pre_topc(esk5_0,esk6_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_64,negated_conjecture,
    ( ~ v4_pre_topc(esk6_0,esk5_0)
    | k2_pre_topc(esk5_0,esk6_0) != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_65,negated_conjecture,
    ( k2_pre_topc(esk5_0,esk6_0) = esk6_0
    | ~ r1_tarski(k2_pre_topc(esk5_0,esk6_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_19]),c_0_20])])).

cnf(c_0_66,negated_conjecture,
    ( r1_tarski(k2_pre_topc(esk5_0,esk6_0),esk6_0)
    | ~ m1_subset_1(k2_pre_topc(esk5_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_19])])).

cnf(c_0_67,negated_conjecture,
    ( k2_pre_topc(esk5_0,esk6_0) != esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_48])])).

cnf(c_0_68,negated_conjecture,
    ( ~ m1_subset_1(k2_pre_topc(esk5_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67])).

cnf(c_0_69,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_45]),c_0_20]),c_0_19])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:02:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S05AN
% 0.20/0.40  # and selection function PSelectComplexExceptUniqMaxPosHorn.
% 0.20/0.40  #
% 0.20/0.40  # Preprocessing time       : 0.029 s
% 0.20/0.40  # Presaturation interreduction done
% 0.20/0.40  
% 0.20/0.40  # Proof found!
% 0.20/0.40  # SZS status Theorem
% 0.20/0.40  # SZS output start CNFRefutation
% 0.20/0.40  fof(t44_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X3,X2)=>v4_pre_topc(X3,X1)))=>v4_pre_topc(k6_setfam_1(u1_struct_0(X1),X2),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_pre_topc)).
% 0.20/0.40  fof(t46_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>?[X3]:((m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))&![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X4,X3)<=>(v4_pre_topc(X4,X1)&r1_tarski(X2,X4)))))&k2_pre_topc(X1,X2)=k6_setfam_1(u1_struct_0(X1),X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_pre_topc)).
% 0.20/0.40  fof(t52_pre_topc, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v4_pre_topc(X2,X1)=>k2_pre_topc(X1,X2)=X2)&((v2_pre_topc(X1)&k2_pre_topc(X1,X2)=X2)=>v4_pre_topc(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 0.20/0.40  fof(t45_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(r2_hidden(X3,u1_struct_0(X1))=>(r2_hidden(X3,k2_pre_topc(X1,X2))<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>((v4_pre_topc(X4,X1)&r1_tarski(X2,X4))=>r2_hidden(X3,X4))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_pre_topc)).
% 0.20/0.40  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 0.20/0.40  fof(dt_k2_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 0.20/0.40  fof(t7_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(![X4]:(m1_subset_1(X4,X1)=>(r2_hidden(X4,X2)=>r2_hidden(X4,X3)))=>r1_tarski(X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_subset_1)).
% 0.20/0.40  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.40  fof(t48_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(X2,k2_pre_topc(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_pre_topc)).
% 0.20/0.40  fof(c_0_9, plain, ![X16, X17]:((m1_subset_1(esk2_2(X16,X17),k1_zfmisc_1(u1_struct_0(X16)))|v4_pre_topc(k6_setfam_1(u1_struct_0(X16),X17),X16)|~m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X16))))|(~v2_pre_topc(X16)|~l1_pre_topc(X16)))&((r2_hidden(esk2_2(X16,X17),X17)|v4_pre_topc(k6_setfam_1(u1_struct_0(X16),X17),X16)|~m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X16))))|(~v2_pre_topc(X16)|~l1_pre_topc(X16)))&(~v4_pre_topc(esk2_2(X16,X17),X16)|v4_pre_topc(k6_setfam_1(u1_struct_0(X16),X17),X16)|~m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X16))))|(~v2_pre_topc(X16)|~l1_pre_topc(X16))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_pre_topc])])])])])).
% 0.20/0.40  fof(c_0_10, plain, ![X24, X25, X27]:(((m1_subset_1(esk4_2(X24,X25),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X24))))|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))|(~v2_pre_topc(X24)|~l1_pre_topc(X24)))&(((v4_pre_topc(X27,X24)|~r2_hidden(X27,esk4_2(X24,X25))|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X24)))|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))|(~v2_pre_topc(X24)|~l1_pre_topc(X24)))&(r1_tarski(X25,X27)|~r2_hidden(X27,esk4_2(X24,X25))|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X24)))|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))|(~v2_pre_topc(X24)|~l1_pre_topc(X24))))&(~v4_pre_topc(X27,X24)|~r1_tarski(X25,X27)|r2_hidden(X27,esk4_2(X24,X25))|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X24)))|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))|(~v2_pre_topc(X24)|~l1_pre_topc(X24)))))&(k2_pre_topc(X24,X25)=k6_setfam_1(u1_struct_0(X24),esk4_2(X24,X25))|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))|(~v2_pre_topc(X24)|~l1_pre_topc(X24)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t46_pre_topc])])])])])).
% 0.20/0.40  cnf(c_0_11, plain, (m1_subset_1(esk2_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|v4_pre_topc(k6_setfam_1(u1_struct_0(X1),X2),X1)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.40  cnf(c_0_12, plain, (m1_subset_1(esk4_2(X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.40  fof(c_0_13, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v4_pre_topc(X2,X1)=>k2_pre_topc(X1,X2)=X2)&((v2_pre_topc(X1)&k2_pre_topc(X1,X2)=X2)=>v4_pre_topc(X2,X1)))))), inference(assume_negation,[status(cth)],[t52_pre_topc])).
% 0.20/0.40  cnf(c_0_14, plain, (v4_pre_topc(k6_setfam_1(u1_struct_0(X1),esk4_2(X1,X2)),X1)|m1_subset_1(esk2_2(X1,esk4_2(X1,X2)),k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.20/0.40  cnf(c_0_15, plain, (k2_pre_topc(X1,X2)=k6_setfam_1(u1_struct_0(X1),esk4_2(X1,X2))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.40  fof(c_0_16, negated_conjecture, (l1_pre_topc(esk5_0)&(m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))&((((v2_pre_topc(esk5_0)|v4_pre_topc(esk6_0,esk5_0))&(k2_pre_topc(esk5_0,esk6_0)=esk6_0|v4_pre_topc(esk6_0,esk5_0)))&(~v4_pre_topc(esk6_0,esk5_0)|v4_pre_topc(esk6_0,esk5_0)))&(((v2_pre_topc(esk5_0)|k2_pre_topc(esk5_0,esk6_0)!=esk6_0)&(k2_pre_topc(esk5_0,esk6_0)=esk6_0|k2_pre_topc(esk5_0,esk6_0)!=esk6_0))&(~v4_pre_topc(esk6_0,esk5_0)|k2_pre_topc(esk5_0,esk6_0)!=esk6_0))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])])).
% 0.20/0.40  cnf(c_0_17, plain, (r2_hidden(esk2_2(X1,X2),X2)|v4_pre_topc(k6_setfam_1(u1_struct_0(X1),X2),X1)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.40  cnf(c_0_18, plain, (v4_pre_topc(k2_pre_topc(X1,X2),X1)|m1_subset_1(esk2_2(X1,esk4_2(X1,X2)),k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.20/0.40  cnf(c_0_19, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.40  cnf(c_0_20, negated_conjecture, (l1_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.40  cnf(c_0_21, plain, (v4_pre_topc(X1,X2)|~r2_hidden(X1,esk4_2(X2,X3))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.40  cnf(c_0_22, plain, (v4_pre_topc(k6_setfam_1(u1_struct_0(X1),esk4_2(X1,X2)),X1)|r2_hidden(esk2_2(X1,esk4_2(X1,X2)),esk4_2(X1,X2))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_17, c_0_12])).
% 0.20/0.40  cnf(c_0_23, negated_conjecture, (v4_pre_topc(k2_pre_topc(esk5_0,esk6_0),esk5_0)|m1_subset_1(esk2_2(esk5_0,esk4_2(esk5_0,esk6_0)),k1_zfmisc_1(u1_struct_0(esk5_0)))|~v2_pre_topc(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20])])).
% 0.20/0.40  cnf(c_0_24, negated_conjecture, (v2_pre_topc(esk5_0)|k2_pre_topc(esk5_0,esk6_0)!=esk6_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.40  cnf(c_0_25, plain, (v4_pre_topc(k6_setfam_1(u1_struct_0(X1),X2),X1)|~v4_pre_topc(esk2_2(X1,X2),X1)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.40  cnf(c_0_26, negated_conjecture, (v4_pre_topc(X1,esk5_0)|~v2_pre_topc(esk5_0)|~r2_hidden(X1,esk4_2(esk5_0,esk6_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_19]), c_0_20])])).
% 0.20/0.40  cnf(c_0_27, negated_conjecture, (v2_pre_topc(esk5_0)|v4_pre_topc(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.40  cnf(c_0_28, negated_conjecture, (v4_pre_topc(k6_setfam_1(u1_struct_0(esk5_0),esk4_2(esk5_0,esk6_0)),esk5_0)|r2_hidden(esk2_2(esk5_0,esk4_2(esk5_0,esk6_0)),esk4_2(esk5_0,esk6_0))|~v2_pre_topc(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_19]), c_0_20])])).
% 0.20/0.40  cnf(c_0_29, negated_conjecture, (v4_pre_topc(k2_pre_topc(esk5_0,esk6_0),esk5_0)|m1_subset_1(esk2_2(esk5_0,esk4_2(esk5_0,esk6_0)),k1_zfmisc_1(u1_struct_0(esk5_0)))|k2_pre_topc(esk5_0,esk6_0)!=esk6_0), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.20/0.40  cnf(c_0_30, negated_conjecture, (k2_pre_topc(esk5_0,esk6_0)=esk6_0|v4_pre_topc(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.40  cnf(c_0_31, plain, (v4_pre_topc(k2_pre_topc(X1,X2),X1)|~v4_pre_topc(esk2_2(X1,esk4_2(X1,X2)),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_15]), c_0_12])).
% 0.20/0.40  cnf(c_0_32, negated_conjecture, (v4_pre_topc(esk6_0,esk5_0)|v4_pre_topc(X1,esk5_0)|~r2_hidden(X1,esk4_2(esk5_0,esk6_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.20/0.40  cnf(c_0_33, negated_conjecture, (v4_pre_topc(k6_setfam_1(u1_struct_0(esk5_0),esk4_2(esk5_0,esk6_0)),esk5_0)|v4_pre_topc(esk6_0,esk5_0)|r2_hidden(esk2_2(esk5_0,esk4_2(esk5_0,esk6_0)),esk4_2(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_28, c_0_27])).
% 0.20/0.40  cnf(c_0_34, negated_conjecture, (v4_pre_topc(esk6_0,esk5_0)|m1_subset_1(esk2_2(esk5_0,esk4_2(esk5_0,esk6_0)),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.20/0.40  cnf(c_0_35, negated_conjecture, (v4_pre_topc(esk6_0,esk5_0)|~v4_pre_topc(esk2_2(esk5_0,esk4_2(esk5_0,esk6_0)),esk5_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_30]), c_0_20]), c_0_19])]), c_0_27])).
% 0.20/0.40  fof(c_0_36, plain, ![X19, X20, X21, X22]:((~r2_hidden(X21,k2_pre_topc(X19,X20))|(~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X19)))|(~v4_pre_topc(X22,X19)|~r1_tarski(X20,X22)|r2_hidden(X21,X22)))|~r2_hidden(X21,u1_struct_0(X19))|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|~l1_pre_topc(X19))&((m1_subset_1(esk3_3(X19,X20,X21),k1_zfmisc_1(u1_struct_0(X19)))|r2_hidden(X21,k2_pre_topc(X19,X20))|~r2_hidden(X21,u1_struct_0(X19))|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|~l1_pre_topc(X19))&(((v4_pre_topc(esk3_3(X19,X20,X21),X19)|r2_hidden(X21,k2_pre_topc(X19,X20))|~r2_hidden(X21,u1_struct_0(X19))|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|~l1_pre_topc(X19))&(r1_tarski(X20,esk3_3(X19,X20,X21))|r2_hidden(X21,k2_pre_topc(X19,X20))|~r2_hidden(X21,u1_struct_0(X19))|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|~l1_pre_topc(X19)))&(~r2_hidden(X21,esk3_3(X19,X20,X21))|r2_hidden(X21,k2_pre_topc(X19,X20))|~r2_hidden(X21,u1_struct_0(X19))|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|~l1_pre_topc(X19))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_pre_topc])])])])])).
% 0.20/0.40  cnf(c_0_37, negated_conjecture, (v4_pre_topc(k6_setfam_1(u1_struct_0(esk5_0),esk4_2(esk5_0,esk6_0)),esk5_0)|v4_pre_topc(esk6_0,esk5_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34]), c_0_35])).
% 0.20/0.40  fof(c_0_38, plain, ![X7, X8, X9]:(~m1_subset_1(X8,k1_zfmisc_1(X7))|(~r2_hidden(X9,X8)|r2_hidden(X9,X7))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.20/0.40  fof(c_0_39, plain, ![X14, X15]:(~l1_pre_topc(X14)|~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))|m1_subset_1(k2_pre_topc(X14,X15),k1_zfmisc_1(u1_struct_0(X14)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).
% 0.20/0.40  fof(c_0_40, plain, ![X10, X11, X12]:((m1_subset_1(esk1_3(X10,X11,X12),X10)|r1_tarski(X11,X12)|~m1_subset_1(X12,k1_zfmisc_1(X10))|~m1_subset_1(X11,k1_zfmisc_1(X10)))&((r2_hidden(esk1_3(X10,X11,X12),X11)|r1_tarski(X11,X12)|~m1_subset_1(X12,k1_zfmisc_1(X10))|~m1_subset_1(X11,k1_zfmisc_1(X10)))&(~r2_hidden(esk1_3(X10,X11,X12),X12)|r1_tarski(X11,X12)|~m1_subset_1(X12,k1_zfmisc_1(X10))|~m1_subset_1(X11,k1_zfmisc_1(X10))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_subset_1])])])])])).
% 0.20/0.40  cnf(c_0_41, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,k2_pre_topc(X2,X3))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|~v4_pre_topc(X4,X2)|~r1_tarski(X3,X4)|~r2_hidden(X1,u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.40  cnf(c_0_42, negated_conjecture, (v4_pre_topc(k2_pre_topc(esk5_0,esk6_0),esk5_0)|v4_pre_topc(esk6_0,esk5_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_15]), c_0_20]), c_0_19])]), c_0_27])).
% 0.20/0.40  fof(c_0_43, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.40  cnf(c_0_44, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.40  cnf(c_0_45, plain, (m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.40  cnf(c_0_46, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r1_tarski(X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.40  cnf(c_0_47, negated_conjecture, (r2_hidden(X1,esk6_0)|~v4_pre_topc(esk6_0,esk5_0)|~r2_hidden(X1,k2_pre_topc(esk5_0,X2))|~r2_hidden(X1,u1_struct_0(esk5_0))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk5_0)))|~r1_tarski(X2,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_19]), c_0_20])])).
% 0.20/0.40  cnf(c_0_48, negated_conjecture, (v4_pre_topc(esk6_0,esk5_0)), inference(spm,[status(thm)],[c_0_42, c_0_30])).
% 0.20/0.40  cnf(c_0_49, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.40  cnf(c_0_50, plain, (r2_hidden(X1,u1_struct_0(X2))|~l1_pre_topc(X2)|~r2_hidden(X1,k2_pre_topc(X2,X3))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.20/0.40  cnf(c_0_51, negated_conjecture, (r2_hidden(esk1_3(u1_struct_0(esk5_0),X1,esk6_0),X1)|r1_tarski(X1,esk6_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(spm,[status(thm)],[c_0_46, c_0_19])).
% 0.20/0.40  fof(c_0_52, plain, ![X28, X29]:(~l1_pre_topc(X28)|(~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))|r1_tarski(X29,k2_pre_topc(X28,X29)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_pre_topc])])])).
% 0.20/0.40  cnf(c_0_53, negated_conjecture, (r2_hidden(X1,esk6_0)|~r2_hidden(X1,k2_pre_topc(esk5_0,X2))|~r2_hidden(X1,u1_struct_0(esk5_0))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk5_0)))|~r1_tarski(X2,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_48])])).
% 0.20/0.40  cnf(c_0_54, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_49])).
% 0.20/0.40  cnf(c_0_55, negated_conjecture, (r2_hidden(X1,u1_struct_0(esk5_0))|~r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_19]), c_0_20])])).
% 0.20/0.40  cnf(c_0_56, negated_conjecture, (r2_hidden(esk1_3(u1_struct_0(esk5_0),k2_pre_topc(esk5_0,X1),esk6_0),k2_pre_topc(esk5_0,X1))|r1_tarski(k2_pre_topc(esk5_0,X1),esk6_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_45]), c_0_20])])).
% 0.20/0.40  cnf(c_0_57, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.40  cnf(c_0_58, plain, (r1_tarski(X2,k2_pre_topc(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.20/0.40  cnf(c_0_59, negated_conjecture, (r2_hidden(X1,esk6_0)|~r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_19]), c_0_54])]), c_0_55])).
% 0.20/0.40  cnf(c_0_60, negated_conjecture, (r2_hidden(esk1_3(u1_struct_0(esk5_0),k2_pre_topc(esk5_0,esk6_0),esk6_0),k2_pre_topc(esk5_0,esk6_0))|r1_tarski(k2_pre_topc(esk5_0,esk6_0),esk6_0)), inference(spm,[status(thm)],[c_0_56, c_0_19])).
% 0.20/0.40  cnf(c_0_61, plain, (k2_pre_topc(X1,X2)=X2|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(k2_pre_topc(X1,X2),X2)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.20/0.40  cnf(c_0_62, plain, (r1_tarski(X2,X3)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.40  cnf(c_0_63, negated_conjecture, (r2_hidden(esk1_3(u1_struct_0(esk5_0),k2_pre_topc(esk5_0,esk6_0),esk6_0),esk6_0)|r1_tarski(k2_pre_topc(esk5_0,esk6_0),esk6_0)), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.20/0.40  cnf(c_0_64, negated_conjecture, (~v4_pre_topc(esk6_0,esk5_0)|k2_pre_topc(esk5_0,esk6_0)!=esk6_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.40  cnf(c_0_65, negated_conjecture, (k2_pre_topc(esk5_0,esk6_0)=esk6_0|~r1_tarski(k2_pre_topc(esk5_0,esk6_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_19]), c_0_20])])).
% 0.20/0.40  cnf(c_0_66, negated_conjecture, (r1_tarski(k2_pre_topc(esk5_0,esk6_0),esk6_0)|~m1_subset_1(k2_pre_topc(esk5_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_19])])).
% 0.20/0.40  cnf(c_0_67, negated_conjecture, (k2_pre_topc(esk5_0,esk6_0)!=esk6_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_64, c_0_48])])).
% 0.20/0.40  cnf(c_0_68, negated_conjecture, (~m1_subset_1(k2_pre_topc(esk5_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_67])).
% 0.20/0.40  cnf(c_0_69, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_45]), c_0_20]), c_0_19])]), ['proof']).
% 0.20/0.40  # SZS output end CNFRefutation
% 0.20/0.40  # Proof object total steps             : 70
% 0.20/0.40  # Proof object clause steps            : 51
% 0.20/0.40  # Proof object formula steps           : 19
% 0.20/0.40  # Proof object conjectures             : 33
% 0.20/0.40  # Proof object clause conjectures      : 30
% 0.20/0.40  # Proof object formula conjectures     : 3
% 0.20/0.40  # Proof object initial clauses used    : 20
% 0.20/0.40  # Proof object initial formulas used   : 9
% 0.20/0.40  # Proof object generating inferences   : 28
% 0.20/0.40  # Proof object simplifying inferences  : 39
% 0.20/0.40  # Training examples: 0 positive, 0 negative
% 0.20/0.40  # Parsed axioms                        : 9
% 0.20/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.40  # Initial clauses                      : 30
% 0.20/0.40  # Removed in clause preprocessing      : 2
% 0.20/0.40  # Initial clauses in saturation        : 28
% 0.20/0.40  # Processed clauses                    : 223
% 0.20/0.40  # ...of these trivial                  : 0
% 0.20/0.40  # ...subsumed                          : 48
% 0.20/0.40  # ...remaining for further processing  : 175
% 0.20/0.40  # Other redundant clauses eliminated   : 2
% 0.20/0.40  # Clauses deleted for lack of memory   : 0
% 0.20/0.40  # Backward-subsumed                    : 18
% 0.20/0.40  # Backward-rewritten                   : 19
% 0.20/0.40  # Generated clauses                    : 340
% 0.20/0.40  # ...of the previous two non-trivial   : 302
% 0.20/0.40  # Contextual simplify-reflections      : 18
% 0.20/0.40  # Paramodulations                      : 334
% 0.20/0.40  # Factorizations                       : 4
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
% 0.20/0.40  # Current number of processed clauses  : 109
% 0.20/0.40  #    Positive orientable unit clauses  : 4
% 0.20/0.40  #    Positive unorientable unit clauses: 0
% 0.20/0.40  #    Negative unit clauses             : 2
% 0.20/0.40  #    Non-unit-clauses                  : 103
% 0.20/0.40  # Current number of unprocessed clauses: 132
% 0.20/0.40  # ...number of literals in the above   : 596
% 0.20/0.40  # Current number of archived formulas  : 0
% 0.20/0.40  # Current number of archived clauses   : 64
% 0.20/0.40  # Clause-clause subsumption calls (NU) : 1668
% 0.20/0.40  # Rec. Clause-clause subsumption calls : 758
% 0.20/0.40  # Non-unit clause-clause subsumptions  : 72
% 0.20/0.40  # Unit Clause-clause subsumption calls : 72
% 0.20/0.40  # Rewrite failures with RHS unbound    : 0
% 0.20/0.40  # BW rewrite match attempts            : 1
% 0.20/0.40  # BW rewrite match successes           : 1
% 0.20/0.40  # Condensation attempts                : 0
% 0.20/0.40  # Condensation successes               : 0
% 0.20/0.40  # Termbank termtop insertions          : 14311
% 0.20/0.40  
% 0.20/0.40  # -------------------------------------------------
% 0.20/0.40  # User time                : 0.049 s
% 0.20/0.40  # System time              : 0.005 s
% 0.20/0.40  # Total time               : 0.054 s
% 0.20/0.40  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
