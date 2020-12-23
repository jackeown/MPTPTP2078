%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1225+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:56 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   35 ( 109 expanded)
%              Number of clauses        :   22 (  39 expanded)
%              Number of leaves         :    6 (  26 expanded)
%              Depth                    :    8
%              Number of atoms          :  101 ( 481 expanded)
%              Number of equality atoms :   19 (  87 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    9 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t34_tops_1,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( v4_pre_topc(X2,X1)
                  & v4_pre_topc(X3,X1) )
               => k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X2,X3)) = k9_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k2_pre_topc(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_tops_1)).

fof(t51_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => r1_tarski(k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X2,X3)),k9_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k2_pre_topc(X1,X3))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_pre_topc)).

fof(t52_pre_topc,axiom,(
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

fof(t48_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(X2,k2_pre_topc(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(dt_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( ( v4_pre_topc(X2,X1)
                    & v4_pre_topc(X3,X1) )
                 => k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X2,X3)) = k9_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k2_pre_topc(X1,X3)) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t34_tops_1])).

fof(c_0_7,plain,(
    ! [X14,X15,X16] :
      ( ~ l1_pre_topc(X14)
      | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
      | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))
      | r1_tarski(k2_pre_topc(X14,k9_subset_1(u1_struct_0(X14),X15,X16)),k9_subset_1(u1_struct_0(X14),k2_pre_topc(X14,X15),k2_pre_topc(X14,X16))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t51_pre_topc])])])).

fof(c_0_8,negated_conjecture,
    ( l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & v4_pre_topc(esk2_0,esk1_0)
    & v4_pre_topc(esk3_0,esk1_0)
    & k2_pre_topc(esk1_0,k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)) != k9_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),k2_pre_topc(esk1_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

fof(c_0_9,plain,(
    ! [X17,X18] :
      ( ( ~ v4_pre_topc(X18,X17)
        | k2_pre_topc(X17,X18) = X18
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ l1_pre_topc(X17) )
      & ( ~ v2_pre_topc(X17)
        | k2_pre_topc(X17,X18) != X18
        | v4_pre_topc(X18,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ l1_pre_topc(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).

fof(c_0_10,plain,(
    ! [X12,X13] :
      ( ~ l1_pre_topc(X12)
      | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
      | r1_tarski(X13,k2_pre_topc(X12,X13)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_pre_topc])])])).

cnf(c_0_11,plain,
    ( r1_tarski(k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X2,X3)),k9_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k2_pre_topc(X1,X3)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( k2_pre_topc(X2,X1) = X1
    | ~ v4_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( v4_pre_topc(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_16,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_17,plain,
    ( r1_tarski(X2,k2_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,negated_conjecture,
    ( r1_tarski(k2_pre_topc(esk1_0,k9_subset_1(u1_struct_0(esk1_0),X1,X2)),k9_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,X1),k2_pre_topc(esk1_0,X2)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( k2_pre_topc(esk1_0,esk3_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_12]),c_0_15])])).

cnf(c_0_20,negated_conjecture,
    ( v4_pre_topc(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_22,negated_conjecture,
    ( k2_pre_topc(esk1_0,k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)) != k9_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),k2_pre_topc(esk1_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_23,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( r1_tarski(X1,k2_pre_topc(esk1_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_17,c_0_12])).

cnf(c_0_25,negated_conjecture,
    ( r1_tarski(k2_pre_topc(esk1_0,k9_subset_1(u1_struct_0(esk1_0),X1,esk3_0)),k9_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,X1),esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_15])])).

cnf(c_0_26,negated_conjecture,
    ( k2_pre_topc(esk1_0,esk2_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_20]),c_0_12]),c_0_21])])).

cnf(c_0_27,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk3_0) != k2_pre_topc(esk1_0,k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)) ),
    inference(rw,[status(thm)],[c_0_22,c_0_19])).

cnf(c_0_28,negated_conjecture,
    ( k2_pre_topc(esk1_0,X1) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(k2_pre_topc(esk1_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( r1_tarski(k2_pre_topc(esk1_0,k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)),k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_21])])).

cnf(c_0_30,negated_conjecture,
    ( k2_pre_topc(esk1_0,k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)) != k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_27,c_0_26])).

fof(c_0_31,plain,(
    ! [X6,X7,X8] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(X6))
      | m1_subset_1(k9_subset_1(X6,X7,X8),k1_zfmisc_1(X6)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).

cnf(c_0_32,negated_conjecture,
    ( ~ m1_subset_1(k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])).

cnf(c_0_33,plain,
    ( m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_34,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_15])]),
    [proof]).

%------------------------------------------------------------------------------
