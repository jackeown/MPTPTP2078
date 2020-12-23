%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1312+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:04 EST 2020

% Result     : Theorem 5.02s
% Output     : CNFRefutation 5.02s
% Verified   : 
% Statistics : Number of formulae       :   39 (  57 expanded)
%              Number of clauses        :   22 (  24 expanded)
%              Number of leaves         :    8 (  14 expanded)
%              Depth                    :   10
%              Number of atoms          :   80 ( 143 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t31_tops_2,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
             => m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_tops_2)).

fof(t39_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
             => m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT016+2.ax',t39_pre_topc)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT005+2.ax',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT005+2.ax',d4_subset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT006+2.ax',t3_subset)).

fof(t79_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT004+2.ax',t79_zfmisc_1)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT016+2.ax',dt_l1_pre_topc)).

fof(t3_tops_2,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ! [X3] :
              ( r1_tarski(X3,X2)
             => m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_tops_2)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_pre_topc(X2,X1)
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
               => m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t31_tops_2])).

fof(c_0_9,plain,(
    ! [X6006,X6007,X6008] :
      ( ~ l1_pre_topc(X6006)
      | ~ m1_pre_topc(X6007,X6006)
      | ~ m1_subset_1(X6008,k1_zfmisc_1(u1_struct_0(X6007)))
      | m1_subset_1(X6008,k1_zfmisc_1(u1_struct_0(X6006))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t39_pre_topc])])])).

fof(c_0_10,negated_conjecture,
    ( l1_pre_topc(esk736_0)
    & m1_pre_topc(esk737_0,esk736_0)
    & m1_subset_1(esk738_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk737_0))))
    & ~ m1_subset_1(esk738_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk736_0)))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

fof(c_0_11,plain,(
    ! [X1583] : m1_subset_1(k2_subset_1(X1583),k1_zfmisc_1(X1583)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_12,plain,(
    ! [X1539] : k2_subset_1(X1539) = X1539 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

cnf(c_0_13,plain,
    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( m1_pre_topc(esk737_0,esk736_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( l1_pre_topc(esk736_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_18,plain,(
    ! [X2019,X2020] :
      ( ( ~ m1_subset_1(X2019,k1_zfmisc_1(X2020))
        | r1_tarski(X2019,X2020) )
      & ( ~ r1_tarski(X2019,X2020)
        | m1_subset_1(X2019,k1_zfmisc_1(X2020)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk736_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk737_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15])])).

cnf(c_0_20,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

fof(c_0_21,plain,(
    ! [X1431,X1432] :
      ( ~ r1_tarski(X1431,X1432)
      | r1_tarski(k1_zfmisc_1(X1431),k1_zfmisc_1(X1432)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_zfmisc_1])])).

cnf(c_0_22,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk737_0),k1_zfmisc_1(u1_struct_0(esk736_0))) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_24,plain,
    ( r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk737_0),u1_struct_0(esk736_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

fof(c_0_26,plain,(
    ! [X5917] :
      ( ~ l1_pre_topc(X5917)
      | l1_struct_0(X5917) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_27,plain,(
    ! [X7267,X7268,X7269] :
      ( ~ l1_struct_0(X7267)
      | ~ m1_subset_1(X7268,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X7267))))
      | ~ r1_tarski(X7269,X7268)
      | m1_subset_1(X7269,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X7267)))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_tops_2])])])).

cnf(c_0_28,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,negated_conjecture,
    ( r1_tarski(k1_zfmisc_1(u1_struct_0(esk737_0)),k1_zfmisc_1(u1_struct_0(esk736_0))) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_30,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,plain,
    ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(k1_zfmisc_1(u1_struct_0(esk737_0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk736_0)))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_33,negated_conjecture,
    ( l1_struct_0(esk736_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_15])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(esk738_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk737_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk736_0))))
    | ~ r1_tarski(X1,k1_zfmisc_1(u1_struct_0(esk737_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(esk738_0,k1_zfmisc_1(u1_struct_0(esk737_0))) ),
    inference(spm,[status(thm)],[c_0_22,c_0_34])).

cnf(c_0_37,negated_conjecture,
    ( ~ m1_subset_1(esk738_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk736_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_38,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37]),
    [proof]).
%------------------------------------------------------------------------------
