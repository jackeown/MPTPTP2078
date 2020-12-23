%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:14:30 EST 2020

% Result     : Theorem 0.17s
% Output     : CNFRefutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :   93 (1157 expanded)
%              Number of clauses        :   70 ( 423 expanded)
%              Number of leaves         :   11 ( 287 expanded)
%              Depth                    :   25
%              Number of atoms          :  440 (9744 expanded)
%              Number of equality atoms :   20 ( 109 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   24 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t44_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(k1_tops_1(X1,X2),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(d1_connsp_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( m1_connsp_2(X3,X1,X2)
              <=> r2_hidden(X2,k1_tops_1(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_connsp_2)).

fof(t9_connsp_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ~ ( r2_hidden(X3,X2)
                    & ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                       => ~ ( m1_connsp_2(X4,X1,X3)
                            & r1_tarski(X4,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_connsp_2)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_subset_1)).

fof(dt_k1_tops_1,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(t48_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( r1_tarski(X2,X3)
               => r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

fof(projectivity_k1_tops_1,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => k1_tops_1(X1,k1_tops_1(X1,X2)) = k1_tops_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',projectivity_k1_tops_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t5_connsp_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( ( v3_pre_topc(X2,X1)
                  & r2_hidden(X3,X2) )
               => m1_connsp_2(X2,X1,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_connsp_2)).

fof(t55_tops_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                 => ( ( v3_pre_topc(X4,X2)
                     => k1_tops_1(X2,X4) = X4 )
                    & ( k1_tops_1(X1,X3) = X3
                     => v3_pre_topc(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).

fof(c_0_11,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_12,plain,(
    ! [X21,X22] :
      ( ~ l1_pre_topc(X21)
      | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
      | r1_tarski(k1_tops_1(X21,X22),X22) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).

cnf(c_0_13,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_14,plain,
    ( r1_tarski(k1_tops_1(X1,X2),X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_15,plain,(
    ! [X30,X31,X32] :
      ( ( ~ m1_connsp_2(X32,X30,X31)
        | r2_hidden(X31,k1_tops_1(X30,X32))
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ m1_subset_1(X31,u1_struct_0(X30))
        | v2_struct_0(X30)
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30) )
      & ( ~ r2_hidden(X31,k1_tops_1(X30,X32))
        | m1_connsp_2(X32,X30,X31)
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ m1_subset_1(X31,u1_struct_0(X30))
        | v2_struct_0(X30)
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_connsp_2])])])])])).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v3_pre_topc(X2,X1)
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => ~ ( r2_hidden(X3,X2)
                      & ! [X4] :
                          ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                         => ~ ( m1_connsp_2(X4,X1,X3)
                              & r1_tarski(X4,X2) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t9_connsp_2])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,X2)
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ r2_hidden(X1,k1_tops_1(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_18,plain,
    ( r2_hidden(X3,k1_tops_1(X2,X1))
    | v2_struct_0(X2)
    | ~ m1_connsp_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_19,negated_conjecture,(
    ! [X39,X40] :
      ( ~ v2_struct_0(esk3_0)
      & v2_pre_topc(esk3_0)
      & l1_pre_topc(esk3_0)
      & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
      & ( m1_subset_1(esk5_0,u1_struct_0(esk3_0))
        | ~ v3_pre_topc(esk4_0,esk3_0) )
      & ( r2_hidden(esk5_0,esk4_0)
        | ~ v3_pre_topc(esk4_0,esk3_0) )
      & ( ~ m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(esk3_0)))
        | ~ m1_connsp_2(X39,esk3_0,esk5_0)
        | ~ r1_tarski(X39,esk4_0)
        | ~ v3_pre_topc(esk4_0,esk3_0) )
      & ( m1_subset_1(esk6_1(X40),k1_zfmisc_1(u1_struct_0(esk3_0)))
        | ~ r2_hidden(X40,esk4_0)
        | ~ m1_subset_1(X40,u1_struct_0(esk3_0))
        | v3_pre_topc(esk4_0,esk3_0) )
      & ( m1_connsp_2(esk6_1(X40),esk3_0,X40)
        | ~ r2_hidden(X40,esk4_0)
        | ~ m1_subset_1(X40,u1_struct_0(esk3_0))
        | v3_pre_topc(esk4_0,esk3_0) )
      & ( r1_tarski(esk6_1(X40),esk4_0)
        | ~ r2_hidden(X40,esk4_0)
        | ~ m1_subset_1(X40,u1_struct_0(esk3_0))
        | v3_pre_topc(esk4_0,esk3_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])])])).

fof(c_0_20,plain,(
    ! [X13,X14,X15] :
      ( ( m1_subset_1(esk2_3(X13,X14,X15),X13)
        | r1_tarski(X14,X15)
        | ~ m1_subset_1(X15,k1_zfmisc_1(X13))
        | ~ m1_subset_1(X14,k1_zfmisc_1(X13)) )
      & ( r2_hidden(esk2_3(X13,X14,X15),X14)
        | r1_tarski(X14,X15)
        | ~ m1_subset_1(X15,k1_zfmisc_1(X13))
        | ~ m1_subset_1(X14,k1_zfmisc_1(X13)) )
      & ( ~ r2_hidden(esk2_3(X13,X14,X15),X15)
        | r1_tarski(X14,X15)
        | ~ m1_subset_1(X15,k1_zfmisc_1(X13))
        | ~ m1_subset_1(X14,k1_zfmisc_1(X13)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_subset_1])])])])])).

cnf(c_0_21,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,X3)
    | ~ m1_connsp_2(X3,X1,X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( m1_connsp_2(X3,X2,X1)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,k1_tops_1(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_27,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | r1_tarski(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ m1_connsp_2(esk4_0,esk3_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23]),c_0_24])]),c_0_25])).

cnf(c_0_29,plain,
    ( m1_connsp_2(X1,X2,esk2_3(X3,k1_tops_1(X2,X1),X4))
    | v2_struct_0(X2)
    | r1_tarski(k1_tops_1(X2,X1),X4)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(esk2_3(X3,k1_tops_1(X2,X1),X4),u1_struct_0(X2))
    | ~ m1_subset_1(k1_tops_1(X2,X1),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk2_3(X1,k1_tops_1(esk3_0,esk4_0),X2),esk4_0)
    | r1_tarski(k1_tops_1(esk3_0,esk4_0),X2)
    | ~ m1_subset_1(esk2_3(X1,k1_tops_1(esk3_0,esk4_0),X2),u1_struct_0(esk3_0))
    | ~ m1_subset_1(k1_tops_1(esk3_0,esk4_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_23]),c_0_24]),c_0_22])]),c_0_25])).

cnf(c_0_31,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),X1)
    | r1_tarski(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_32,plain,
    ( r1_tarski(X2,X3)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk2_3(u1_struct_0(esk3_0),k1_tops_1(esk3_0,esk4_0),X1),esk4_0)
    | r1_tarski(k1_tops_1(esk3_0,esk4_0),X1)
    | ~ m1_subset_1(k1_tops_1(esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

fof(c_0_34,plain,(
    ! [X17,X18] :
      ( ~ l1_pre_topc(X17)
      | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
      | m1_subset_1(k1_tops_1(X17,X18),k1_zfmisc_1(u1_struct_0(X17))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_tops_1])])).

fof(c_0_35,plain,(
    ! [X23,X24,X25] :
      ( ~ l1_pre_topc(X23)
      | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))
      | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))
      | ~ r1_tarski(X24,X25)
      | r1_tarski(k1_tops_1(X23,X24),k1_tops_1(X23,X25)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_tops_1])])])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk3_0,esk4_0),esk4_0)
    | ~ m1_subset_1(k1_tops_1(esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_22])])).

cnf(c_0_37,plain,
    ( m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_38,plain,
    ( r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_39,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk3_0,esk4_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_24]),c_0_22])])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,k1_tops_1(X2,X3))
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X1,k1_tops_1(X2,X4))
    | ~ r1_tarski(X4,X3) ),
    inference(spm,[status(thm)],[c_0_13,c_0_38])).

cnf(c_0_41,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_42,plain,(
    ! [X19,X20] :
      ( ~ l1_pre_topc(X19)
      | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
      | k1_tops_1(X19,k1_tops_1(X19,X20)) = k1_tops_1(X19,X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[projectivity_k1_tops_1])])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,k1_tops_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_39])).

cnf(c_0_44,plain,
    ( r2_hidden(esk1_2(k1_tops_1(X1,X2),X3),k1_tops_1(X1,X4))
    | r1_tarski(k1_tops_1(X1,X2),X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X4) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_45,plain,
    ( k1_tops_1(X1,k1_tops_1(X1,X2)) = k1_tops_1(X1,X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_46,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk1_2(k1_tops_1(esk3_0,X1),X2),esk4_0)
    | r1_tarski(k1_tops_1(esk3_0,X1),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r1_tarski(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_24]),c_0_22])])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,k1_tops_1(X2,X3))
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X1,k1_tops_1(X2,X4))
    | ~ r1_tarski(k1_tops_1(X2,X4),X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_45]),c_0_37])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk3_0,X1),esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

fof(c_0_50,plain,(
    ! [X11,X12] :
      ( ( r1_tarski(X11,X12)
        | X11 != X12 )
      & ( r1_tarski(X12,X11)
        | X11 != X12 )
      & ( ~ r1_tarski(X11,X12)
        | ~ r1_tarski(X12,X11)
        | X11 = X12 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(X1,k1_tops_1(esk3_0,esk4_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r2_hidden(X1,k1_tops_1(esk3_0,X2))
    | ~ r1_tarski(X2,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_24]),c_0_22])])).

cnf(c_0_52,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

fof(c_0_53,plain,(
    ! [X33,X34,X35] :
      ( v2_struct_0(X33)
      | ~ v2_pre_topc(X33)
      | ~ l1_pre_topc(X33)
      | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))
      | ~ m1_subset_1(X35,u1_struct_0(X33))
      | ~ v3_pre_topc(X34,X33)
      | ~ r2_hidden(X35,X34)
      | m1_connsp_2(X34,X33,X35) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t5_connsp_2])])])])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk1_2(k1_tops_1(esk3_0,X1),X2),k1_tops_1(esk3_0,esk4_0))
    | r1_tarski(k1_tops_1(esk3_0,X1),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_41])).

cnf(c_0_55,negated_conjecture,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_connsp_2(X1,esk3_0,esk5_0)
    | ~ r1_tarski(X1,esk4_0)
    | ~ v3_pre_topc(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_56,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_52])).

cnf(c_0_57,plain,
    ( v2_struct_0(X1)
    | m1_connsp_2(X2,X1,X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v3_pre_topc(X2,X1)
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_58,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk3_0,X1),k1_tops_1(esk3_0,esk4_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_54])).

cnf(c_0_60,negated_conjecture,
    ( ~ m1_connsp_2(esk4_0,esk3_0,esk5_0)
    | ~ v3_pre_topc(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_22]),c_0_56])])).

cnf(c_0_61,negated_conjecture,
    ( m1_connsp_2(esk4_0,esk3_0,X1)
    | ~ v3_pre_topc(esk4_0,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_22]),c_0_23]),c_0_24])]),c_0_25])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(esk5_0,esk4_0)
    | ~ v3_pre_topc(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_63,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk3_0))
    | ~ v3_pre_topc(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_64,negated_conjecture,
    ( k1_tops_1(esk3_0,esk4_0) = k1_tops_1(esk3_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r1_tarski(k1_tops_1(esk3_0,esk4_0),k1_tops_1(esk3_0,X1))
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_65,plain,
    ( r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k1_tops_1(X1,X2),X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_45]),c_0_37])).

cnf(c_0_66,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,k1_tops_1(X1,X3))
    | ~ m1_connsp_2(X4,X1,X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r1_tarski(X4,X3) ),
    inference(spm,[status(thm)],[c_0_40,c_0_18])).

cnf(c_0_67,negated_conjecture,
    ( m1_subset_1(esk6_1(X1),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | v3_pre_topc(esk4_0,esk3_0)
    | ~ r2_hidden(X1,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_68,negated_conjecture,
    ( ~ v3_pre_topc(esk4_0,esk3_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_62]),c_0_63])).

cnf(c_0_69,negated_conjecture,
    ( k1_tops_1(esk3_0,esk4_0) = k1_tops_1(esk3_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r1_tarski(k1_tops_1(esk3_0,esk4_0),X1)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_24]),c_0_22])])).

cnf(c_0_70,negated_conjecture,
    ( r2_hidden(X1,k1_tops_1(esk3_0,X2))
    | ~ m1_connsp_2(esk6_1(X3),esk3_0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ m1_subset_1(X3,u1_struct_0(esk3_0))
    | ~ r2_hidden(X3,esk4_0)
    | ~ r1_tarski(esk6_1(X3),X2) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_23]),c_0_24])]),c_0_25]),c_0_68])).

cnf(c_0_71,negated_conjecture,
    ( m1_connsp_2(esk6_1(X1),esk3_0,X1)
    | v3_pre_topc(esk4_0,esk3_0)
    | ~ r2_hidden(X1,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_72,negated_conjecture,
    ( k1_tops_1(esk3_0,k1_tops_1(esk3_0,X1)) = k1_tops_1(esk3_0,esk4_0)
    | ~ m1_subset_1(k1_tops_1(esk3_0,X1),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r1_tarski(k1_tops_1(esk3_0,X1),esk4_0)
    | ~ r1_tarski(esk4_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_38]),c_0_24]),c_0_22])])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(X1,k1_tops_1(esk3_0,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,esk4_0)
    | ~ r1_tarski(esk6_1(X1),X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_68])).

cnf(c_0_74,negated_conjecture,
    ( k1_tops_1(esk3_0,k1_tops_1(esk3_0,X1)) = k1_tops_1(esk3_0,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r1_tarski(k1_tops_1(esk3_0,X1),esk4_0)
    | ~ r1_tarski(esk4_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_37]),c_0_24])])).

fof(c_0_75,plain,(
    ! [X26,X27,X28,X29] :
      ( ( ~ v3_pre_topc(X29,X27)
        | k1_tops_1(X27,X29) = X29
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X27)))
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ l1_pre_topc(X27)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) )
      & ( k1_tops_1(X26,X28) != X28
        | v3_pre_topc(X28,X26)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X27)))
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ l1_pre_topc(X27)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_tops_1])])])])).

cnf(c_0_76,negated_conjecture,
    ( m1_connsp_2(X1,esk3_0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0))
    | ~ r2_hidden(X2,esk4_0)
    | ~ r1_tarski(esk6_1(X2),X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_73]),c_0_23]),c_0_24])]),c_0_25])).

cnf(c_0_77,negated_conjecture,
    ( m1_subset_1(k1_tops_1(esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(k1_tops_1(esk3_0,X1),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r1_tarski(k1_tops_1(esk3_0,X1),esk4_0)
    | ~ r1_tarski(esk4_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_74]),c_0_24])])).

cnf(c_0_78,plain,
    ( v3_pre_topc(X2,X1)
    | k1_tops_1(X1,X2) != X2
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X4)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_79,plain,
    ( v2_struct_0(X1)
    | r1_tarski(X2,k1_tops_1(X1,X3))
    | ~ m1_connsp_2(X3,X1,esk2_3(X4,X2,k1_tops_1(X1,X3)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(esk2_3(X4,X2,k1_tops_1(X1,X3)),u1_struct_0(X1))
    | ~ m1_subset_1(k1_tops_1(X1,X3),k1_zfmisc_1(X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_18])).

cnf(c_0_80,negated_conjecture,
    ( m1_connsp_2(esk4_0,esk3_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,esk4_0)
    | ~ r1_tarski(esk6_1(X1),esk4_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_22])).

cnf(c_0_81,negated_conjecture,
    ( m1_subset_1(k1_tops_1(esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r1_tarski(k1_tops_1(esk3_0,X1),esk4_0)
    | ~ r1_tarski(esk4_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_37]),c_0_24])])).

cnf(c_0_82,negated_conjecture,
    ( v3_pre_topc(X1,X2)
    | k1_tops_1(X2,X1) != X1
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_22]),c_0_24])])).

cnf(c_0_83,negated_conjecture,
    ( r1_tarski(X1,k1_tops_1(esk3_0,esk4_0))
    | ~ m1_subset_1(esk2_3(X2,X1,k1_tops_1(esk3_0,esk4_0)),u1_struct_0(esk3_0))
    | ~ m1_subset_1(k1_tops_1(esk3_0,esk4_0),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(esk2_3(X2,X1,k1_tops_1(esk3_0,esk4_0)),esk4_0)
    | ~ r1_tarski(esk6_1(esk2_3(X2,X1,k1_tops_1(esk3_0,esk4_0))),esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_23]),c_0_24]),c_0_22])]),c_0_25])).

cnf(c_0_84,negated_conjecture,
    ( m1_subset_1(k1_tops_1(esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_14]),c_0_22]),c_0_56]),c_0_24])])).

cnf(c_0_85,negated_conjecture,
    ( k1_tops_1(esk3_0,esk4_0) != esk4_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_22]),c_0_23]),c_0_24])]),c_0_68])).

cnf(c_0_86,negated_conjecture,
    ( r1_tarski(esk6_1(X1),esk4_0)
    | v3_pre_topc(esk4_0,esk3_0)
    | ~ r2_hidden(X1,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_87,negated_conjecture,
    ( r1_tarski(X1,k1_tops_1(esk3_0,esk4_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r2_hidden(esk2_3(u1_struct_0(esk3_0),X1,k1_tops_1(esk3_0,esk4_0)),esk4_0)
    | ~ r1_tarski(esk6_1(esk2_3(u1_struct_0(esk3_0),X1,k1_tops_1(esk3_0,esk4_0))),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_31]),c_0_84])])).

cnf(c_0_88,negated_conjecture,
    ( ~ r1_tarski(esk4_0,k1_tops_1(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_39]),c_0_85])).

cnf(c_0_89,negated_conjecture,
    ( r1_tarski(esk6_1(esk2_3(u1_struct_0(esk3_0),X1,X2)),esk4_0)
    | r1_tarski(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r2_hidden(esk2_3(u1_struct_0(esk3_0),X1,X2),esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_31]),c_0_68])).

cnf(c_0_90,negated_conjecture,
    ( ~ r1_tarski(esk6_1(esk2_3(u1_struct_0(esk3_0),esk4_0,k1_tops_1(esk3_0,esk4_0))),esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_27]),c_0_22]),c_0_84])]),c_0_88])).

cnf(c_0_91,negated_conjecture,
    ( r1_tarski(esk6_1(esk2_3(u1_struct_0(esk3_0),esk4_0,X1)),esk4_0)
    | r1_tarski(esk4_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_27]),c_0_22])])).

cnf(c_0_92,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_84])]),c_0_88]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.11  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.31  % Computer   : n017.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % WCLimit    : 600
% 0.11/0.31  % DateTime   : Tue Dec  1 10:25:01 EST 2020
% 0.11/0.31  % CPUTime    : 
% 0.11/0.32  # Version: 2.5pre002
% 0.11/0.32  # No SInE strategy applied
% 0.11/0.32  # Trying AutoSched0 for 299 seconds
% 0.17/0.45  # AutoSched0-Mode selected heuristic G_E___207_C01_F1_SE_CS_SP_PI_S5PRR_S0Y
% 0.17/0.45  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.17/0.45  #
% 0.17/0.45  # Preprocessing time       : 0.019 s
% 0.17/0.45  
% 0.17/0.45  # Proof found!
% 0.17/0.45  # SZS status Theorem
% 0.17/0.45  # SZS output start CNFRefutation
% 0.17/0.45  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.17/0.45  fof(t44_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k1_tops_1(X1,X2),X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 0.17/0.45  fof(d1_connsp_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(m1_connsp_2(X3,X1,X2)<=>r2_hidden(X2,k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_connsp_2)).
% 0.17/0.45  fof(t9_connsp_2, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>~((r2_hidden(X3,X2)&![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>~((m1_connsp_2(X4,X1,X3)&r1_tarski(X4,X2)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_connsp_2)).
% 0.17/0.45  fof(t7_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(![X4]:(m1_subset_1(X4,X1)=>(r2_hidden(X4,X2)=>r2_hidden(X4,X3)))=>r1_tarski(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_subset_1)).
% 0.17/0.45  fof(dt_k1_tops_1, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 0.17/0.45  fof(t48_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r1_tarski(X2,X3)=>r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tops_1)).
% 0.17/0.45  fof(projectivity_k1_tops_1, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>k1_tops_1(X1,k1_tops_1(X1,X2))=k1_tops_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', projectivity_k1_tops_1)).
% 0.17/0.45  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.17/0.45  fof(t5_connsp_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>((v3_pre_topc(X2,X1)&r2_hidden(X3,X2))=>m1_connsp_2(X2,X1,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_connsp_2)).
% 0.17/0.45  fof(t55_tops_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(l1_pre_topc(X2)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>((v3_pre_topc(X4,X2)=>k1_tops_1(X2,X4)=X4)&(k1_tops_1(X1,X3)=X3=>v3_pre_topc(X3,X1))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_tops_1)).
% 0.17/0.45  fof(c_0_11, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.17/0.45  fof(c_0_12, plain, ![X21, X22]:(~l1_pre_topc(X21)|(~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))|r1_tarski(k1_tops_1(X21,X22),X22))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).
% 0.17/0.45  cnf(c_0_13, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.17/0.45  cnf(c_0_14, plain, (r1_tarski(k1_tops_1(X1,X2),X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.17/0.45  fof(c_0_15, plain, ![X30, X31, X32]:((~m1_connsp_2(X32,X30,X31)|r2_hidden(X31,k1_tops_1(X30,X32))|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X30)))|~m1_subset_1(X31,u1_struct_0(X30))|(v2_struct_0(X30)|~v2_pre_topc(X30)|~l1_pre_topc(X30)))&(~r2_hidden(X31,k1_tops_1(X30,X32))|m1_connsp_2(X32,X30,X31)|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X30)))|~m1_subset_1(X31,u1_struct_0(X30))|(v2_struct_0(X30)|~v2_pre_topc(X30)|~l1_pre_topc(X30)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_connsp_2])])])])])).
% 0.17/0.45  fof(c_0_16, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>~((r2_hidden(X3,X2)&![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>~((m1_connsp_2(X4,X1,X3)&r1_tarski(X4,X2))))))))))), inference(assume_negation,[status(cth)],[t9_connsp_2])).
% 0.17/0.45  cnf(c_0_17, plain, (r2_hidden(X1,X2)|~l1_pre_topc(X3)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~r2_hidden(X1,k1_tops_1(X3,X2))), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.17/0.45  cnf(c_0_18, plain, (r2_hidden(X3,k1_tops_1(X2,X1))|v2_struct_0(X2)|~m1_connsp_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,u1_struct_0(X2))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.17/0.45  fof(c_0_19, negated_conjecture, ![X39, X40]:(((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&l1_pre_topc(esk3_0))&(m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&(((m1_subset_1(esk5_0,u1_struct_0(esk3_0))|~v3_pre_topc(esk4_0,esk3_0))&((r2_hidden(esk5_0,esk4_0)|~v3_pre_topc(esk4_0,esk3_0))&(~m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(esk3_0)))|(~m1_connsp_2(X39,esk3_0,esk5_0)|~r1_tarski(X39,esk4_0))|~v3_pre_topc(esk4_0,esk3_0))))&((m1_subset_1(esk6_1(X40),k1_zfmisc_1(u1_struct_0(esk3_0)))|~r2_hidden(X40,esk4_0)|~m1_subset_1(X40,u1_struct_0(esk3_0))|v3_pre_topc(esk4_0,esk3_0))&((m1_connsp_2(esk6_1(X40),esk3_0,X40)|~r2_hidden(X40,esk4_0)|~m1_subset_1(X40,u1_struct_0(esk3_0))|v3_pre_topc(esk4_0,esk3_0))&(r1_tarski(esk6_1(X40),esk4_0)|~r2_hidden(X40,esk4_0)|~m1_subset_1(X40,u1_struct_0(esk3_0))|v3_pre_topc(esk4_0,esk3_0))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])])])).
% 0.17/0.45  fof(c_0_20, plain, ![X13, X14, X15]:((m1_subset_1(esk2_3(X13,X14,X15),X13)|r1_tarski(X14,X15)|~m1_subset_1(X15,k1_zfmisc_1(X13))|~m1_subset_1(X14,k1_zfmisc_1(X13)))&((r2_hidden(esk2_3(X13,X14,X15),X14)|r1_tarski(X14,X15)|~m1_subset_1(X15,k1_zfmisc_1(X13))|~m1_subset_1(X14,k1_zfmisc_1(X13)))&(~r2_hidden(esk2_3(X13,X14,X15),X15)|r1_tarski(X14,X15)|~m1_subset_1(X15,k1_zfmisc_1(X13))|~m1_subset_1(X14,k1_zfmisc_1(X13))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_subset_1])])])])])).
% 0.17/0.45  cnf(c_0_21, plain, (v2_struct_0(X1)|r2_hidden(X2,X3)|~m1_connsp_2(X3,X1,X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.17/0.45  cnf(c_0_22, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.17/0.45  cnf(c_0_23, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.17/0.45  cnf(c_0_24, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.17/0.45  cnf(c_0_25, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.17/0.45  cnf(c_0_26, plain, (m1_connsp_2(X3,X2,X1)|v2_struct_0(X2)|~r2_hidden(X1,k1_tops_1(X2,X3))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,u1_struct_0(X2))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.17/0.45  cnf(c_0_27, plain, (r2_hidden(esk2_3(X1,X2,X3),X2)|r1_tarski(X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.17/0.45  cnf(c_0_28, negated_conjecture, (r2_hidden(X1,esk4_0)|~m1_connsp_2(esk4_0,esk3_0,X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23]), c_0_24])]), c_0_25])).
% 0.17/0.45  cnf(c_0_29, plain, (m1_connsp_2(X1,X2,esk2_3(X3,k1_tops_1(X2,X1),X4))|v2_struct_0(X2)|r1_tarski(k1_tops_1(X2,X1),X4)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_subset_1(esk2_3(X3,k1_tops_1(X2,X1),X4),u1_struct_0(X2))|~m1_subset_1(k1_tops_1(X2,X1),k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X4,k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.17/0.45  cnf(c_0_30, negated_conjecture, (r2_hidden(esk2_3(X1,k1_tops_1(esk3_0,esk4_0),X2),esk4_0)|r1_tarski(k1_tops_1(esk3_0,esk4_0),X2)|~m1_subset_1(esk2_3(X1,k1_tops_1(esk3_0,esk4_0),X2),u1_struct_0(esk3_0))|~m1_subset_1(k1_tops_1(esk3_0,esk4_0),k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_23]), c_0_24]), c_0_22])]), c_0_25])).
% 0.17/0.45  cnf(c_0_31, plain, (m1_subset_1(esk2_3(X1,X2,X3),X1)|r1_tarski(X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.17/0.45  cnf(c_0_32, plain, (r1_tarski(X2,X3)|~r2_hidden(esk2_3(X1,X2,X3),X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.17/0.45  cnf(c_0_33, negated_conjecture, (r2_hidden(esk2_3(u1_struct_0(esk3_0),k1_tops_1(esk3_0,esk4_0),X1),esk4_0)|r1_tarski(k1_tops_1(esk3_0,esk4_0),X1)|~m1_subset_1(k1_tops_1(esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.17/0.45  fof(c_0_34, plain, ![X17, X18]:(~l1_pre_topc(X17)|~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))|m1_subset_1(k1_tops_1(X17,X18),k1_zfmisc_1(u1_struct_0(X17)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_tops_1])])).
% 0.17/0.45  fof(c_0_35, plain, ![X23, X24, X25]:(~l1_pre_topc(X23)|(~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))|(~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))|(~r1_tarski(X24,X25)|r1_tarski(k1_tops_1(X23,X24),k1_tops_1(X23,X25)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_tops_1])])])).
% 0.17/0.45  cnf(c_0_36, negated_conjecture, (r1_tarski(k1_tops_1(esk3_0,esk4_0),esk4_0)|~m1_subset_1(k1_tops_1(esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_22])])).
% 0.17/0.45  cnf(c_0_37, plain, (m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.17/0.45  cnf(c_0_38, plain, (r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.17/0.45  cnf(c_0_39, negated_conjecture, (r1_tarski(k1_tops_1(esk3_0,esk4_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_24]), c_0_22])])).
% 0.17/0.45  cnf(c_0_40, plain, (r2_hidden(X1,k1_tops_1(X2,X3))|~l1_pre_topc(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|~r2_hidden(X1,k1_tops_1(X2,X4))|~r1_tarski(X4,X3)), inference(spm,[status(thm)],[c_0_13, c_0_38])).
% 0.17/0.45  cnf(c_0_41, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.17/0.45  fof(c_0_42, plain, ![X19, X20]:(~l1_pre_topc(X19)|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|k1_tops_1(X19,k1_tops_1(X19,X20))=k1_tops_1(X19,X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[projectivity_k1_tops_1])])).
% 0.17/0.45  cnf(c_0_43, negated_conjecture, (r2_hidden(X1,esk4_0)|~r2_hidden(X1,k1_tops_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_13, c_0_39])).
% 0.17/0.45  cnf(c_0_44, plain, (r2_hidden(esk1_2(k1_tops_1(X1,X2),X3),k1_tops_1(X1,X4))|r1_tarski(k1_tops_1(X1,X2),X3)|~l1_pre_topc(X1)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X2,X4)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.17/0.45  cnf(c_0_45, plain, (k1_tops_1(X1,k1_tops_1(X1,X2))=k1_tops_1(X1,X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.17/0.45  cnf(c_0_46, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.17/0.45  cnf(c_0_47, negated_conjecture, (r2_hidden(esk1_2(k1_tops_1(esk3_0,X1),X2),esk4_0)|r1_tarski(k1_tops_1(esk3_0,X1),X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r1_tarski(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_24]), c_0_22])])).
% 0.17/0.45  cnf(c_0_48, plain, (r2_hidden(X1,k1_tops_1(X2,X3))|~l1_pre_topc(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|~r2_hidden(X1,k1_tops_1(X2,X4))|~r1_tarski(k1_tops_1(X2,X4),X3)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_45]), c_0_37])).
% 0.17/0.45  cnf(c_0_49, negated_conjecture, (r1_tarski(k1_tops_1(esk3_0,X1),esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.17/0.45  fof(c_0_50, plain, ![X11, X12]:(((r1_tarski(X11,X12)|X11!=X12)&(r1_tarski(X12,X11)|X11!=X12))&(~r1_tarski(X11,X12)|~r1_tarski(X12,X11)|X11=X12)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.17/0.45  cnf(c_0_51, negated_conjecture, (r2_hidden(X1,k1_tops_1(esk3_0,esk4_0))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r2_hidden(X1,k1_tops_1(esk3_0,X2))|~r1_tarski(X2,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_24]), c_0_22])])).
% 0.17/0.45  cnf(c_0_52, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.17/0.45  fof(c_0_53, plain, ![X33, X34, X35]:(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33)|(~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))|(~m1_subset_1(X35,u1_struct_0(X33))|(~v3_pre_topc(X34,X33)|~r2_hidden(X35,X34)|m1_connsp_2(X34,X33,X35))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t5_connsp_2])])])])).
% 0.17/0.45  cnf(c_0_54, negated_conjecture, (r2_hidden(esk1_2(k1_tops_1(esk3_0,X1),X2),k1_tops_1(esk3_0,esk4_0))|r1_tarski(k1_tops_1(esk3_0,X1),X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_51, c_0_41])).
% 0.17/0.45  cnf(c_0_55, negated_conjecture, (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_connsp_2(X1,esk3_0,esk5_0)|~r1_tarski(X1,esk4_0)|~v3_pre_topc(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.17/0.45  cnf(c_0_56, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_52])).
% 0.17/0.45  cnf(c_0_57, plain, (v2_struct_0(X1)|m1_connsp_2(X2,X1,X3)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,u1_struct_0(X1))|~v3_pre_topc(X2,X1)|~r2_hidden(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.17/0.45  cnf(c_0_58, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.17/0.45  cnf(c_0_59, negated_conjecture, (r1_tarski(k1_tops_1(esk3_0,X1),k1_tops_1(esk3_0,esk4_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_46, c_0_54])).
% 0.17/0.45  cnf(c_0_60, negated_conjecture, (~m1_connsp_2(esk4_0,esk3_0,esk5_0)|~v3_pre_topc(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_22]), c_0_56])])).
% 0.17/0.45  cnf(c_0_61, negated_conjecture, (m1_connsp_2(esk4_0,esk3_0,X1)|~v3_pre_topc(esk4_0,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk3_0))|~r2_hidden(X1,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_22]), c_0_23]), c_0_24])]), c_0_25])).
% 0.17/0.45  cnf(c_0_62, negated_conjecture, (r2_hidden(esk5_0,esk4_0)|~v3_pre_topc(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.17/0.45  cnf(c_0_63, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk3_0))|~v3_pre_topc(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.17/0.45  cnf(c_0_64, negated_conjecture, (k1_tops_1(esk3_0,esk4_0)=k1_tops_1(esk3_0,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r1_tarski(k1_tops_1(esk3_0,esk4_0),k1_tops_1(esk3_0,X1))|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.17/0.45  cnf(c_0_65, plain, (r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))|~l1_pre_topc(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(k1_tops_1(X1,X2),X3)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_45]), c_0_37])).
% 0.17/0.45  cnf(c_0_66, plain, (v2_struct_0(X1)|r2_hidden(X2,k1_tops_1(X1,X3))|~m1_connsp_2(X4,X1,X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,u1_struct_0(X1))|~r1_tarski(X4,X3)), inference(spm,[status(thm)],[c_0_40, c_0_18])).
% 0.17/0.45  cnf(c_0_67, negated_conjecture, (m1_subset_1(esk6_1(X1),k1_zfmisc_1(u1_struct_0(esk3_0)))|v3_pre_topc(esk4_0,esk3_0)|~r2_hidden(X1,esk4_0)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.17/0.45  cnf(c_0_68, negated_conjecture, (~v3_pre_topc(esk4_0,esk3_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_62]), c_0_63])).
% 0.17/0.45  cnf(c_0_69, negated_conjecture, (k1_tops_1(esk3_0,esk4_0)=k1_tops_1(esk3_0,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r1_tarski(k1_tops_1(esk3_0,esk4_0),X1)|~r1_tarski(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_24]), c_0_22])])).
% 0.17/0.45  cnf(c_0_70, negated_conjecture, (r2_hidden(X1,k1_tops_1(esk3_0,X2))|~m1_connsp_2(esk6_1(X3),esk3_0,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(X1,u1_struct_0(esk3_0))|~m1_subset_1(X3,u1_struct_0(esk3_0))|~r2_hidden(X3,esk4_0)|~r1_tarski(esk6_1(X3),X2)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_23]), c_0_24])]), c_0_25]), c_0_68])).
% 0.17/0.46  cnf(c_0_71, negated_conjecture, (m1_connsp_2(esk6_1(X1),esk3_0,X1)|v3_pre_topc(esk4_0,esk3_0)|~r2_hidden(X1,esk4_0)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.17/0.46  cnf(c_0_72, negated_conjecture, (k1_tops_1(esk3_0,k1_tops_1(esk3_0,X1))=k1_tops_1(esk3_0,esk4_0)|~m1_subset_1(k1_tops_1(esk3_0,X1),k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r1_tarski(k1_tops_1(esk3_0,X1),esk4_0)|~r1_tarski(esk4_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_38]), c_0_24]), c_0_22])])).
% 0.17/0.46  cnf(c_0_73, negated_conjecture, (r2_hidden(X1,k1_tops_1(esk3_0,X2))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(X1,u1_struct_0(esk3_0))|~r2_hidden(X1,esk4_0)|~r1_tarski(esk6_1(X1),X2)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_68])).
% 0.17/0.46  cnf(c_0_74, negated_conjecture, (k1_tops_1(esk3_0,k1_tops_1(esk3_0,X1))=k1_tops_1(esk3_0,esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r1_tarski(k1_tops_1(esk3_0,X1),esk4_0)|~r1_tarski(esk4_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_37]), c_0_24])])).
% 0.17/0.46  fof(c_0_75, plain, ![X26, X27, X28, X29]:((~v3_pre_topc(X29,X27)|k1_tops_1(X27,X29)=X29|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X27)))|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))|~l1_pre_topc(X27)|(~v2_pre_topc(X26)|~l1_pre_topc(X26)))&(k1_tops_1(X26,X28)!=X28|v3_pre_topc(X28,X26)|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X27)))|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))|~l1_pre_topc(X27)|(~v2_pre_topc(X26)|~l1_pre_topc(X26)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_tops_1])])])])).
% 0.17/0.46  cnf(c_0_76, negated_conjecture, (m1_connsp_2(X1,esk3_0,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(X2,u1_struct_0(esk3_0))|~r2_hidden(X2,esk4_0)|~r1_tarski(esk6_1(X2),X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_73]), c_0_23]), c_0_24])]), c_0_25])).
% 0.17/0.46  cnf(c_0_77, negated_conjecture, (m1_subset_1(k1_tops_1(esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(k1_tops_1(esk3_0,X1),k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r1_tarski(k1_tops_1(esk3_0,X1),esk4_0)|~r1_tarski(esk4_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_74]), c_0_24])])).
% 0.17/0.46  cnf(c_0_78, plain, (v3_pre_topc(X2,X1)|k1_tops_1(X1,X2)!=X2|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X4)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.17/0.46  cnf(c_0_79, plain, (v2_struct_0(X1)|r1_tarski(X2,k1_tops_1(X1,X3))|~m1_connsp_2(X3,X1,esk2_3(X4,X2,k1_tops_1(X1,X3)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(esk2_3(X4,X2,k1_tops_1(X1,X3)),u1_struct_0(X1))|~m1_subset_1(k1_tops_1(X1,X3),k1_zfmisc_1(X4))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(X4))), inference(spm,[status(thm)],[c_0_32, c_0_18])).
% 0.17/0.46  cnf(c_0_80, negated_conjecture, (m1_connsp_2(esk4_0,esk3_0,X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))|~r2_hidden(X1,esk4_0)|~r1_tarski(esk6_1(X1),esk4_0)), inference(spm,[status(thm)],[c_0_76, c_0_22])).
% 0.17/0.46  cnf(c_0_81, negated_conjecture, (m1_subset_1(k1_tops_1(esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r1_tarski(k1_tops_1(esk3_0,X1),esk4_0)|~r1_tarski(esk4_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_37]), c_0_24])])).
% 0.17/0.46  cnf(c_0_82, negated_conjecture, (v3_pre_topc(X1,X2)|k1_tops_1(X2,X1)!=X1|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_22]), c_0_24])])).
% 0.17/0.46  cnf(c_0_83, negated_conjecture, (r1_tarski(X1,k1_tops_1(esk3_0,esk4_0))|~m1_subset_1(esk2_3(X2,X1,k1_tops_1(esk3_0,esk4_0)),u1_struct_0(esk3_0))|~m1_subset_1(k1_tops_1(esk3_0,esk4_0),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(esk2_3(X2,X1,k1_tops_1(esk3_0,esk4_0)),esk4_0)|~r1_tarski(esk6_1(esk2_3(X2,X1,k1_tops_1(esk3_0,esk4_0))),esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_23]), c_0_24]), c_0_22])]), c_0_25])).
% 0.17/0.46  cnf(c_0_84, negated_conjecture, (m1_subset_1(k1_tops_1(esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_14]), c_0_22]), c_0_56]), c_0_24])])).
% 0.17/0.46  cnf(c_0_85, negated_conjecture, (k1_tops_1(esk3_0,esk4_0)!=esk4_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_22]), c_0_23]), c_0_24])]), c_0_68])).
% 0.17/0.46  cnf(c_0_86, negated_conjecture, (r1_tarski(esk6_1(X1),esk4_0)|v3_pre_topc(esk4_0,esk3_0)|~r2_hidden(X1,esk4_0)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.17/0.46  cnf(c_0_87, negated_conjecture, (r1_tarski(X1,k1_tops_1(esk3_0,esk4_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r2_hidden(esk2_3(u1_struct_0(esk3_0),X1,k1_tops_1(esk3_0,esk4_0)),esk4_0)|~r1_tarski(esk6_1(esk2_3(u1_struct_0(esk3_0),X1,k1_tops_1(esk3_0,esk4_0))),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_31]), c_0_84])])).
% 0.17/0.46  cnf(c_0_88, negated_conjecture, (~r1_tarski(esk4_0,k1_tops_1(esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_39]), c_0_85])).
% 0.17/0.46  cnf(c_0_89, negated_conjecture, (r1_tarski(esk6_1(esk2_3(u1_struct_0(esk3_0),X1,X2)),esk4_0)|r1_tarski(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r2_hidden(esk2_3(u1_struct_0(esk3_0),X1,X2),esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_31]), c_0_68])).
% 0.17/0.46  cnf(c_0_90, negated_conjecture, (~r1_tarski(esk6_1(esk2_3(u1_struct_0(esk3_0),esk4_0,k1_tops_1(esk3_0,esk4_0))),esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_27]), c_0_22]), c_0_84])]), c_0_88])).
% 0.17/0.46  cnf(c_0_91, negated_conjecture, (r1_tarski(esk6_1(esk2_3(u1_struct_0(esk3_0),esk4_0,X1)),esk4_0)|r1_tarski(esk4_0,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_27]), c_0_22])])).
% 0.17/0.46  cnf(c_0_92, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_91]), c_0_84])]), c_0_88]), ['proof']).
% 0.17/0.46  # SZS output end CNFRefutation
% 0.17/0.46  # Proof object total steps             : 93
% 0.17/0.46  # Proof object clause steps            : 70
% 0.17/0.46  # Proof object formula steps           : 23
% 0.17/0.46  # Proof object conjectures             : 47
% 0.17/0.46  # Proof object clause conjectures      : 44
% 0.17/0.46  # Proof object formula conjectures     : 3
% 0.17/0.46  # Proof object initial clauses used    : 26
% 0.17/0.46  # Proof object initial formulas used   : 11
% 0.17/0.46  # Proof object generating inferences   : 43
% 0.17/0.46  # Proof object simplifying inferences  : 81
% 0.17/0.46  # Training examples: 0 positive, 0 negative
% 0.17/0.46  # Parsed axioms                        : 11
% 0.17/0.46  # Removed by relevancy pruning/SinE    : 0
% 0.17/0.46  # Initial clauses                      : 28
% 0.17/0.46  # Removed in clause preprocessing      : 0
% 0.17/0.46  # Initial clauses in saturation        : 28
% 0.17/0.46  # Processed clauses                    : 1185
% 0.17/0.46  # ...of these trivial                  : 5
% 0.17/0.46  # ...subsumed                          : 783
% 0.17/0.46  # ...remaining for further processing  : 397
% 0.17/0.46  # Other redundant clauses eliminated   : 2
% 0.17/0.46  # Clauses deleted for lack of memory   : 0
% 0.17/0.46  # Backward-subsumed                    : 48
% 0.17/0.46  # Backward-rewritten                   : 25
% 0.17/0.46  # Generated clauses                    : 3314
% 0.17/0.46  # ...of the previous two non-trivial   : 2941
% 0.17/0.46  # Contextual simplify-reflections      : 17
% 0.17/0.46  # Paramodulations                      : 3312
% 0.17/0.46  # Factorizations                       : 0
% 0.17/0.46  # Equation resolutions                 : 2
% 0.17/0.46  # Propositional unsat checks           : 0
% 0.17/0.46  #    Propositional check models        : 0
% 0.17/0.46  #    Propositional check unsatisfiable : 0
% 0.17/0.46  #    Propositional clauses             : 0
% 0.17/0.46  #    Propositional clauses after purity: 0
% 0.17/0.46  #    Propositional unsat core size     : 0
% 0.17/0.46  #    Propositional preprocessing time  : 0.000
% 0.17/0.46  #    Propositional encoding time       : 0.000
% 0.17/0.46  #    Propositional solver time         : 0.000
% 0.17/0.46  #    Success case prop preproc time    : 0.000
% 0.17/0.46  #    Success case prop encoding time   : 0.000
% 0.17/0.46  #    Success case prop solver time     : 0.000
% 0.17/0.46  # Current number of processed clauses  : 322
% 0.17/0.46  #    Positive orientable unit clauses  : 8
% 0.17/0.46  #    Positive unorientable unit clauses: 0
% 0.17/0.46  #    Negative unit clauses             : 5
% 0.17/0.46  #    Non-unit-clauses                  : 309
% 0.17/0.46  # Current number of unprocessed clauses: 1739
% 0.17/0.46  # ...number of literals in the above   : 13869
% 0.17/0.46  # Current number of archived formulas  : 0
% 0.17/0.46  # Current number of archived clauses   : 73
% 0.17/0.46  # Clause-clause subsumption calls (NU) : 35649
% 0.17/0.46  # Rec. Clause-clause subsumption calls : 4052
% 0.17/0.46  # Non-unit clause-clause subsumptions  : 654
% 0.17/0.46  # Unit Clause-clause subsumption calls : 92
% 0.17/0.46  # Rewrite failures with RHS unbound    : 0
% 0.17/0.46  # BW rewrite match attempts            : 14
% 0.17/0.46  # BW rewrite match successes           : 4
% 0.17/0.46  # Condensation attempts                : 0
% 0.17/0.46  # Condensation successes               : 0
% 0.17/0.46  # Termbank termtop insertions          : 127994
% 0.17/0.46  
% 0.17/0.46  # -------------------------------------------------
% 0.17/0.46  # User time                : 0.136 s
% 0.17/0.46  # System time              : 0.005 s
% 0.17/0.46  # Total time               : 0.141 s
% 0.17/0.46  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
