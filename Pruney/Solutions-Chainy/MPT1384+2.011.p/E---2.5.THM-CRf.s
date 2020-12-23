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

% Result     : Theorem 1.34s
% Output     : CNFRefutation 1.34s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 320 expanded)
%              Number of clauses        :   43 ( 118 expanded)
%              Number of leaves         :   12 (  77 expanded)
%              Depth                    :   13
%              Number of atoms          :  329 (2738 expanded)
%              Number of equality atoms :   14 (  38 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   24 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

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

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

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

fof(t44_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(k1_tops_1(X1,X2),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(dt_k1_tops_1,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(c_0_12,plain,(
    ! [X7,X8,X9] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(X7))
      | ~ r2_hidden(X9,X8)
      | r2_hidden(X9,X7) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

fof(c_0_13,plain,(
    ! [X14,X15] :
      ( ( ~ m1_subset_1(X14,k1_zfmisc_1(X15))
        | r1_tarski(X14,X15) )
      & ( ~ r1_tarski(X14,X15)
        | m1_subset_1(X14,k1_zfmisc_1(X15)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_14,negated_conjecture,(
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

fof(c_0_15,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_16,plain,(
    ! [X35,X36,X37] :
      ( v2_struct_0(X35)
      | ~ v2_pre_topc(X35)
      | ~ l1_pre_topc(X35)
      | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))
      | ~ m1_subset_1(X37,u1_struct_0(X35))
      | ~ v3_pre_topc(X36,X35)
      | ~ r2_hidden(X37,X36)
      | m1_connsp_2(X36,X35,X37) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t5_connsp_2])])])])).

fof(c_0_17,plain,(
    ! [X16,X17,X18] :
      ( ~ r2_hidden(X16,X17)
      | ~ m1_subset_1(X17,k1_zfmisc_1(X18))
      | m1_subset_1(X16,X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_18,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_20,plain,(
    ! [X25,X26,X27] :
      ( ~ l1_pre_topc(X25)
      | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
      | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X25)))
      | ~ r1_tarski(X26,X27)
      | r1_tarski(k1_tops_1(X25,X26),k1_tops_1(X25,X27)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_tops_1])])])).

fof(c_0_21,negated_conjecture,(
    ! [X44,X45] :
      ( ~ v2_struct_0(esk2_0)
      & v2_pre_topc(esk2_0)
      & l1_pre_topc(esk2_0)
      & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
      & ( m1_subset_1(esk4_0,u1_struct_0(esk2_0))
        | ~ v3_pre_topc(esk3_0,esk2_0) )
      & ( r2_hidden(esk4_0,esk3_0)
        | ~ v3_pre_topc(esk3_0,esk2_0) )
      & ( ~ m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(esk2_0)))
        | ~ m1_connsp_2(X44,esk2_0,esk4_0)
        | ~ r1_tarski(X44,esk3_0)
        | ~ v3_pre_topc(esk3_0,esk2_0) )
      & ( m1_subset_1(esk5_1(X45),k1_zfmisc_1(u1_struct_0(esk2_0)))
        | ~ r2_hidden(X45,esk3_0)
        | ~ m1_subset_1(X45,u1_struct_0(esk2_0))
        | v3_pre_topc(esk3_0,esk2_0) )
      & ( m1_connsp_2(esk5_1(X45),esk2_0,X45)
        | ~ r2_hidden(X45,esk3_0)
        | ~ m1_subset_1(X45,u1_struct_0(esk2_0))
        | v3_pre_topc(esk3_0,esk2_0) )
      & ( r1_tarski(esk5_1(X45),esk3_0)
        | ~ r2_hidden(X45,esk3_0)
        | ~ m1_subset_1(X45,u1_struct_0(esk2_0))
        | v3_pre_topc(esk3_0,esk2_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])])])).

cnf(c_0_22,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( v2_struct_0(X1)
    | m1_connsp_2(X2,X1,X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v3_pre_topc(X2,X1)
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_26,plain,
    ( r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_27,plain,(
    ! [X32,X33,X34] :
      ( ( ~ m1_connsp_2(X34,X32,X33)
        | r2_hidden(X33,k1_tops_1(X32,X34))
        | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X32)))
        | ~ m1_subset_1(X33,u1_struct_0(X32))
        | v2_struct_0(X32)
        | ~ v2_pre_topc(X32)
        | ~ l1_pre_topc(X32) )
      & ( ~ r2_hidden(X33,k1_tops_1(X32,X34))
        | m1_connsp_2(X34,X32,X33)
        | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X32)))
        | ~ m1_subset_1(X33,u1_struct_0(X32))
        | v2_struct_0(X32)
        | ~ v2_pre_topc(X32)
        | ~ l1_pre_topc(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_connsp_2])])])])])).

cnf(c_0_28,negated_conjecture,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_connsp_2(X1,esk2_0,esk4_0)
    | ~ r1_tarski(X1,esk3_0)
    | ~ v3_pre_topc(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( m1_connsp_2(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ v3_pre_topc(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(csr,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_32,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_33,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_34,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,k1_tops_1(X2,X3))
    | ~ l1_pre_topc(X2)
    | ~ r2_hidden(X1,k1_tops_1(X2,X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(X4,X3) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_36,plain,
    ( r2_hidden(X3,k1_tops_1(X2,X1))
    | v2_struct_0(X2)
    | ~ m1_connsp_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,negated_conjecture,
    ( ~ m1_connsp_2(esk3_0,esk2_0,esk4_0)
    | ~ v3_pre_topc(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])])).

cnf(c_0_38,negated_conjecture,
    ( m1_connsp_2(esk3_0,esk2_0,X1)
    | ~ v3_pre_topc(esk3_0,esk2_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_29]),c_0_32]),c_0_33])]),c_0_34])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk4_0,esk3_0)
    | ~ v3_pre_topc(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_40,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,k1_tops_1(X1,X3))
    | ~ m1_connsp_2(X4,X1,X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r1_tarski(X4,X3) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(esk5_1(X1),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | v3_pre_topc(esk3_0,esk2_0)
    | ~ r2_hidden(X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_42,negated_conjecture,
    ( ~ v3_pre_topc(esk3_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_29])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(X1,k1_tops_1(esk2_0,X2))
    | ~ m1_connsp_2(esk5_1(X3),esk2_0,X1)
    | ~ r2_hidden(X3,esk3_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ r1_tarski(esk5_1(X3),X2) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_32]),c_0_33])]),c_0_34]),c_0_42]),c_0_43])).

cnf(c_0_45,negated_conjecture,
    ( m1_connsp_2(esk5_1(X1),esk2_0,X1)
    | v3_pre_topc(esk3_0,esk2_0)
    | ~ r2_hidden(X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(X1,k1_tops_1(esk2_0,X2))
    | ~ r2_hidden(X1,esk3_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r1_tarski(esk5_1(X1),X2) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_42]),c_0_43])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(esk5_1(X1),esk3_0)
    | v3_pre_topc(esk3_0,esk2_0)
    | ~ r2_hidden(X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_48,plain,(
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

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(X1,k1_tops_1(esk2_0,X2))
    | ~ r2_hidden(X1,esk3_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r1_tarski(esk5_1(X1),X3)
    | ~ r1_tarski(X3,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_46]),c_0_33])])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(esk5_1(X1),esk3_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_43]),c_0_42])).

cnf(c_0_51,plain,
    ( r1_tarski(X2,X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(X1,k1_tops_1(esk2_0,X2))
    | ~ r2_hidden(X1,esk3_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r1_tarski(esk3_0,X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_29]),c_0_50])).

fof(c_0_53,plain,(
    ! [X28,X29,X30,X31] :
      ( ( ~ v3_pre_topc(X31,X29)
        | k1_tops_1(X29,X31) = X31
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X29)))
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X28)))
        | ~ l1_pre_topc(X29)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28) )
      & ( k1_tops_1(X28,X30) != X30
        | v3_pre_topc(X30,X28)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X29)))
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X28)))
        | ~ l1_pre_topc(X29)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_tops_1])])])])).

fof(c_0_54,plain,(
    ! [X23,X24] :
      ( ~ l1_pre_topc(X23)
      | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))
      | r1_tarski(k1_tops_1(X23,X24),X24) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(X1,k1_tops_1(esk2_0,X2))
    | ~ r2_hidden(esk1_3(X3,X1,k1_tops_1(esk2_0,X2)),esk3_0)
    | ~ m1_subset_1(k1_tops_1(esk2_0,X2),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | ~ r1_tarski(esk3_0,X2) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_56,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r1_tarski(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

fof(c_0_57,plain,(
    ! [X19,X20] :
      ( ~ l1_pre_topc(X19)
      | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
      | m1_subset_1(k1_tops_1(X19,X20),k1_zfmisc_1(u1_struct_0(X19))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_tops_1])])).

cnf(c_0_58,plain,
    ( v3_pre_topc(X2,X1)
    | k1_tops_1(X1,X2) != X2
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X4)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_59,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_60,plain,
    ( r1_tarski(k1_tops_1(X1,X2),X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_61,negated_conjecture,
    ( r1_tarski(esk3_0,k1_tops_1(esk2_0,X1))
    | ~ m1_subset_1(k1_tops_1(esk2_0,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X2))
    | ~ r1_tarski(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_62,plain,
    ( m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_63,negated_conjecture,
    ( v3_pre_topc(X1,X2)
    | k1_tops_1(X2,X1) != X1
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_29]),c_0_33])])).

cnf(c_0_64,plain,
    ( k1_tops_1(X1,X2) = X2
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,k1_tops_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_65,negated_conjecture,
    ( r1_tarski(esk3_0,k1_tops_1(esk2_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r1_tarski(esk3_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_29]),c_0_33])])).

cnf(c_0_66,negated_conjecture,
    ( k1_tops_1(esk2_0,esk3_0) != esk3_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_29]),c_0_32]),c_0_33])]),c_0_42])).

cnf(c_0_67,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_33]),c_0_29]),c_0_30])]),c_0_66]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:56:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 1.34/1.49  # AutoSched0-Mode selected heuristic G_E___207_C01_F1_SE_CS_SP_PI_S5PRR_S0Y
% 1.34/1.49  # and selection function SelectMaxLComplexAvoidPosPred.
% 1.34/1.49  #
% 1.34/1.49  # Preprocessing time       : 0.028 s
% 1.34/1.49  
% 1.34/1.49  # Proof found!
% 1.34/1.49  # SZS status Theorem
% 1.34/1.49  # SZS output start CNFRefutation
% 1.34/1.49  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 1.34/1.49  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 1.34/1.49  fof(t9_connsp_2, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>~((r2_hidden(X3,X2)&![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>~((m1_connsp_2(X4,X1,X3)&r1_tarski(X4,X2)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_connsp_2)).
% 1.34/1.49  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.34/1.49  fof(t5_connsp_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>((v3_pre_topc(X2,X1)&r2_hidden(X3,X2))=>m1_connsp_2(X2,X1,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_connsp_2)).
% 1.34/1.49  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 1.34/1.49  fof(t48_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r1_tarski(X2,X3)=>r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tops_1)).
% 1.34/1.49  fof(d1_connsp_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(m1_connsp_2(X3,X1,X2)<=>r2_hidden(X2,k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_connsp_2)).
% 1.34/1.49  fof(t7_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(![X4]:(m1_subset_1(X4,X1)=>(r2_hidden(X4,X2)=>r2_hidden(X4,X3)))=>r1_tarski(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_subset_1)).
% 1.34/1.49  fof(t55_tops_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(l1_pre_topc(X2)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>((v3_pre_topc(X4,X2)=>k1_tops_1(X2,X4)=X4)&(k1_tops_1(X1,X3)=X3=>v3_pre_topc(X3,X1))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_tops_1)).
% 1.34/1.49  fof(t44_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k1_tops_1(X1,X2),X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 1.34/1.49  fof(dt_k1_tops_1, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 1.34/1.49  fof(c_0_12, plain, ![X7, X8, X9]:(~m1_subset_1(X8,k1_zfmisc_1(X7))|(~r2_hidden(X9,X8)|r2_hidden(X9,X7))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 1.34/1.49  fof(c_0_13, plain, ![X14, X15]:((~m1_subset_1(X14,k1_zfmisc_1(X15))|r1_tarski(X14,X15))&(~r1_tarski(X14,X15)|m1_subset_1(X14,k1_zfmisc_1(X15)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 1.34/1.49  fof(c_0_14, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>~((r2_hidden(X3,X2)&![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>~((m1_connsp_2(X4,X1,X3)&r1_tarski(X4,X2))))))))))), inference(assume_negation,[status(cth)],[t9_connsp_2])).
% 1.34/1.49  fof(c_0_15, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 1.34/1.49  fof(c_0_16, plain, ![X35, X36, X37]:(v2_struct_0(X35)|~v2_pre_topc(X35)|~l1_pre_topc(X35)|(~m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))|(~m1_subset_1(X37,u1_struct_0(X35))|(~v3_pre_topc(X36,X35)|~r2_hidden(X37,X36)|m1_connsp_2(X36,X35,X37))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t5_connsp_2])])])])).
% 1.34/1.49  fof(c_0_17, plain, ![X16, X17, X18]:(~r2_hidden(X16,X17)|~m1_subset_1(X17,k1_zfmisc_1(X18))|m1_subset_1(X16,X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 1.34/1.49  cnf(c_0_18, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 1.34/1.49  cnf(c_0_19, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 1.34/1.49  fof(c_0_20, plain, ![X25, X26, X27]:(~l1_pre_topc(X25)|(~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))|(~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X25)))|(~r1_tarski(X26,X27)|r1_tarski(k1_tops_1(X25,X26),k1_tops_1(X25,X27)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_tops_1])])])).
% 1.34/1.49  fof(c_0_21, negated_conjecture, ![X44, X45]:(((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&(((m1_subset_1(esk4_0,u1_struct_0(esk2_0))|~v3_pre_topc(esk3_0,esk2_0))&((r2_hidden(esk4_0,esk3_0)|~v3_pre_topc(esk3_0,esk2_0))&(~m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(esk2_0)))|(~m1_connsp_2(X44,esk2_0,esk4_0)|~r1_tarski(X44,esk3_0))|~v3_pre_topc(esk3_0,esk2_0))))&((m1_subset_1(esk5_1(X45),k1_zfmisc_1(u1_struct_0(esk2_0)))|~r2_hidden(X45,esk3_0)|~m1_subset_1(X45,u1_struct_0(esk2_0))|v3_pre_topc(esk3_0,esk2_0))&((m1_connsp_2(esk5_1(X45),esk2_0,X45)|~r2_hidden(X45,esk3_0)|~m1_subset_1(X45,u1_struct_0(esk2_0))|v3_pre_topc(esk3_0,esk2_0))&(r1_tarski(esk5_1(X45),esk3_0)|~r2_hidden(X45,esk3_0)|~m1_subset_1(X45,u1_struct_0(esk2_0))|v3_pre_topc(esk3_0,esk2_0))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])])])).
% 1.34/1.49  cnf(c_0_22, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.34/1.49  cnf(c_0_23, plain, (v2_struct_0(X1)|m1_connsp_2(X2,X1,X3)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,u1_struct_0(X1))|~v3_pre_topc(X2,X1)|~r2_hidden(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 1.34/1.49  cnf(c_0_24, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.34/1.49  cnf(c_0_25, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 1.34/1.49  cnf(c_0_26, plain, (r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 1.34/1.49  fof(c_0_27, plain, ![X32, X33, X34]:((~m1_connsp_2(X34,X32,X33)|r2_hidden(X33,k1_tops_1(X32,X34))|~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X32)))|~m1_subset_1(X33,u1_struct_0(X32))|(v2_struct_0(X32)|~v2_pre_topc(X32)|~l1_pre_topc(X32)))&(~r2_hidden(X33,k1_tops_1(X32,X34))|m1_connsp_2(X34,X32,X33)|~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X32)))|~m1_subset_1(X33,u1_struct_0(X32))|(v2_struct_0(X32)|~v2_pre_topc(X32)|~l1_pre_topc(X32)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_connsp_2])])])])])).
% 1.34/1.49  cnf(c_0_28, negated_conjecture, (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_connsp_2(X1,esk2_0,esk4_0)|~r1_tarski(X1,esk3_0)|~v3_pre_topc(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.34/1.49  cnf(c_0_29, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.34/1.49  cnf(c_0_30, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_22])).
% 1.34/1.49  cnf(c_0_31, plain, (m1_connsp_2(X1,X2,X3)|v2_struct_0(X2)|~v3_pre_topc(X1,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~r2_hidden(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(csr,[status(thm)],[c_0_23, c_0_24])).
% 1.34/1.49  cnf(c_0_32, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.34/1.49  cnf(c_0_33, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.34/1.49  cnf(c_0_34, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.34/1.49  cnf(c_0_35, plain, (r2_hidden(X1,k1_tops_1(X2,X3))|~l1_pre_topc(X2)|~r2_hidden(X1,k1_tops_1(X2,X4))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|~r1_tarski(X4,X3)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 1.34/1.49  cnf(c_0_36, plain, (r2_hidden(X3,k1_tops_1(X2,X1))|v2_struct_0(X2)|~m1_connsp_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,u1_struct_0(X2))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 1.34/1.49  cnf(c_0_37, negated_conjecture, (~m1_connsp_2(esk3_0,esk2_0,esk4_0)|~v3_pre_topc(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30])])).
% 1.34/1.49  cnf(c_0_38, negated_conjecture, (m1_connsp_2(esk3_0,esk2_0,X1)|~v3_pre_topc(esk3_0,esk2_0)|~r2_hidden(X1,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_29]), c_0_32]), c_0_33])]), c_0_34])).
% 1.34/1.49  cnf(c_0_39, negated_conjecture, (r2_hidden(esk4_0,esk3_0)|~v3_pre_topc(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.34/1.49  cnf(c_0_40, plain, (v2_struct_0(X1)|r2_hidden(X2,k1_tops_1(X1,X3))|~m1_connsp_2(X4,X1,X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,u1_struct_0(X1))|~r1_tarski(X4,X3)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 1.34/1.49  cnf(c_0_41, negated_conjecture, (m1_subset_1(esk5_1(X1),k1_zfmisc_1(u1_struct_0(esk2_0)))|v3_pre_topc(esk3_0,esk2_0)|~r2_hidden(X1,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.34/1.49  cnf(c_0_42, negated_conjecture, (~v3_pre_topc(esk3_0,esk2_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39])).
% 1.34/1.49  cnf(c_0_43, negated_conjecture, (m1_subset_1(X1,u1_struct_0(esk2_0))|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_24, c_0_29])).
% 1.34/1.49  cnf(c_0_44, negated_conjecture, (r2_hidden(X1,k1_tops_1(esk2_0,X2))|~m1_connsp_2(esk5_1(X3),esk2_0,X1)|~r2_hidden(X3,esk3_0)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(X1,u1_struct_0(esk2_0))|~r1_tarski(esk5_1(X3),X2)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_32]), c_0_33])]), c_0_34]), c_0_42]), c_0_43])).
% 1.34/1.49  cnf(c_0_45, negated_conjecture, (m1_connsp_2(esk5_1(X1),esk2_0,X1)|v3_pre_topc(esk3_0,esk2_0)|~r2_hidden(X1,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.34/1.49  cnf(c_0_46, negated_conjecture, (r2_hidden(X1,k1_tops_1(esk2_0,X2))|~r2_hidden(X1,esk3_0)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r1_tarski(esk5_1(X1),X2)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_42]), c_0_43])).
% 1.34/1.49  cnf(c_0_47, negated_conjecture, (r1_tarski(esk5_1(X1),esk3_0)|v3_pre_topc(esk3_0,esk2_0)|~r2_hidden(X1,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.34/1.49  fof(c_0_48, plain, ![X10, X11, X12]:((m1_subset_1(esk1_3(X10,X11,X12),X10)|r1_tarski(X11,X12)|~m1_subset_1(X12,k1_zfmisc_1(X10))|~m1_subset_1(X11,k1_zfmisc_1(X10)))&((r2_hidden(esk1_3(X10,X11,X12),X11)|r1_tarski(X11,X12)|~m1_subset_1(X12,k1_zfmisc_1(X10))|~m1_subset_1(X11,k1_zfmisc_1(X10)))&(~r2_hidden(esk1_3(X10,X11,X12),X12)|r1_tarski(X11,X12)|~m1_subset_1(X12,k1_zfmisc_1(X10))|~m1_subset_1(X11,k1_zfmisc_1(X10))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_subset_1])])])])])).
% 1.34/1.49  cnf(c_0_49, negated_conjecture, (r2_hidden(X1,k1_tops_1(esk2_0,X2))|~r2_hidden(X1,esk3_0)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r1_tarski(esk5_1(X1),X3)|~r1_tarski(X3,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_46]), c_0_33])])).
% 1.34/1.49  cnf(c_0_50, negated_conjecture, (r1_tarski(esk5_1(X1),esk3_0)|~r2_hidden(X1,esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_43]), c_0_42])).
% 1.34/1.49  cnf(c_0_51, plain, (r1_tarski(X2,X3)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 1.34/1.49  cnf(c_0_52, negated_conjecture, (r2_hidden(X1,k1_tops_1(esk2_0,X2))|~r2_hidden(X1,esk3_0)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r1_tarski(esk3_0,X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_29]), c_0_50])).
% 1.34/1.49  fof(c_0_53, plain, ![X28, X29, X30, X31]:((~v3_pre_topc(X31,X29)|k1_tops_1(X29,X31)=X31|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X29)))|~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X28)))|~l1_pre_topc(X29)|(~v2_pre_topc(X28)|~l1_pre_topc(X28)))&(k1_tops_1(X28,X30)!=X30|v3_pre_topc(X30,X28)|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X29)))|~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X28)))|~l1_pre_topc(X29)|(~v2_pre_topc(X28)|~l1_pre_topc(X28)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_tops_1])])])])).
% 1.34/1.49  fof(c_0_54, plain, ![X23, X24]:(~l1_pre_topc(X23)|(~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))|r1_tarski(k1_tops_1(X23,X24),X24))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).
% 1.34/1.49  cnf(c_0_55, negated_conjecture, (r1_tarski(X1,k1_tops_1(esk2_0,X2))|~r2_hidden(esk1_3(X3,X1,k1_tops_1(esk2_0,X2)),esk3_0)|~m1_subset_1(k1_tops_1(esk2_0,X2),k1_zfmisc_1(X3))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(X1,k1_zfmisc_1(X3))|~r1_tarski(esk3_0,X2)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 1.34/1.49  cnf(c_0_56, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r1_tarski(X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 1.34/1.49  fof(c_0_57, plain, ![X19, X20]:(~l1_pre_topc(X19)|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|m1_subset_1(k1_tops_1(X19,X20),k1_zfmisc_1(u1_struct_0(X19)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_tops_1])])).
% 1.34/1.49  cnf(c_0_58, plain, (v3_pre_topc(X2,X1)|k1_tops_1(X1,X2)!=X2|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X4)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 1.34/1.49  cnf(c_0_59, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.34/1.49  cnf(c_0_60, plain, (r1_tarski(k1_tops_1(X1,X2),X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 1.34/1.49  cnf(c_0_61, negated_conjecture, (r1_tarski(esk3_0,k1_tops_1(esk2_0,X1))|~m1_subset_1(k1_tops_1(esk2_0,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(esk3_0,k1_zfmisc_1(X2))|~r1_tarski(esk3_0,X1)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 1.34/1.49  cnf(c_0_62, plain, (m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 1.34/1.49  cnf(c_0_63, negated_conjecture, (v3_pre_topc(X1,X2)|k1_tops_1(X2,X1)!=X1|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_29]), c_0_33])])).
% 1.34/1.49  cnf(c_0_64, plain, (k1_tops_1(X1,X2)=X2|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X2,k1_tops_1(X1,X2))), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 1.34/1.49  cnf(c_0_65, negated_conjecture, (r1_tarski(esk3_0,k1_tops_1(esk2_0,X1))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r1_tarski(esk3_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_29]), c_0_33])])).
% 1.34/1.49  cnf(c_0_66, negated_conjecture, (k1_tops_1(esk2_0,esk3_0)!=esk3_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_29]), c_0_32]), c_0_33])]), c_0_42])).
% 1.34/1.49  cnf(c_0_67, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_33]), c_0_29]), c_0_30])]), c_0_66]), ['proof']).
% 1.34/1.49  # SZS output end CNFRefutation
% 1.34/1.49  # Proof object total steps             : 68
% 1.34/1.49  # Proof object clause steps            : 43
% 1.34/1.49  # Proof object formula steps           : 25
% 1.34/1.49  # Proof object conjectures             : 27
% 1.34/1.49  # Proof object clause conjectures      : 24
% 1.34/1.49  # Proof object formula conjectures     : 3
% 1.34/1.49  # Proof object initial clauses used    : 22
% 1.34/1.49  # Proof object initial formulas used   : 12
% 1.34/1.49  # Proof object generating inferences   : 19
% 1.34/1.49  # Proof object simplifying inferences  : 35
% 1.34/1.49  # Training examples: 0 positive, 0 negative
% 1.34/1.49  # Parsed axioms                        : 14
% 1.34/1.49  # Removed by relevancy pruning/SinE    : 0
% 1.34/1.49  # Initial clauses                      : 30
% 1.34/1.49  # Removed in clause preprocessing      : 0
% 1.34/1.49  # Initial clauses in saturation        : 30
% 1.34/1.49  # Processed clauses                    : 10674
% 1.34/1.49  # ...of these trivial                  : 22
% 1.34/1.49  # ...subsumed                          : 8812
% 1.34/1.49  # ...remaining for further processing  : 1840
% 1.34/1.49  # Other redundant clauses eliminated   : 2
% 1.34/1.49  # Clauses deleted for lack of memory   : 0
% 1.34/1.49  # Backward-subsumed                    : 492
% 1.34/1.49  # Backward-rewritten                   : 2
% 1.34/1.49  # Generated clauses                    : 37802
% 1.34/1.49  # ...of the previous two non-trivial   : 35775
% 1.34/1.49  # Contextual simplify-reflections      : 383
% 1.34/1.49  # Paramodulations                      : 37800
% 1.34/1.49  # Factorizations                       : 0
% 1.34/1.49  # Equation resolutions                 : 2
% 1.34/1.49  # Propositional unsat checks           : 0
% 1.34/1.49  #    Propositional check models        : 0
% 1.34/1.49  #    Propositional check unsatisfiable : 0
% 1.34/1.49  #    Propositional clauses             : 0
% 1.34/1.49  #    Propositional clauses after purity: 0
% 1.34/1.49  #    Propositional unsat core size     : 0
% 1.34/1.49  #    Propositional preprocessing time  : 0.000
% 1.34/1.49  #    Propositional encoding time       : 0.000
% 1.34/1.49  #    Propositional solver time         : 0.000
% 1.34/1.49  #    Success case prop preproc time    : 0.000
% 1.34/1.49  #    Success case prop encoding time   : 0.000
% 1.34/1.49  #    Success case prop solver time     : 0.000
% 1.34/1.49  # Current number of processed clauses  : 1344
% 1.34/1.49  #    Positive orientable unit clauses  : 6
% 1.34/1.49  #    Positive unorientable unit clauses: 0
% 1.34/1.49  #    Negative unit clauses             : 5
% 1.34/1.49  #    Non-unit-clauses                  : 1333
% 1.34/1.49  # Current number of unprocessed clauses: 24057
% 1.34/1.49  # ...number of literals in the above   : 238021
% 1.34/1.49  # Current number of archived formulas  : 0
% 1.34/1.49  # Current number of archived clauses   : 494
% 1.34/1.49  # Clause-clause subsumption calls (NU) : 511485
% 1.34/1.49  # Rec. Clause-clause subsumption calls : 46125
% 1.34/1.49  # Non-unit clause-clause subsumptions  : 6182
% 1.34/1.49  # Unit Clause-clause subsumption calls : 692
% 1.34/1.49  # Rewrite failures with RHS unbound    : 0
% 1.34/1.49  # BW rewrite match attempts            : 8
% 1.34/1.49  # BW rewrite match successes           : 1
% 1.34/1.49  # Condensation attempts                : 0
% 1.34/1.49  # Condensation successes               : 0
% 1.34/1.49  # Termbank termtop insertions          : 1465160
% 1.34/1.49  
% 1.34/1.49  # -------------------------------------------------
% 1.34/1.49  # User time                : 1.130 s
% 1.34/1.49  # System time              : 0.023 s
% 1.34/1.49  # Total time               : 1.153 s
% 1.34/1.49  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
