%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT2045+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:09 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 645 expanded)
%              Number of clauses        :   66 ( 228 expanded)
%              Number of leaves         :   14 ( 157 expanded)
%              Depth                    :   12
%              Number of atoms          :  396 (4171 expanded)
%              Number of equality atoms :    4 (   8 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   23 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t4_yellow19,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( ( v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X1)))
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) )
             => ( r2_waybel_7(X1,X3,X2)
              <=> r1_tarski(k1_yellow19(X1,X2),X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_yellow19)).

fof(t3_yellow19,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( r2_hidden(X3,k1_yellow19(X1,X2))
            <=> m1_connsp_2(X3,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_yellow19)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(dt_m1_connsp_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => ! [X3] :
          ( m1_connsp_2(X3,X1,X2)
         => m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).

fof(d5_waybel_7,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2,X3] :
          ( r2_waybel_7(X1,X2,X3)
        <=> ! [X4] :
              ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( v3_pre_topc(X4,X1)
                  & r2_hidden(X3,X4) )
               => r2_hidden(X4,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_waybel_7)).

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

fof(dt_k1_tops_1,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(fc9_tops_1,axiom,(
    ! [X1,X2] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => v3_pre_topc(k1_tops_1(X1,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(t44_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(k1_tops_1(X1,X2),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(t11_waybel_7,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
     => ( v13_waybel_0(X2,k3_yellow_1(X1))
      <=> ! [X3,X4] :
            ( ( r1_tarski(X3,X4)
              & r1_tarski(X4,X1)
              & r2_hidden(X3,X2) )
           => r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_waybel_7)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( ( v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X1)))
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) )
               => ( r2_waybel_7(X1,X3,X2)
                <=> r1_tarski(k1_yellow19(X1,X2),X3) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t4_yellow19])).

fof(c_0_15,plain,(
    ! [X38,X39,X40] :
      ( ( ~ r2_hidden(X40,k1_yellow19(X38,X39))
        | m1_connsp_2(X40,X38,X39)
        | ~ m1_subset_1(X39,u1_struct_0(X38))
        | v2_struct_0(X38)
        | ~ v2_pre_topc(X38)
        | ~ l1_pre_topc(X38) )
      & ( ~ m1_connsp_2(X40,X38,X39)
        | r2_hidden(X40,k1_yellow19(X38,X39))
        | ~ m1_subset_1(X39,u1_struct_0(X38))
        | v2_struct_0(X38)
        | ~ v2_pre_topc(X38)
        | ~ l1_pre_topc(X38) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_yellow19])])])])])).

fof(c_0_16,plain,(
    ! [X9,X10,X11,X12,X13] :
      ( ( ~ r1_tarski(X9,X10)
        | ~ r2_hidden(X11,X9)
        | r2_hidden(X11,X10) )
      & ( r2_hidden(esk1_2(X12,X13),X12)
        | r1_tarski(X12,X13) )
      & ( ~ r2_hidden(esk1_2(X12,X13),X13)
        | r1_tarski(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_17,plain,(
    ! [X25,X26,X27] :
      ( v2_struct_0(X25)
      | ~ v2_pre_topc(X25)
      | ~ l1_pre_topc(X25)
      | ~ m1_subset_1(X26,u1_struct_0(X25))
      | ~ m1_connsp_2(X27,X25,X26)
      | m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X25))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m1_connsp_2])])])])).

fof(c_0_18,negated_conjecture,
    ( ~ v2_struct_0(esk5_0)
    & v2_pre_topc(esk5_0)
    & l1_pre_topc(esk5_0)
    & m1_subset_1(esk6_0,u1_struct_0(esk5_0))
    & v13_waybel_0(esk7_0,k3_yellow_1(k2_struct_0(esk5_0)))
    & m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk5_0)))))
    & ( ~ r2_waybel_7(esk5_0,esk7_0,esk6_0)
      | ~ r1_tarski(k1_yellow19(esk5_0,esk6_0),esk7_0) )
    & ( r2_waybel_7(esk5_0,esk7_0,esk6_0)
      | r1_tarski(k1_yellow19(esk5_0,esk6_0),esk7_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).

cnf(c_0_19,plain,
    ( m1_connsp_2(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,k1_yellow19(X2,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_21,plain,(
    ! [X15,X16,X17,X18,X19,X20] :
      ( ( ~ r2_waybel_7(X15,X16,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ v3_pre_topc(X18,X15)
        | ~ r2_hidden(X17,X18)
        | r2_hidden(X18,X16)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( m1_subset_1(esk2_3(X15,X19,X20),k1_zfmisc_1(u1_struct_0(X15)))
        | r2_waybel_7(X15,X19,X20)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( v3_pre_topc(esk2_3(X15,X19,X20),X15)
        | r2_waybel_7(X15,X19,X20)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( r2_hidden(X20,esk2_3(X15,X19,X20))
        | r2_waybel_7(X15,X19,X20)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( ~ r2_hidden(esk2_3(X15,X19,X20),X19)
        | r2_waybel_7(X15,X19,X20)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_waybel_7])])])])])])).

fof(c_0_22,plain,(
    ! [X5,X6,X7] :
      ( ( ~ m1_connsp_2(X7,X5,X6)
        | r2_hidden(X6,k1_tops_1(X5,X7))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X5)))
        | ~ m1_subset_1(X6,u1_struct_0(X5))
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5) )
      & ( ~ r2_hidden(X6,k1_tops_1(X5,X7))
        | m1_connsp_2(X7,X5,X6)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X5)))
        | ~ m1_subset_1(X6,u1_struct_0(X5))
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_connsp_2])])])])])).

fof(c_0_23,plain,(
    ! [X43,X44,X45] :
      ( v2_struct_0(X43)
      | ~ v2_pre_topc(X43)
      | ~ l1_pre_topc(X43)
      | ~ m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X43)))
      | ~ m1_subset_1(X45,u1_struct_0(X43))
      | ~ v3_pre_topc(X44,X43)
      | ~ r2_hidden(X45,X44)
      | m1_connsp_2(X44,X43,X45) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t5_connsp_2])])])])).

fof(c_0_24,plain,(
    ! [X22,X23] :
      ( ~ l1_pre_topc(X22)
      | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
      | m1_subset_1(k1_tops_1(X22,X23),k1_zfmisc_1(u1_struct_0(X22))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_tops_1])])).

fof(c_0_25,plain,(
    ! [X28,X29] :
      ( ~ v2_pre_topc(X28)
      | ~ l1_pre_topc(X28)
      | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))
      | v3_pre_topc(k1_tops_1(X28,X29),X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).

cnf(c_0_26,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,negated_conjecture,
    ( v2_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_30,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_31,plain,
    ( r1_tarski(k1_yellow19(X1,X2),X3)
    | m1_connsp_2(esk1_2(k1_yellow19(X1,X2),X3),X1,X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_32,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | r2_waybel_7(X1,X2,X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_33,plain,
    ( v3_pre_topc(esk2_3(X1,X2,X3),X1)
    | r2_waybel_7(X1,X2,X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_34,plain,(
    ! [X8] :
      ( ~ l1_struct_0(X8)
      | k2_struct_0(X8) = u1_struct_0(X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_35,plain,(
    ! [X24] :
      ( ~ l1_pre_topc(X24)
      | l1_struct_0(X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_36,plain,(
    ! [X41,X42] :
      ( ~ l1_pre_topc(X41)
      | ~ m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41)))
      | r1_tarski(k1_tops_1(X41,X42),X42) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).

cnf(c_0_37,plain,
    ( r2_hidden(X3,k1_tops_1(X2,X1))
    | v2_struct_0(X2)
    | ~ m1_connsp_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_38,plain,
    ( v2_struct_0(X1)
    | m1_connsp_2(X2,X1,X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v3_pre_topc(X2,X1)
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_39,plain,
    ( m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_40,plain,
    ( v3_pre_topc(k1_tops_1(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_connsp_2(X1,esk5_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29])]),c_0_30])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(k1_yellow19(esk5_0,esk6_0),X1)
    | m1_connsp_2(esk1_2(k1_yellow19(esk5_0,esk6_0),X1),esk5_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_27]),c_0_28]),c_0_29])]),c_0_30])).

cnf(c_0_43,negated_conjecture,
    ( r2_waybel_7(esk5_0,X1,X2)
    | m1_subset_1(esk2_3(esk5_0,X1,X2),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_28]),c_0_29])])).

cnf(c_0_44,negated_conjecture,
    ( v3_pre_topc(esk2_3(esk5_0,X1,X2),esk5_0)
    | r2_waybel_7(esk5_0,X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_28]),c_0_29])])).

cnf(c_0_45,plain,
    ( r2_hidden(X1,esk2_3(X2,X3,X1))
    | r2_waybel_7(X2,X3,X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_46,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_47,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_48,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_49,plain,
    ( r1_tarski(k1_tops_1(X1,X2),X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_50,plain,
    ( r2_hidden(X1,k1_tops_1(X2,X3))
    | v2_struct_0(X2)
    | ~ m1_connsp_2(X3,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_37,c_0_26])).

cnf(c_0_51,plain,
    ( m1_connsp_2(k1_tops_1(X1,X2),X1,X3)
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,k1_tops_1(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(k1_yellow19(esk5_0,esk6_0),X1)
    | m1_subset_1(esk1_2(k1_yellow19(esk5_0,esk6_0),X1),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_53,negated_conjecture,
    ( r2_waybel_7(esk5_0,esk7_0,esk6_0)
    | r1_tarski(k1_yellow19(esk5_0,esk6_0),esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_54,plain,
    ( r2_hidden(X1,k1_yellow19(X2,X3))
    | v2_struct_0(X2)
    | ~ m1_connsp_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_55,negated_conjecture,
    ( r2_waybel_7(esk5_0,X1,X2)
    | m1_connsp_2(esk2_3(esk5_0,X1,X2),esk5_0,X3)
    | ~ r2_hidden(X3,esk2_3(esk5_0,X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_43]),c_0_28]),c_0_29])]),c_0_30]),c_0_44])).

cnf(c_0_56,negated_conjecture,
    ( r2_waybel_7(esk5_0,X1,X2)
    | r2_hidden(X2,esk2_3(esk5_0,X1,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_28]),c_0_29])])).

cnf(c_0_57,plain,
    ( r2_hidden(X4,X2)
    | ~ r2_waybel_7(X1,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X4,X1)
    | ~ r2_hidden(X3,X4)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_58,plain,(
    ! [X30,X31,X32,X33] :
      ( ( ~ v13_waybel_0(X31,k3_yellow_1(X30))
        | ~ r1_tarski(X32,X33)
        | ~ r1_tarski(X33,X30)
        | ~ r2_hidden(X32,X31)
        | r2_hidden(X33,X31)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X30)))) )
      & ( r1_tarski(esk3_2(X30,X31),esk4_2(X30,X31))
        | v13_waybel_0(X31,k3_yellow_1(X30))
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X30)))) )
      & ( r1_tarski(esk4_2(X30,X31),X30)
        | v13_waybel_0(X31,k3_yellow_1(X30))
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X30)))) )
      & ( r2_hidden(esk3_2(X30,X31),X31)
        | v13_waybel_0(X31,k3_yellow_1(X30))
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X30)))) )
      & ( ~ r2_hidden(esk4_2(X30,X31),X31)
        | v13_waybel_0(X31,k3_yellow_1(X30))
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X30)))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_waybel_7])])])])])).

cnf(c_0_59,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk5_0))))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_60,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_61,negated_conjecture,
    ( v13_waybel_0(esk7_0,k3_yellow_1(k2_struct_0(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_62,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_tops_1(X3,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_pre_topc(X3) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(esk6_0,k1_tops_1(esk5_0,X1))
    | ~ m1_connsp_2(X1,esk5_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_27]),c_0_28]),c_0_29])]),c_0_30])).

cnf(c_0_64,negated_conjecture,
    ( r1_tarski(k1_yellow19(esk5_0,esk6_0),X1)
    | m1_connsp_2(k1_tops_1(esk5_0,esk1_2(k1_yellow19(esk5_0,esk6_0),X1)),esk5_0,X2)
    | ~ r2_hidden(X2,k1_tops_1(esk5_0,esk1_2(k1_yellow19(esk5_0,esk6_0),X1)))
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_28]),c_0_29])]),c_0_30])).

cnf(c_0_65,negated_conjecture,
    ( r2_waybel_7(esk5_0,esk7_0,esk6_0)
    | r2_hidden(X1,esk7_0)
    | ~ r2_hidden(X1,k1_yellow19(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_53])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(X1,k1_yellow19(esk5_0,esk6_0))
    | ~ m1_connsp_2(X1,esk5_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_27]),c_0_28]),c_0_29])]),c_0_30])).

cnf(c_0_67,negated_conjecture,
    ( r2_waybel_7(esk5_0,X1,X2)
    | m1_connsp_2(esk2_3(esk5_0,X1,X2),esk5_0,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_68,negated_conjecture,
    ( r2_waybel_7(esk5_0,X1,X2)
    | r2_hidden(esk2_3(esk5_0,X1,X2),X3)
    | ~ r2_waybel_7(esk5_0,X3,X4)
    | ~ r2_hidden(X4,esk2_3(esk5_0,X1,X2)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_43]),c_0_28]),c_0_29])]),c_0_44])).

cnf(c_0_69,plain,
    ( r2_hidden(X4,X1)
    | ~ v13_waybel_0(X1,k3_yellow_1(X2))
    | ~ r1_tarski(X3,X4)
    | ~ r1_tarski(X4,X2)
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_70,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(esk5_0))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_28])])).

cnf(c_0_71,negated_conjecture,
    ( v13_waybel_0(esk7_0,k3_yellow_1(u1_struct_0(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_60]),c_0_28])])).

fof(c_0_72,plain,(
    ! [X36,X37] :
      ( ( ~ m1_subset_1(X36,k1_zfmisc_1(X37))
        | r1_tarski(X36,X37) )
      & ( ~ r1_tarski(X36,X37)
        | m1_subset_1(X36,k1_zfmisc_1(X37)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_73,plain,
    ( r2_hidden(k1_tops_1(X1,X2),X3)
    | ~ r2_waybel_7(X1,X3,X4)
    | ~ r2_hidden(X4,k1_tops_1(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_39]),c_0_40])).

cnf(c_0_74,negated_conjecture,
    ( r2_hidden(esk6_0,X1)
    | ~ m1_connsp_2(X1,esk5_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_28])]),c_0_41])).

cnf(c_0_75,negated_conjecture,
    ( r1_tarski(k1_yellow19(esk5_0,esk6_0),X1)
    | m1_connsp_2(k1_tops_1(esk5_0,esk1_2(k1_yellow19(esk5_0,esk6_0),X1)),esk5_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_63]),c_0_27])]),c_0_42])).

cnf(c_0_76,negated_conjecture,
    ( r2_waybel_7(esk5_0,esk7_0,esk6_0)
    | r2_hidden(X1,esk7_0)
    | ~ m1_connsp_2(X1,esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_77,negated_conjecture,
    ( r2_waybel_7(esk5_0,X1,esk6_0)
    | m1_connsp_2(esk2_3(esk5_0,X1,esk6_0),esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_67,c_0_27])).

cnf(c_0_78,negated_conjecture,
    ( r2_waybel_7(esk5_0,X1,X2)
    | r2_hidden(esk2_3(esk5_0,X1,X2),X3)
    | ~ r2_waybel_7(esk5_0,X3,X2) ),
    inference(spm,[status(thm)],[c_0_68,c_0_56])).

cnf(c_0_79,negated_conjecture,
    ( r2_hidden(X1,esk7_0)
    | ~ r1_tarski(X1,u1_struct_0(esk5_0))
    | ~ r1_tarski(X2,X1)
    | ~ r2_hidden(X2,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71])])).

cnf(c_0_80,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_81,negated_conjecture,
    ( r1_tarski(k1_yellow19(esk5_0,esk6_0),X1)
    | r2_hidden(k1_tops_1(esk5_0,esk1_2(k1_yellow19(esk5_0,esk6_0),X1)),X2)
    | ~ r2_waybel_7(esk5_0,X2,X3)
    | ~ r2_hidden(X3,k1_tops_1(esk5_0,esk1_2(k1_yellow19(esk5_0,esk6_0),X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_52]),c_0_28]),c_0_29])])).

cnf(c_0_82,negated_conjecture,
    ( r1_tarski(k1_yellow19(esk5_0,esk6_0),X1)
    | r2_hidden(esk6_0,k1_tops_1(esk5_0,esk1_2(k1_yellow19(esk5_0,esk6_0),X1))) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_83,plain,
    ( r2_waybel_7(X1,X2,X3)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_84,negated_conjecture,
    ( r2_waybel_7(esk5_0,X1,esk6_0)
    | r2_hidden(esk2_3(esk5_0,X1,esk6_0),esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_78])).

cnf(c_0_85,negated_conjecture,
    ( r2_hidden(X1,esk7_0)
    | ~ r1_tarski(X2,X1)
    | ~ r2_hidden(X2,esk7_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_86,negated_conjecture,
    ( r1_tarski(k1_yellow19(esk5_0,esk6_0),X1)
    | r2_hidden(k1_tops_1(esk5_0,esk1_2(k1_yellow19(esk5_0,esk6_0),X1)),X2)
    | ~ r2_waybel_7(esk5_0,X2,esk6_0) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_87,negated_conjecture,
    ( r2_waybel_7(esk5_0,esk7_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_28]),c_0_29])])).

cnf(c_0_88,negated_conjecture,
    ( r2_hidden(X1,esk7_0)
    | ~ r2_hidden(k1_tops_1(X2,X1),esk7_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_85,c_0_49])).

cnf(c_0_89,negated_conjecture,
    ( r1_tarski(k1_yellow19(esk5_0,esk6_0),X1)
    | r2_hidden(k1_tops_1(esk5_0,esk1_2(k1_yellow19(esk5_0,esk6_0),X1)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_90,negated_conjecture,
    ( ~ r2_waybel_7(esk5_0,esk7_0,esk6_0)
    | ~ r1_tarski(k1_yellow19(esk5_0,esk6_0),esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_91,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_92,negated_conjecture,
    ( r1_tarski(k1_yellow19(esk5_0,esk6_0),X1)
    | r2_hidden(esk1_2(k1_yellow19(esk5_0,esk6_0),X1),esk7_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_28])]),c_0_52])).

cnf(c_0_93,negated_conjecture,
    ( ~ r1_tarski(k1_yellow19(esk5_0,esk6_0),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_90,c_0_87])])).

cnf(c_0_94,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_93]),
    [proof]).

%------------------------------------------------------------------------------
