%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:50 EST 2020

% Result     : Theorem 12.06s
% Output     : CNFRefutation 12.06s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 513 expanded)
%              Number of clauses        :   81 ( 196 expanded)
%              Number of leaves         :   14 ( 127 expanded)
%              Depth                    :   17
%              Number of atoms          :  525 (3312 expanded)
%              Number of equality atoms :    7 (  40 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   28 (   4 average)
%              Maximal term depth       :    6 (   1 average)

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

fof(d2_yellow_1,axiom,(
    ! [X1] : k3_yellow_1(X1) = k3_lattice3(k1_lattice3(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_yellow_1)).

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

fof(t54_tops_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2,X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
         => ( r2_hidden(X2,k1_tops_1(X1,X3))
          <=> ? [X4] :
                ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                & v3_pre_topc(X4,X1)
                & r1_tarski(X4,X3)
                & r2_hidden(X2,X4) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_tops_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

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

fof(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk6_0)
    & v2_pre_topc(esk6_0)
    & l1_pre_topc(esk6_0)
    & m1_subset_1(esk7_0,u1_struct_0(esk6_0))
    & v13_waybel_0(esk8_0,k3_yellow_1(k2_struct_0(esk6_0)))
    & m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk6_0)))))
    & ( ~ r2_waybel_7(esk6_0,esk8_0,esk7_0)
      | ~ r1_tarski(k1_yellow19(esk6_0,esk7_0),esk8_0) )
    & ( r2_waybel_7(esk6_0,esk8_0,esk7_0)
      | r1_tarski(k1_yellow19(esk6_0,esk7_0),esk8_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).

fof(c_0_16,plain,(
    ! [X32] : k3_yellow_1(X32) = k3_lattice3(k1_lattice3(X32)) ),
    inference(variable_rename,[status(thm)],[d2_yellow_1])).

fof(c_0_17,plain,(
    ! [X16] :
      ( ~ l1_struct_0(X16)
      | k2_struct_0(X16) = u1_struct_0(X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_18,plain,(
    ! [X17] :
      ( ~ l1_pre_topc(X17)
      | l1_struct_0(X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_19,plain,(
    ! [X40,X41,X42,X43] :
      ( ( ~ v13_waybel_0(X41,k3_yellow_1(X40))
        | ~ r1_tarski(X42,X43)
        | ~ r1_tarski(X43,X40)
        | ~ r2_hidden(X42,X41)
        | r2_hidden(X43,X41)
        | ~ m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X40)))) )
      & ( r1_tarski(esk4_2(X40,X41),esk5_2(X40,X41))
        | v13_waybel_0(X41,k3_yellow_1(X40))
        | ~ m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X40)))) )
      & ( r1_tarski(esk5_2(X40,X41),X40)
        | v13_waybel_0(X41,k3_yellow_1(X40))
        | ~ m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X40)))) )
      & ( r2_hidden(esk4_2(X40,X41),X41)
        | v13_waybel_0(X41,k3_yellow_1(X40))
        | ~ m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X40)))) )
      & ( ~ r2_hidden(esk5_2(X40,X41),X41)
        | v13_waybel_0(X41,k3_yellow_1(X40))
        | ~ m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X40)))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_waybel_7])])])])])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk6_0))))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( k3_yellow_1(X1) = k3_lattice3(k1_lattice3(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( v13_waybel_0(esk8_0,k3_yellow_1(k2_struct_0(esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,plain,
    ( r2_hidden(X4,X1)
    | ~ v13_waybel_0(X1,k3_yellow_1(X2))
    | ~ r1_tarski(X3,X4)
    | ~ r1_tarski(X4,X2)
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk6_0)))))) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_27,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( l1_pre_topc(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_29,negated_conjecture,
    ( v13_waybel_0(esk8_0,k3_lattice3(k1_lattice3(k2_struct_0(esk6_0)))) ),
    inference(rw,[status(thm)],[c_0_24,c_0_21])).

fof(c_0_30,plain,(
    ! [X18,X19,X20,X22] :
      ( ( m1_subset_1(esk2_3(X18,X19,X20),k1_zfmisc_1(u1_struct_0(X18)))
        | ~ r2_hidden(X19,k1_tops_1(X18,X20))
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18) )
      & ( v3_pre_topc(esk2_3(X18,X19,X20),X18)
        | ~ r2_hidden(X19,k1_tops_1(X18,X20))
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18) )
      & ( r1_tarski(esk2_3(X18,X19,X20),X20)
        | ~ r2_hidden(X19,k1_tops_1(X18,X20))
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18) )
      & ( r2_hidden(X19,esk2_3(X18,X19,X20))
        | ~ r2_hidden(X19,k1_tops_1(X18,X20))
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18) )
      & ( ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ v3_pre_topc(X22,X18)
        | ~ r1_tarski(X22,X20)
        | ~ r2_hidden(X19,X22)
        | r2_hidden(X19,k1_tops_1(X18,X20))
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_tops_1])])])])])).

cnf(c_0_31,plain,
    ( r2_hidden(X4,X1)
    | ~ r1_tarski(X4,X2)
    | ~ r1_tarski(X3,X4)
    | ~ r2_hidden(X3,X1)
    | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_21]),c_0_21])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(esk6_0)))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])])).

cnf(c_0_33,negated_conjecture,
    ( v13_waybel_0(esk8_0,k3_lattice3(k1_lattice3(u1_struct_0(esk6_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_27]),c_0_28])])).

fof(c_0_34,plain,(
    ! [X11,X12] :
      ( ( ~ m1_subset_1(X11,k1_zfmisc_1(X12))
        | r1_tarski(X11,X12) )
      & ( ~ r1_tarski(X11,X12)
        | m1_subset_1(X11,k1_zfmisc_1(X12)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_35,plain,
    ( r2_hidden(X4,k1_tops_1(X2,X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v3_pre_topc(X1,X2)
    | ~ r1_tarski(X1,X3)
    | ~ r2_hidden(X4,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k1_tops_1(X1,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_37,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(X1,esk8_0)
    | ~ r2_hidden(X2,esk8_0)
    | ~ r1_tarski(X1,u1_struct_0(esk6_0))
    | ~ r1_tarski(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_40,plain,(
    ! [X33,X34,X35,X36,X37,X38] :
      ( ( ~ r2_waybel_7(X33,X34,X35)
        | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X33)))
        | ~ v3_pre_topc(X36,X33)
        | ~ r2_hidden(X35,X36)
        | r2_hidden(X36,X34)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) )
      & ( m1_subset_1(esk3_3(X33,X37,X38),k1_zfmisc_1(u1_struct_0(X33)))
        | r2_waybel_7(X33,X37,X38)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) )
      & ( v3_pre_topc(esk3_3(X33,X37,X38),X33)
        | r2_waybel_7(X33,X37,X38)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) )
      & ( r2_hidden(X38,esk3_3(X33,X37,X38))
        | r2_waybel_7(X33,X37,X38)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) )
      & ( ~ r2_hidden(esk3_3(X33,X37,X38),X37)
        | r2_waybel_7(X33,X37,X38)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_waybel_7])])])])])])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,k1_tops_1(X2,esk2_3(X2,X3,X4)))
    | ~ v3_pre_topc(X5,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X3,k1_tops_1(X2,X4))
    | ~ r2_hidden(X1,X5)
    | ~ r1_tarski(X5,esk2_3(X2,X3,X4)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_42,plain,
    ( v3_pre_topc(esk2_3(X1,X2,X3),X1)
    | ~ r2_hidden(X2,k1_tops_1(X1,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_44,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(X1,esk8_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk6_0)))
    | ~ r2_hidden(X2,esk8_0)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_46,plain,
    ( r2_hidden(X4,X2)
    | ~ r2_waybel_7(X1,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X4,X1)
    | ~ r2_hidden(X3,X4)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,k1_tops_1(X2,esk2_3(X2,X3,X4)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X1,esk2_3(X2,X6,X5))
    | ~ r2_hidden(X3,k1_tops_1(X2,X4))
    | ~ r2_hidden(X6,k1_tops_1(X2,X5))
    | ~ r1_tarski(esk2_3(X2,X6,X5),esk2_3(X2,X3,X4)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_36]),c_0_42])).

cnf(c_0_48,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(X1,esk8_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk6_0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,esk8_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_39])).

cnf(c_0_50,negated_conjecture,
    ( v2_pre_topc(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_51,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_52,plain,
    ( r1_tarski(esk2_3(X1,X2,X3),X3)
    | ~ r2_hidden(X2,k1_tops_1(X1,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_53,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X4)
    | ~ r2_waybel_7(X1,X4,X5)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X5,esk2_3(X1,X2,X3))
    | ~ r2_hidden(X2,k1_tops_1(X1,X3)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_36]),c_0_42])).

cnf(c_0_54,plain,
    ( r2_hidden(X1,k1_tops_1(X2,esk2_3(X2,X3,X4)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X1,esk2_3(X2,X3,X4))
    | ~ r2_hidden(X3,k1_tops_1(X2,X4)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

fof(c_0_55,plain,(
    ! [X46,X47,X48] :
      ( ( ~ r2_hidden(X48,k1_yellow19(X46,X47))
        | m1_connsp_2(X48,X46,X47)
        | ~ m1_subset_1(X47,u1_struct_0(X46))
        | v2_struct_0(X46)
        | ~ v2_pre_topc(X46)
        | ~ l1_pre_topc(X46) )
      & ( ~ m1_connsp_2(X48,X46,X47)
        | r2_hidden(X48,k1_yellow19(X46,X47))
        | ~ m1_subset_1(X47,u1_struct_0(X46))
        | v2_struct_0(X46)
        | ~ v2_pre_topc(X46)
        | ~ l1_pre_topc(X46) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_yellow19])])])])])).

fof(c_0_56,plain,(
    ! [X29,X30,X31] :
      ( v2_struct_0(X29)
      | ~ v2_pre_topc(X29)
      | ~ l1_pre_topc(X29)
      | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))
      | ~ m1_subset_1(X31,u1_struct_0(X29))
      | ~ v3_pre_topc(X30,X29)
      | ~ r2_hidden(X31,X30)
      | m1_connsp_2(X30,X29,X31) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t5_connsp_2])])])])).

fof(c_0_57,plain,(
    ! [X13,X14,X15] :
      ( ~ r2_hidden(X13,X14)
      | ~ m1_subset_1(X14,k1_zfmisc_1(X15))
      | m1_subset_1(X13,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(esk2_3(esk6_0,X1,X2),esk8_0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(esk2_3(esk6_0,X1,X2)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk6_0)))
    | ~ r2_hidden(X1,k1_tops_1(esk6_0,X2))
    | ~ r2_hidden(X3,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_36]),c_0_50]),c_0_28])])).

cnf(c_0_59,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),k1_zfmisc_1(X3))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k1_tops_1(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_60,plain,
    ( r2_hidden(esk2_3(X1,X2,esk2_3(X1,X3,X4)),X5)
    | ~ r2_waybel_7(X1,X5,X6)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X6,esk2_3(X1,X2,esk2_3(X1,X3,X4)))
    | ~ r2_hidden(X2,k1_tops_1(X1,esk2_3(X1,X3,X4)))
    | ~ r2_hidden(X3,k1_tops_1(X1,X4)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_36])).

cnf(c_0_61,plain,
    ( r2_hidden(X1,esk2_3(X2,X1,X3))
    | ~ r2_hidden(X1,k1_tops_1(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_62,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_63,plain,
    ( r1_tarski(X1,k1_tops_1(X2,esk2_3(X2,X3,X4)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(esk1_2(X1,k1_tops_1(X2,esk2_3(X2,X3,X4))),esk2_3(X2,X3,X4))
    | ~ r2_hidden(X3,k1_tops_1(X2,X4)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_54])).

cnf(c_0_64,plain,
    ( r2_hidden(X1,k1_yellow19(X2,X3))
    | v2_struct_0(X2)
    | ~ m1_connsp_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_65,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_66,negated_conjecture,
    ( ~ v2_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_67,plain,
    ( v2_struct_0(X1)
    | m1_connsp_2(X2,X1,X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v3_pre_topc(X2,X1)
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_68,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_69,plain,
    ( m1_subset_1(esk3_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | r2_waybel_7(X1,X2,X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_70,plain,
    ( v3_pre_topc(esk3_3(X1,X2,X3),X1)
    | r2_waybel_7(X1,X2,X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_71,negated_conjecture,
    ( r2_hidden(esk2_3(esk6_0,X1,X2),esk8_0)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(esk2_3(esk6_0,X1,X2),k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk6_0)))
    | ~ r2_hidden(esk2_3(X3,X4,esk2_3(esk6_0,X1,X2)),esk8_0)
    | ~ r2_hidden(X4,k1_tops_1(X3,esk2_3(esk6_0,X1,X2)))
    | ~ r2_hidden(X1,k1_tops_1(esk6_0,X2)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_72,plain,
    ( r2_hidden(esk2_3(X1,X2,esk2_3(X1,X3,X4)),X5)
    | ~ r2_waybel_7(X1,X5,X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k1_tops_1(X1,esk2_3(X1,X3,X4)))
    | ~ r2_hidden(X3,k1_tops_1(X1,X4)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_36])).

cnf(c_0_73,plain,
    ( r2_hidden(X1,X2)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ r2_hidden(X1,k1_tops_1(X3,X4))
    | ~ r1_tarski(esk2_3(X3,X1,X4),X2) ),
    inference(spm,[status(thm)],[c_0_62,c_0_61])).

cnf(c_0_74,plain,
    ( r1_tarski(esk2_3(X1,X2,X3),k1_tops_1(X1,esk2_3(X1,X2,X3)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k1_tops_1(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_44])).

cnf(c_0_75,negated_conjecture,
    ( r2_hidden(X1,k1_yellow19(esk6_0,esk7_0))
    | ~ m1_connsp_2(X1,esk6_0,esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_50]),c_0_28])]),c_0_66])).

cnf(c_0_76,plain,
    ( m1_connsp_2(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ v3_pre_topc(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X3,X1) ),
    inference(csr,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_77,negated_conjecture,
    ( r2_waybel_7(esk6_0,X1,X2)
    | m1_subset_1(esk3_3(esk6_0,X1,X2),k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_50]),c_0_28])])).

cnf(c_0_78,negated_conjecture,
    ( r2_waybel_7(esk6_0,X1,X2)
    | v3_pre_topc(esk3_3(esk6_0,X1,X2),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_50]),c_0_28])])).

cnf(c_0_79,plain,
    ( r2_hidden(X1,esk3_3(X2,X3,X1))
    | r2_waybel_7(X2,X3,X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_80,negated_conjecture,
    ( r2_hidden(esk2_3(esk6_0,X1,X2),esk8_0)
    | ~ r2_waybel_7(esk6_0,esk8_0,X3)
    | ~ m1_subset_1(esk2_3(esk6_0,X1,X2),k1_zfmisc_1(u1_struct_0(esk6_0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk6_0)))
    | ~ r2_hidden(X3,k1_tops_1(esk6_0,esk2_3(esk6_0,X1,X2)))
    | ~ r2_hidden(X1,k1_tops_1(esk6_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_50]),c_0_28])])).

cnf(c_0_81,plain,
    ( r2_hidden(X1,k1_tops_1(X2,esk2_3(X2,X1,X3)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X1,k1_tops_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

fof(c_0_82,plain,(
    ! [X23,X24,X25] :
      ( ( ~ m1_connsp_2(X25,X23,X24)
        | r2_hidden(X24,k1_tops_1(X23,X25))
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))
        | ~ m1_subset_1(X24,u1_struct_0(X23))
        | v2_struct_0(X23)
        | ~ v2_pre_topc(X23)
        | ~ l1_pre_topc(X23) )
      & ( ~ r2_hidden(X24,k1_tops_1(X23,X25))
        | m1_connsp_2(X25,X23,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))
        | ~ m1_subset_1(X24,u1_struct_0(X23))
        | v2_struct_0(X23)
        | ~ v2_pre_topc(X23)
        | ~ l1_pre_topc(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_connsp_2])])])])])).

fof(c_0_83,plain,(
    ! [X26,X27,X28] :
      ( v2_struct_0(X26)
      | ~ v2_pre_topc(X26)
      | ~ l1_pre_topc(X26)
      | ~ m1_subset_1(X27,u1_struct_0(X26))
      | ~ m1_connsp_2(X28,X26,X27)
      | m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m1_connsp_2])])])])).

cnf(c_0_84,negated_conjecture,
    ( r2_hidden(X1,X2)
    | ~ m1_connsp_2(X1,esk6_0,esk7_0)
    | ~ r1_tarski(k1_yellow19(esk6_0,esk7_0),X2) ),
    inference(spm,[status(thm)],[c_0_62,c_0_75])).

cnf(c_0_85,negated_conjecture,
    ( r2_waybel_7(esk6_0,esk8_0,esk7_0)
    | r1_tarski(k1_yellow19(esk6_0,esk7_0),esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_86,negated_conjecture,
    ( r2_waybel_7(esk6_0,X1,X2)
    | m1_connsp_2(esk3_3(esk6_0,X1,X2),esk6_0,X3)
    | ~ r2_hidden(X3,esk3_3(esk6_0,X1,X2)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_50]),c_0_28])]),c_0_66]),c_0_78])).

cnf(c_0_87,negated_conjecture,
    ( r2_waybel_7(esk6_0,X1,X2)
    | r2_hidden(X2,esk3_3(esk6_0,X1,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_50]),c_0_28])])).

cnf(c_0_88,negated_conjecture,
    ( r2_hidden(esk2_3(esk6_0,X1,X2),esk8_0)
    | ~ r2_waybel_7(esk6_0,esk8_0,X1)
    | ~ m1_subset_1(esk2_3(esk6_0,X1,X2),k1_zfmisc_1(u1_struct_0(esk6_0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk6_0)))
    | ~ r2_hidden(X1,k1_tops_1(esk6_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_50]),c_0_28])])).

cnf(c_0_89,plain,
    ( r2_hidden(X3,k1_tops_1(X2,X1))
    | v2_struct_0(X2)
    | ~ m1_connsp_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_90,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_91,negated_conjecture,
    ( r2_waybel_7(esk6_0,esk8_0,esk7_0)
    | r2_hidden(X1,esk8_0)
    | ~ m1_connsp_2(X1,esk6_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_92,negated_conjecture,
    ( r2_waybel_7(esk6_0,X1,X2)
    | m1_connsp_2(esk3_3(esk6_0,X1,X2),esk6_0,X2) ),
    inference(spm,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_93,negated_conjecture,
    ( r2_hidden(X1,esk8_0)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk6_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(esk2_3(X2,X3,X1),esk8_0)
    | ~ r2_hidden(X3,k1_tops_1(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_52])).

cnf(c_0_94,negated_conjecture,
    ( r2_hidden(esk2_3(esk6_0,X1,X2),esk8_0)
    | ~ r2_waybel_7(esk6_0,esk8_0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk6_0)))
    | ~ r2_hidden(X1,k1_tops_1(esk6_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_36]),c_0_50]),c_0_28])])).

cnf(c_0_95,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,k1_tops_1(X1,X3))
    | ~ m1_connsp_2(X3,X1,X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_96,plain,
    ( r2_waybel_7(X1,X2,X3)
    | ~ r2_hidden(esk3_3(X1,X2,X3),X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_97,negated_conjecture,
    ( r2_waybel_7(esk6_0,esk8_0,esk7_0)
    | r2_waybel_7(esk6_0,X1,esk7_0)
    | r2_hidden(esk3_3(esk6_0,X1,esk7_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_91,c_0_92])).

cnf(c_0_98,plain,
    ( m1_connsp_2(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,k1_yellow19(X2,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_99,negated_conjecture,
    ( r2_hidden(X1,esk8_0)
    | ~ r2_waybel_7(esk6_0,esk8_0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk6_0)))
    | ~ r2_hidden(X2,k1_tops_1(esk6_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_50]),c_0_28])])).

cnf(c_0_100,negated_conjecture,
    ( r2_hidden(esk7_0,k1_tops_1(esk6_0,X1))
    | ~ m1_connsp_2(X1,esk6_0,esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_65]),c_0_50]),c_0_28])]),c_0_66])).

cnf(c_0_101,negated_conjecture,
    ( r2_waybel_7(esk6_0,esk8_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_50]),c_0_28])])).

cnf(c_0_102,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk6_0)))
    | ~ m1_connsp_2(X1,esk6_0,esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_65]),c_0_50]),c_0_28])]),c_0_66])).

cnf(c_0_103,plain,
    ( m1_connsp_2(esk1_2(k1_yellow19(X1,X2),X3),X1,X2)
    | v2_struct_0(X1)
    | r1_tarski(k1_yellow19(X1,X2),X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_98,c_0_44])).

cnf(c_0_104,negated_conjecture,
    ( r2_hidden(X1,esk8_0)
    | ~ m1_connsp_2(X1,esk6_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_100]),c_0_101])]),c_0_102])).

cnf(c_0_105,negated_conjecture,
    ( m1_connsp_2(esk1_2(k1_yellow19(esk6_0,esk7_0),X1),esk6_0,esk7_0)
    | r1_tarski(k1_yellow19(esk6_0,esk7_0),X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_65]),c_0_50]),c_0_28])]),c_0_66])).

cnf(c_0_106,negated_conjecture,
    ( ~ r2_waybel_7(esk6_0,esk8_0,esk7_0)
    | ~ r1_tarski(k1_yellow19(esk6_0,esk7_0),esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_107,negated_conjecture,
    ( r2_hidden(esk1_2(k1_yellow19(esk6_0,esk7_0),X1),esk8_0)
    | r1_tarski(k1_yellow19(esk6_0,esk7_0),X1) ),
    inference(spm,[status(thm)],[c_0_104,c_0_105])).

cnf(c_0_108,negated_conjecture,
    ( ~ r1_tarski(k1_yellow19(esk6_0,esk7_0),esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_106,c_0_101])])).

cnf(c_0_109,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_107]),c_0_108]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:11:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 12.06/12.30  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 12.06/12.30  # and selection function PSelectComplexExceptUniqMaxHorn.
% 12.06/12.30  #
% 12.06/12.30  # Preprocessing time       : 0.030 s
% 12.06/12.30  
% 12.06/12.30  # Proof found!
% 12.06/12.30  # SZS status Theorem
% 12.06/12.30  # SZS output start CNFRefutation
% 12.06/12.30  fof(t4_yellow19, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:((v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X1)))&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))))=>(r2_waybel_7(X1,X3,X2)<=>r1_tarski(k1_yellow19(X1,X2),X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_yellow19)).
% 12.06/12.30  fof(d2_yellow_1, axiom, ![X1]:k3_yellow_1(X1)=k3_lattice3(k1_lattice3(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_yellow_1)).
% 12.06/12.30  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 12.06/12.30  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 12.06/12.30  fof(t11_waybel_7, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))=>(v13_waybel_0(X2,k3_yellow_1(X1))<=>![X3, X4]:(((r1_tarski(X3,X4)&r1_tarski(X4,X1))&r2_hidden(X3,X2))=>r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_waybel_7)).
% 12.06/12.30  fof(t54_tops_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X2,k1_tops_1(X1,X3))<=>?[X4]:(((m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))&v3_pre_topc(X4,X1))&r1_tarski(X4,X3))&r2_hidden(X2,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_tops_1)).
% 12.06/12.30  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 12.06/12.30  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 12.06/12.30  fof(d5_waybel_7, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2, X3]:(r2_waybel_7(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>((v3_pre_topc(X4,X1)&r2_hidden(X3,X4))=>r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_waybel_7)).
% 12.06/12.30  fof(t3_yellow19, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(r2_hidden(X3,k1_yellow19(X1,X2))<=>m1_connsp_2(X3,X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_yellow19)).
% 12.06/12.30  fof(t5_connsp_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>((v3_pre_topc(X2,X1)&r2_hidden(X3,X2))=>m1_connsp_2(X2,X1,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_connsp_2)).
% 12.06/12.30  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 12.06/12.30  fof(d1_connsp_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(m1_connsp_2(X3,X1,X2)<=>r2_hidden(X2,k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_connsp_2)).
% 12.06/12.30  fof(dt_m1_connsp_2, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>![X3]:(m1_connsp_2(X3,X1,X2)=>m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 12.06/12.30  fof(c_0_14, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:((v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X1)))&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))))=>(r2_waybel_7(X1,X3,X2)<=>r1_tarski(k1_yellow19(X1,X2),X3)))))), inference(assume_negation,[status(cth)],[t4_yellow19])).
% 12.06/12.30  fof(c_0_15, negated_conjecture, (((~v2_struct_0(esk6_0)&v2_pre_topc(esk6_0))&l1_pre_topc(esk6_0))&(m1_subset_1(esk7_0,u1_struct_0(esk6_0))&((v13_waybel_0(esk8_0,k3_yellow_1(k2_struct_0(esk6_0)))&m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk6_0))))))&((~r2_waybel_7(esk6_0,esk8_0,esk7_0)|~r1_tarski(k1_yellow19(esk6_0,esk7_0),esk8_0))&(r2_waybel_7(esk6_0,esk8_0,esk7_0)|r1_tarski(k1_yellow19(esk6_0,esk7_0),esk8_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).
% 12.06/12.30  fof(c_0_16, plain, ![X32]:k3_yellow_1(X32)=k3_lattice3(k1_lattice3(X32)), inference(variable_rename,[status(thm)],[d2_yellow_1])).
% 12.06/12.30  fof(c_0_17, plain, ![X16]:(~l1_struct_0(X16)|k2_struct_0(X16)=u1_struct_0(X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 12.06/12.30  fof(c_0_18, plain, ![X17]:(~l1_pre_topc(X17)|l1_struct_0(X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 12.06/12.30  fof(c_0_19, plain, ![X40, X41, X42, X43]:((~v13_waybel_0(X41,k3_yellow_1(X40))|(~r1_tarski(X42,X43)|~r1_tarski(X43,X40)|~r2_hidden(X42,X41)|r2_hidden(X43,X41))|~m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X40)))))&((((r1_tarski(esk4_2(X40,X41),esk5_2(X40,X41))|v13_waybel_0(X41,k3_yellow_1(X40))|~m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X40)))))&(r1_tarski(esk5_2(X40,X41),X40)|v13_waybel_0(X41,k3_yellow_1(X40))|~m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X40))))))&(r2_hidden(esk4_2(X40,X41),X41)|v13_waybel_0(X41,k3_yellow_1(X40))|~m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X40))))))&(~r2_hidden(esk5_2(X40,X41),X41)|v13_waybel_0(X41,k3_yellow_1(X40))|~m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X40))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_waybel_7])])])])])).
% 12.06/12.30  cnf(c_0_20, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk6_0)))))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 12.06/12.30  cnf(c_0_21, plain, (k3_yellow_1(X1)=k3_lattice3(k1_lattice3(X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 12.06/12.30  cnf(c_0_22, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 12.06/12.30  cnf(c_0_23, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 12.06/12.30  cnf(c_0_24, negated_conjecture, (v13_waybel_0(esk8_0,k3_yellow_1(k2_struct_0(esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 12.06/12.30  cnf(c_0_25, plain, (r2_hidden(X4,X1)|~v13_waybel_0(X1,k3_yellow_1(X2))|~r1_tarski(X3,X4)|~r1_tarski(X4,X2)|~r2_hidden(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2))))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 12.06/12.30  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk6_0))))))), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 12.06/12.30  cnf(c_0_27, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 12.06/12.30  cnf(c_0_28, negated_conjecture, (l1_pre_topc(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 12.06/12.30  cnf(c_0_29, negated_conjecture, (v13_waybel_0(esk8_0,k3_lattice3(k1_lattice3(k2_struct_0(esk6_0))))), inference(rw,[status(thm)],[c_0_24, c_0_21])).
% 12.06/12.30  fof(c_0_30, plain, ![X18, X19, X20, X22]:(((((m1_subset_1(esk2_3(X18,X19,X20),k1_zfmisc_1(u1_struct_0(X18)))|~r2_hidden(X19,k1_tops_1(X18,X20))|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))|(~v2_pre_topc(X18)|~l1_pre_topc(X18)))&(v3_pre_topc(esk2_3(X18,X19,X20),X18)|~r2_hidden(X19,k1_tops_1(X18,X20))|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))|(~v2_pre_topc(X18)|~l1_pre_topc(X18))))&(r1_tarski(esk2_3(X18,X19,X20),X20)|~r2_hidden(X19,k1_tops_1(X18,X20))|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))|(~v2_pre_topc(X18)|~l1_pre_topc(X18))))&(r2_hidden(X19,esk2_3(X18,X19,X20))|~r2_hidden(X19,k1_tops_1(X18,X20))|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))|(~v2_pre_topc(X18)|~l1_pre_topc(X18))))&(~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X18)))|~v3_pre_topc(X22,X18)|~r1_tarski(X22,X20)|~r2_hidden(X19,X22)|r2_hidden(X19,k1_tops_1(X18,X20))|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))|(~v2_pre_topc(X18)|~l1_pre_topc(X18)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_tops_1])])])])])).
% 12.06/12.30  cnf(c_0_31, plain, (r2_hidden(X4,X1)|~r1_tarski(X4,X2)|~r1_tarski(X3,X4)|~r2_hidden(X3,X1)|~v13_waybel_0(X1,k3_lattice3(k1_lattice3(X2)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_21]), c_0_21])).
% 12.06/12.30  cnf(c_0_32, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(esk6_0))))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28])])).
% 12.06/12.30  cnf(c_0_33, negated_conjecture, (v13_waybel_0(esk8_0,k3_lattice3(k1_lattice3(u1_struct_0(esk6_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_27]), c_0_28])])).
% 12.06/12.30  fof(c_0_34, plain, ![X11, X12]:((~m1_subset_1(X11,k1_zfmisc_1(X12))|r1_tarski(X11,X12))&(~r1_tarski(X11,X12)|m1_subset_1(X11,k1_zfmisc_1(X12)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 12.06/12.30  cnf(c_0_35, plain, (r2_hidden(X4,k1_tops_1(X2,X3))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v3_pre_topc(X1,X2)|~r1_tarski(X1,X3)|~r2_hidden(X4,X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 12.06/12.30  cnf(c_0_36, plain, (m1_subset_1(esk2_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(X2,k1_tops_1(X1,X3))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 12.06/12.30  fof(c_0_37, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 12.06/12.30  cnf(c_0_38, negated_conjecture, (r2_hidden(X1,esk8_0)|~r2_hidden(X2,esk8_0)|~r1_tarski(X1,u1_struct_0(esk6_0))|~r1_tarski(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33])])).
% 12.06/12.30  cnf(c_0_39, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 12.06/12.30  fof(c_0_40, plain, ![X33, X34, X35, X36, X37, X38]:((~r2_waybel_7(X33,X34,X35)|(~m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X33)))|(~v3_pre_topc(X36,X33)|~r2_hidden(X35,X36)|r2_hidden(X36,X34)))|(~v2_pre_topc(X33)|~l1_pre_topc(X33)))&((m1_subset_1(esk3_3(X33,X37,X38),k1_zfmisc_1(u1_struct_0(X33)))|r2_waybel_7(X33,X37,X38)|(~v2_pre_topc(X33)|~l1_pre_topc(X33)))&(((v3_pre_topc(esk3_3(X33,X37,X38),X33)|r2_waybel_7(X33,X37,X38)|(~v2_pre_topc(X33)|~l1_pre_topc(X33)))&(r2_hidden(X38,esk3_3(X33,X37,X38))|r2_waybel_7(X33,X37,X38)|(~v2_pre_topc(X33)|~l1_pre_topc(X33))))&(~r2_hidden(esk3_3(X33,X37,X38),X37)|r2_waybel_7(X33,X37,X38)|(~v2_pre_topc(X33)|~l1_pre_topc(X33)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_waybel_7])])])])])])).
% 12.06/12.30  cnf(c_0_41, plain, (r2_hidden(X1,k1_tops_1(X2,esk2_3(X2,X3,X4)))|~v3_pre_topc(X5,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|~r2_hidden(X3,k1_tops_1(X2,X4))|~r2_hidden(X1,X5)|~r1_tarski(X5,esk2_3(X2,X3,X4))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 12.06/12.30  cnf(c_0_42, plain, (v3_pre_topc(esk2_3(X1,X2,X3),X1)|~r2_hidden(X2,k1_tops_1(X1,X3))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 12.06/12.30  cnf(c_0_43, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 12.06/12.30  cnf(c_0_44, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 12.06/12.30  cnf(c_0_45, negated_conjecture, (r2_hidden(X1,esk8_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk6_0)))|~r2_hidden(X2,esk8_0)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 12.06/12.30  cnf(c_0_46, plain, (r2_hidden(X4,X2)|~r2_waybel_7(X1,X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))|~v3_pre_topc(X4,X1)|~r2_hidden(X3,X4)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 12.06/12.30  cnf(c_0_47, plain, (r2_hidden(X1,k1_tops_1(X2,esk2_3(X2,X3,X4)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))|~r2_hidden(X1,esk2_3(X2,X6,X5))|~r2_hidden(X3,k1_tops_1(X2,X4))|~r2_hidden(X6,k1_tops_1(X2,X5))|~r1_tarski(esk2_3(X2,X6,X5),esk2_3(X2,X3,X4))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_36]), c_0_42])).
% 12.06/12.30  cnf(c_0_48, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 12.06/12.30  cnf(c_0_49, negated_conjecture, (r2_hidden(X1,esk8_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk6_0)))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r2_hidden(X2,esk8_0)), inference(spm,[status(thm)],[c_0_45, c_0_39])).
% 12.06/12.30  cnf(c_0_50, negated_conjecture, (v2_pre_topc(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 12.06/12.30  cnf(c_0_51, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 12.06/12.30  cnf(c_0_52, plain, (r1_tarski(esk2_3(X1,X2,X3),X3)|~r2_hidden(X2,k1_tops_1(X1,X3))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 12.06/12.30  cnf(c_0_53, plain, (r2_hidden(esk2_3(X1,X2,X3),X4)|~r2_waybel_7(X1,X4,X5)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(X5,esk2_3(X1,X2,X3))|~r2_hidden(X2,k1_tops_1(X1,X3))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_36]), c_0_42])).
% 12.06/12.30  cnf(c_0_54, plain, (r2_hidden(X1,k1_tops_1(X2,esk2_3(X2,X3,X4)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|~r2_hidden(X1,esk2_3(X2,X3,X4))|~r2_hidden(X3,k1_tops_1(X2,X4))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 12.06/12.30  fof(c_0_55, plain, ![X46, X47, X48]:((~r2_hidden(X48,k1_yellow19(X46,X47))|m1_connsp_2(X48,X46,X47)|~m1_subset_1(X47,u1_struct_0(X46))|(v2_struct_0(X46)|~v2_pre_topc(X46)|~l1_pre_topc(X46)))&(~m1_connsp_2(X48,X46,X47)|r2_hidden(X48,k1_yellow19(X46,X47))|~m1_subset_1(X47,u1_struct_0(X46))|(v2_struct_0(X46)|~v2_pre_topc(X46)|~l1_pre_topc(X46)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_yellow19])])])])])).
% 12.06/12.30  fof(c_0_56, plain, ![X29, X30, X31]:(v2_struct_0(X29)|~v2_pre_topc(X29)|~l1_pre_topc(X29)|(~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))|(~m1_subset_1(X31,u1_struct_0(X29))|(~v3_pre_topc(X30,X29)|~r2_hidden(X31,X30)|m1_connsp_2(X30,X29,X31))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t5_connsp_2])])])])).
% 12.06/12.30  fof(c_0_57, plain, ![X13, X14, X15]:(~r2_hidden(X13,X14)|~m1_subset_1(X14,k1_zfmisc_1(X15))|m1_subset_1(X13,X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 12.06/12.30  cnf(c_0_58, negated_conjecture, (r2_hidden(esk2_3(esk6_0,X1,X2),esk8_0)|~m1_subset_1(X3,k1_zfmisc_1(esk2_3(esk6_0,X1,X2)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk6_0)))|~r2_hidden(X1,k1_tops_1(esk6_0,X2))|~r2_hidden(X3,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_36]), c_0_50]), c_0_28])])).
% 12.06/12.30  cnf(c_0_59, plain, (m1_subset_1(esk2_3(X1,X2,X3),k1_zfmisc_1(X3))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(X2,k1_tops_1(X1,X3))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 12.06/12.30  cnf(c_0_60, plain, (r2_hidden(esk2_3(X1,X2,esk2_3(X1,X3,X4)),X5)|~r2_waybel_7(X1,X5,X6)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(X6,esk2_3(X1,X2,esk2_3(X1,X3,X4)))|~r2_hidden(X2,k1_tops_1(X1,esk2_3(X1,X3,X4)))|~r2_hidden(X3,k1_tops_1(X1,X4))), inference(spm,[status(thm)],[c_0_53, c_0_36])).
% 12.06/12.30  cnf(c_0_61, plain, (r2_hidden(X1,esk2_3(X2,X1,X3))|~r2_hidden(X1,k1_tops_1(X2,X3))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 12.06/12.30  cnf(c_0_62, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 12.06/12.30  cnf(c_0_63, plain, (r1_tarski(X1,k1_tops_1(X2,esk2_3(X2,X3,X4)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|~r2_hidden(esk1_2(X1,k1_tops_1(X2,esk2_3(X2,X3,X4))),esk2_3(X2,X3,X4))|~r2_hidden(X3,k1_tops_1(X2,X4))), inference(spm,[status(thm)],[c_0_43, c_0_54])).
% 12.06/12.30  cnf(c_0_64, plain, (r2_hidden(X1,k1_yellow19(X2,X3))|v2_struct_0(X2)|~m1_connsp_2(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X2))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 12.06/12.30  cnf(c_0_65, negated_conjecture, (m1_subset_1(esk7_0,u1_struct_0(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 12.06/12.30  cnf(c_0_66, negated_conjecture, (~v2_struct_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 12.06/12.30  cnf(c_0_67, plain, (v2_struct_0(X1)|m1_connsp_2(X2,X1,X3)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,u1_struct_0(X1))|~v3_pre_topc(X2,X1)|~r2_hidden(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 12.06/12.30  cnf(c_0_68, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 12.06/12.30  cnf(c_0_69, plain, (m1_subset_1(esk3_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|r2_waybel_7(X1,X2,X3)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 12.06/12.30  cnf(c_0_70, plain, (v3_pre_topc(esk3_3(X1,X2,X3),X1)|r2_waybel_7(X1,X2,X3)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 12.06/12.30  cnf(c_0_71, negated_conjecture, (r2_hidden(esk2_3(esk6_0,X1,X2),esk8_0)|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~m1_subset_1(esk2_3(esk6_0,X1,X2),k1_zfmisc_1(u1_struct_0(X3)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk6_0)))|~r2_hidden(esk2_3(X3,X4,esk2_3(esk6_0,X1,X2)),esk8_0)|~r2_hidden(X4,k1_tops_1(X3,esk2_3(esk6_0,X1,X2)))|~r2_hidden(X1,k1_tops_1(esk6_0,X2))), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 12.06/12.30  cnf(c_0_72, plain, (r2_hidden(esk2_3(X1,X2,esk2_3(X1,X3,X4)),X5)|~r2_waybel_7(X1,X5,X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(X2,k1_tops_1(X1,esk2_3(X1,X3,X4)))|~r2_hidden(X3,k1_tops_1(X1,X4))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_36])).
% 12.06/12.30  cnf(c_0_73, plain, (r2_hidden(X1,X2)|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))|~r2_hidden(X1,k1_tops_1(X3,X4))|~r1_tarski(esk2_3(X3,X1,X4),X2)), inference(spm,[status(thm)],[c_0_62, c_0_61])).
% 12.06/12.30  cnf(c_0_74, plain, (r1_tarski(esk2_3(X1,X2,X3),k1_tops_1(X1,esk2_3(X1,X2,X3)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(X2,k1_tops_1(X1,X3))), inference(spm,[status(thm)],[c_0_63, c_0_44])).
% 12.06/12.30  cnf(c_0_75, negated_conjecture, (r2_hidden(X1,k1_yellow19(esk6_0,esk7_0))|~m1_connsp_2(X1,esk6_0,esk7_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_50]), c_0_28])]), c_0_66])).
% 12.06/12.30  cnf(c_0_76, plain, (m1_connsp_2(X1,X2,X3)|v2_struct_0(X2)|~v3_pre_topc(X1,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~r2_hidden(X3,X1)), inference(csr,[status(thm)],[c_0_67, c_0_68])).
% 12.06/12.30  cnf(c_0_77, negated_conjecture, (r2_waybel_7(esk6_0,X1,X2)|m1_subset_1(esk3_3(esk6_0,X1,X2),k1_zfmisc_1(u1_struct_0(esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_50]), c_0_28])])).
% 12.06/12.30  cnf(c_0_78, negated_conjecture, (r2_waybel_7(esk6_0,X1,X2)|v3_pre_topc(esk3_3(esk6_0,X1,X2),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_50]), c_0_28])])).
% 12.06/12.30  cnf(c_0_79, plain, (r2_hidden(X1,esk3_3(X2,X3,X1))|r2_waybel_7(X2,X3,X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 12.06/12.30  cnf(c_0_80, negated_conjecture, (r2_hidden(esk2_3(esk6_0,X1,X2),esk8_0)|~r2_waybel_7(esk6_0,esk8_0,X3)|~m1_subset_1(esk2_3(esk6_0,X1,X2),k1_zfmisc_1(u1_struct_0(esk6_0)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk6_0)))|~r2_hidden(X3,k1_tops_1(esk6_0,esk2_3(esk6_0,X1,X2)))|~r2_hidden(X1,k1_tops_1(esk6_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_50]), c_0_28])])).
% 12.06/12.30  cnf(c_0_81, plain, (r2_hidden(X1,k1_tops_1(X2,esk2_3(X2,X1,X3)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~r2_hidden(X1,k1_tops_1(X2,X3))), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 12.06/12.30  fof(c_0_82, plain, ![X23, X24, X25]:((~m1_connsp_2(X25,X23,X24)|r2_hidden(X24,k1_tops_1(X23,X25))|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))|~m1_subset_1(X24,u1_struct_0(X23))|(v2_struct_0(X23)|~v2_pre_topc(X23)|~l1_pre_topc(X23)))&(~r2_hidden(X24,k1_tops_1(X23,X25))|m1_connsp_2(X25,X23,X24)|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))|~m1_subset_1(X24,u1_struct_0(X23))|(v2_struct_0(X23)|~v2_pre_topc(X23)|~l1_pre_topc(X23)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_connsp_2])])])])])).
% 12.06/12.30  fof(c_0_83, plain, ![X26, X27, X28]:(v2_struct_0(X26)|~v2_pre_topc(X26)|~l1_pre_topc(X26)|~m1_subset_1(X27,u1_struct_0(X26))|(~m1_connsp_2(X28,X26,X27)|m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m1_connsp_2])])])])).
% 12.06/12.30  cnf(c_0_84, negated_conjecture, (r2_hidden(X1,X2)|~m1_connsp_2(X1,esk6_0,esk7_0)|~r1_tarski(k1_yellow19(esk6_0,esk7_0),X2)), inference(spm,[status(thm)],[c_0_62, c_0_75])).
% 12.06/12.30  cnf(c_0_85, negated_conjecture, (r2_waybel_7(esk6_0,esk8_0,esk7_0)|r1_tarski(k1_yellow19(esk6_0,esk7_0),esk8_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 12.06/12.30  cnf(c_0_86, negated_conjecture, (r2_waybel_7(esk6_0,X1,X2)|m1_connsp_2(esk3_3(esk6_0,X1,X2),esk6_0,X3)|~r2_hidden(X3,esk3_3(esk6_0,X1,X2))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_50]), c_0_28])]), c_0_66]), c_0_78])).
% 12.06/12.30  cnf(c_0_87, negated_conjecture, (r2_waybel_7(esk6_0,X1,X2)|r2_hidden(X2,esk3_3(esk6_0,X1,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_50]), c_0_28])])).
% 12.06/12.30  cnf(c_0_88, negated_conjecture, (r2_hidden(esk2_3(esk6_0,X1,X2),esk8_0)|~r2_waybel_7(esk6_0,esk8_0,X1)|~m1_subset_1(esk2_3(esk6_0,X1,X2),k1_zfmisc_1(u1_struct_0(esk6_0)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk6_0)))|~r2_hidden(X1,k1_tops_1(esk6_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_50]), c_0_28])])).
% 12.06/12.30  cnf(c_0_89, plain, (r2_hidden(X3,k1_tops_1(X2,X1))|v2_struct_0(X2)|~m1_connsp_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,u1_struct_0(X2))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_82])).
% 12.06/12.30  cnf(c_0_90, plain, (v2_struct_0(X1)|m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_connsp_2(X3,X1,X2)), inference(split_conjunct,[status(thm)],[c_0_83])).
% 12.06/12.30  cnf(c_0_91, negated_conjecture, (r2_waybel_7(esk6_0,esk8_0,esk7_0)|r2_hidden(X1,esk8_0)|~m1_connsp_2(X1,esk6_0,esk7_0)), inference(spm,[status(thm)],[c_0_84, c_0_85])).
% 12.06/12.30  cnf(c_0_92, negated_conjecture, (r2_waybel_7(esk6_0,X1,X2)|m1_connsp_2(esk3_3(esk6_0,X1,X2),esk6_0,X2)), inference(spm,[status(thm)],[c_0_86, c_0_87])).
% 12.06/12.30  cnf(c_0_93, negated_conjecture, (r2_hidden(X1,esk8_0)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk6_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~r2_hidden(esk2_3(X2,X3,X1),esk8_0)|~r2_hidden(X3,k1_tops_1(X2,X1))), inference(spm,[status(thm)],[c_0_45, c_0_52])).
% 12.06/12.30  cnf(c_0_94, negated_conjecture, (r2_hidden(esk2_3(esk6_0,X1,X2),esk8_0)|~r2_waybel_7(esk6_0,esk8_0,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk6_0)))|~r2_hidden(X1,k1_tops_1(esk6_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_36]), c_0_50]), c_0_28])])).
% 12.06/12.30  cnf(c_0_95, plain, (v2_struct_0(X1)|r2_hidden(X2,k1_tops_1(X1,X3))|~m1_connsp_2(X3,X1,X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(csr,[status(thm)],[c_0_89, c_0_90])).
% 12.06/12.30  cnf(c_0_96, plain, (r2_waybel_7(X1,X2,X3)|~r2_hidden(esk3_3(X1,X2,X3),X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 12.06/12.30  cnf(c_0_97, negated_conjecture, (r2_waybel_7(esk6_0,esk8_0,esk7_0)|r2_waybel_7(esk6_0,X1,esk7_0)|r2_hidden(esk3_3(esk6_0,X1,esk7_0),esk8_0)), inference(spm,[status(thm)],[c_0_91, c_0_92])).
% 12.06/12.30  cnf(c_0_98, plain, (m1_connsp_2(X1,X2,X3)|v2_struct_0(X2)|~r2_hidden(X1,k1_yellow19(X2,X3))|~m1_subset_1(X3,u1_struct_0(X2))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 12.06/12.30  cnf(c_0_99, negated_conjecture, (r2_hidden(X1,esk8_0)|~r2_waybel_7(esk6_0,esk8_0,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk6_0)))|~r2_hidden(X2,k1_tops_1(esk6_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_94]), c_0_50]), c_0_28])])).
% 12.06/12.30  cnf(c_0_100, negated_conjecture, (r2_hidden(esk7_0,k1_tops_1(esk6_0,X1))|~m1_connsp_2(X1,esk6_0,esk7_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_65]), c_0_50]), c_0_28])]), c_0_66])).
% 12.06/12.30  cnf(c_0_101, negated_conjecture, (r2_waybel_7(esk6_0,esk8_0,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_97]), c_0_50]), c_0_28])])).
% 12.06/12.30  cnf(c_0_102, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk6_0)))|~m1_connsp_2(X1,esk6_0,esk7_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_65]), c_0_50]), c_0_28])]), c_0_66])).
% 12.06/12.30  cnf(c_0_103, plain, (m1_connsp_2(esk1_2(k1_yellow19(X1,X2),X3),X1,X2)|v2_struct_0(X1)|r1_tarski(k1_yellow19(X1,X2),X3)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_98, c_0_44])).
% 12.06/12.30  cnf(c_0_104, negated_conjecture, (r2_hidden(X1,esk8_0)|~m1_connsp_2(X1,esk6_0,esk7_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_100]), c_0_101])]), c_0_102])).
% 12.06/12.30  cnf(c_0_105, negated_conjecture, (m1_connsp_2(esk1_2(k1_yellow19(esk6_0,esk7_0),X1),esk6_0,esk7_0)|r1_tarski(k1_yellow19(esk6_0,esk7_0),X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_65]), c_0_50]), c_0_28])]), c_0_66])).
% 12.06/12.30  cnf(c_0_106, negated_conjecture, (~r2_waybel_7(esk6_0,esk8_0,esk7_0)|~r1_tarski(k1_yellow19(esk6_0,esk7_0),esk8_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 12.06/12.30  cnf(c_0_107, negated_conjecture, (r2_hidden(esk1_2(k1_yellow19(esk6_0,esk7_0),X1),esk8_0)|r1_tarski(k1_yellow19(esk6_0,esk7_0),X1)), inference(spm,[status(thm)],[c_0_104, c_0_105])).
% 12.06/12.30  cnf(c_0_108, negated_conjecture, (~r1_tarski(k1_yellow19(esk6_0,esk7_0),esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_106, c_0_101])])).
% 12.06/12.30  cnf(c_0_109, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_107]), c_0_108]), ['proof']).
% 12.06/12.30  # SZS output end CNFRefutation
% 12.06/12.30  # Proof object total steps             : 110
% 12.06/12.30  # Proof object clause steps            : 81
% 12.06/12.30  # Proof object formula steps           : 29
% 12.06/12.30  # Proof object conjectures             : 42
% 12.06/12.30  # Proof object clause conjectures      : 39
% 12.06/12.30  # Proof object formula conjectures     : 3
% 12.06/12.30  # Proof object initial clauses used    : 33
% 12.06/12.30  # Proof object initial formulas used   : 14
% 12.06/12.30  # Proof object generating inferences   : 42
% 12.06/12.30  # Proof object simplifying inferences  : 66
% 12.06/12.30  # Training examples: 0 positive, 0 negative
% 12.06/12.30  # Parsed axioms                        : 14
% 12.06/12.30  # Removed by relevancy pruning/SinE    : 0
% 12.06/12.30  # Initial clauses                      : 38
% 12.06/12.30  # Removed in clause preprocessing      : 1
% 12.06/12.30  # Initial clauses in saturation        : 37
% 12.06/12.30  # Processed clauses                    : 20482
% 12.06/12.30  # ...of these trivial                  : 349
% 12.06/12.30  # ...subsumed                          : 10254
% 12.06/12.30  # ...remaining for further processing  : 9879
% 12.06/12.30  # Other redundant clauses eliminated   : 0
% 12.06/12.30  # Clauses deleted for lack of memory   : 0
% 12.06/12.30  # Backward-subsumed                    : 1630
% 12.06/12.30  # Backward-rewritten                   : 541
% 12.06/12.30  # Generated clauses                    : 358744
% 12.06/12.30  # ...of the previous two non-trivial   : 342870
% 12.06/12.30  # Contextual simplify-reflections      : 393
% 12.06/12.30  # Paramodulations                      : 358434
% 12.06/12.30  # Factorizations                       : 310
% 12.06/12.30  # Equation resolutions                 : 0
% 12.06/12.30  # Propositional unsat checks           : 0
% 12.06/12.30  #    Propositional check models        : 0
% 12.06/12.30  #    Propositional check unsatisfiable : 0
% 12.06/12.30  #    Propositional clauses             : 0
% 12.06/12.30  #    Propositional clauses after purity: 0
% 12.06/12.30  #    Propositional unsat core size     : 0
% 12.06/12.30  #    Propositional preprocessing time  : 0.000
% 12.06/12.30  #    Propositional encoding time       : 0.000
% 12.06/12.30  #    Propositional solver time         : 0.000
% 12.06/12.30  #    Success case prop preproc time    : 0.000
% 12.06/12.30  #    Success case prop encoding time   : 0.000
% 12.06/12.30  #    Success case prop solver time     : 0.000
% 12.06/12.30  # Current number of processed clauses  : 7708
% 12.06/12.30  #    Positive orientable unit clauses  : 151
% 12.06/12.30  #    Positive unorientable unit clauses: 0
% 12.06/12.30  #    Negative unit clauses             : 3
% 12.06/12.30  #    Non-unit-clauses                  : 7554
% 12.06/12.30  # Current number of unprocessed clauses: 310427
% 12.06/12.30  # ...number of literals in the above   : 2174594
% 12.06/12.30  # Current number of archived formulas  : 0
% 12.06/12.30  # Current number of archived clauses   : 2172
% 12.06/12.30  # Clause-clause subsumption calls (NU) : 6360959
% 12.06/12.30  # Rec. Clause-clause subsumption calls : 1071218
% 12.06/12.30  # Non-unit clause-clause subsumptions  : 12141
% 12.06/12.30  # Unit Clause-clause subsumption calls : 64915
% 12.06/12.30  # Rewrite failures with RHS unbound    : 0
% 12.06/12.30  # BW rewrite match attempts            : 643
% 12.06/12.30  # BW rewrite match successes           : 52
% 12.06/12.30  # Condensation attempts                : 0
% 12.06/12.30  # Condensation successes               : 0
% 12.06/12.30  # Termbank termtop insertions          : 16531792
% 12.15/12.32  
% 12.15/12.32  # -------------------------------------------------
% 12.15/12.32  # User time                : 11.806 s
% 12.15/12.32  # System time              : 0.174 s
% 12.15/12.32  # Total time               : 11.980 s
% 12.15/12.32  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
