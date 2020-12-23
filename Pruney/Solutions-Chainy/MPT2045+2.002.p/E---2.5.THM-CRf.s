%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:50 EST 2020

% Result     : Theorem 0.50s
% Output     : CNFRefutation 0.50s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 614 expanded)
%              Number of clauses        :   67 ( 224 expanded)
%              Number of leaves         :   16 ( 151 expanded)
%              Depth                    :   12
%              Number of atoms          :  409 (3617 expanded)
%              Number of equality atoms :    7 (  40 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   23 (   3 average)
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

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

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

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t44_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(k1_tops_1(X1,X2),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(c_0_16,negated_conjecture,(
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

fof(c_0_17,negated_conjecture,
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
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])).

fof(c_0_18,plain,(
    ! [X33] : k3_yellow_1(X33) = k3_lattice3(k1_lattice3(X33)) ),
    inference(variable_rename,[status(thm)],[d2_yellow_1])).

fof(c_0_19,plain,(
    ! [X16] :
      ( ~ l1_struct_0(X16)
      | k2_struct_0(X16) = u1_struct_0(X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_20,plain,(
    ! [X17] :
      ( ~ l1_pre_topc(X17)
      | l1_struct_0(X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_21,plain,(
    ! [X47,X48,X49] :
      ( ( ~ r2_hidden(X49,k1_yellow19(X47,X48))
        | m1_connsp_2(X49,X47,X48)
        | ~ m1_subset_1(X48,u1_struct_0(X47))
        | v2_struct_0(X47)
        | ~ v2_pre_topc(X47)
        | ~ l1_pre_topc(X47) )
      & ( ~ m1_connsp_2(X49,X47,X48)
        | r2_hidden(X49,k1_yellow19(X47,X48))
        | ~ m1_subset_1(X48,u1_struct_0(X47))
        | v2_struct_0(X47)
        | ~ v2_pre_topc(X47)
        | ~ l1_pre_topc(X47) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_yellow19])])])])])).

fof(c_0_22,plain,(
    ! [X30,X31,X32] :
      ( v2_struct_0(X30)
      | ~ v2_pre_topc(X30)
      | ~ l1_pre_topc(X30)
      | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))
      | ~ m1_subset_1(X32,u1_struct_0(X30))
      | ~ v3_pre_topc(X31,X30)
      | ~ r2_hidden(X32,X31)
      | m1_connsp_2(X31,X30,X32) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t5_connsp_2])])])])).

fof(c_0_23,plain,(
    ! [X13,X14,X15] :
      ( ~ r2_hidden(X13,X14)
      | ~ m1_subset_1(X14,k1_zfmisc_1(X15))
      | m1_subset_1(X13,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_24,plain,(
    ! [X34,X35,X36,X37,X38,X39] :
      ( ( ~ r2_waybel_7(X34,X35,X36)
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X34)))
        | ~ v3_pre_topc(X37,X34)
        | ~ r2_hidden(X36,X37)
        | r2_hidden(X37,X35)
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34) )
      & ( m1_subset_1(esk2_3(X34,X38,X39),k1_zfmisc_1(u1_struct_0(X34)))
        | r2_waybel_7(X34,X38,X39)
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34) )
      & ( v3_pre_topc(esk2_3(X34,X38,X39),X34)
        | r2_waybel_7(X34,X38,X39)
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34) )
      & ( r2_hidden(X39,esk2_3(X34,X38,X39))
        | r2_waybel_7(X34,X38,X39)
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34) )
      & ( ~ r2_hidden(esk2_3(X34,X38,X39),X38)
        | r2_waybel_7(X34,X38,X39)
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_waybel_7])])])])])])).

fof(c_0_25,plain,(
    ! [X41,X42,X43,X44] :
      ( ( ~ v13_waybel_0(X42,k3_yellow_1(X41))
        | ~ r1_tarski(X43,X44)
        | ~ r1_tarski(X44,X41)
        | ~ r2_hidden(X43,X42)
        | r2_hidden(X44,X42)
        | ~ m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X41)))) )
      & ( r1_tarski(esk3_2(X41,X42),esk4_2(X41,X42))
        | v13_waybel_0(X42,k3_yellow_1(X41))
        | ~ m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X41)))) )
      & ( r1_tarski(esk4_2(X41,X42),X41)
        | v13_waybel_0(X42,k3_yellow_1(X41))
        | ~ m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X41)))) )
      & ( r2_hidden(esk3_2(X41,X42),X42)
        | v13_waybel_0(X42,k3_yellow_1(X41))
        | ~ m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X41)))) )
      & ( ~ r2_hidden(esk4_2(X41,X42),X42)
        | v13_waybel_0(X42,k3_yellow_1(X41))
        | ~ m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X41)))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_waybel_7])])])])])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk5_0))))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,plain,
    ( k3_yellow_1(X1) = k3_lattice3(k1_lattice3(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,negated_conjecture,
    ( v13_waybel_0(esk7_0,k3_yellow_1(k2_struct_0(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_31,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,k1_yellow19(X2,X3))
    | v2_struct_0(X2)
    | ~ m1_connsp_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_34,negated_conjecture,
    ( v2_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_35,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_36,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_37,plain,
    ( v2_struct_0(X1)
    | m1_connsp_2(X2,X1,X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v3_pre_topc(X2,X1)
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_38,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_39,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | r2_waybel_7(X1,X2,X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_40,plain,
    ( v3_pre_topc(esk2_3(X1,X2,X3),X1)
    | r2_waybel_7(X1,X2,X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_41,plain,
    ( r2_hidden(X4,X1)
    | ~ v13_waybel_0(X1,k3_yellow_1(X2))
    | ~ r1_tarski(X3,X4)
    | ~ r1_tarski(X4,X2)
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk5_0)))))) ),
    inference(rw,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_43,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_44,negated_conjecture,
    ( v13_waybel_0(esk7_0,k3_lattice3(k1_lattice3(k2_struct_0(esk5_0)))) ),
    inference(rw,[status(thm)],[c_0_30,c_0_27])).

fof(c_0_45,plain,(
    ! [X18,X19] :
      ( ~ l1_pre_topc(X18)
      | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
      | m1_subset_1(k1_tops_1(X18,X19),k1_zfmisc_1(u1_struct_0(X18))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_tops_1])])).

fof(c_0_46,plain,(
    ! [X20,X21] :
      ( ~ v2_pre_topc(X20)
      | ~ l1_pre_topc(X20)
      | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))
      | v3_pre_topc(k1_tops_1(X20,X21),X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).

fof(c_0_47,plain,(
    ! [X24,X25,X26] :
      ( ( ~ m1_connsp_2(X26,X24,X25)
        | r2_hidden(X25,k1_tops_1(X24,X26))
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X24)))
        | ~ m1_subset_1(X25,u1_struct_0(X24))
        | v2_struct_0(X24)
        | ~ v2_pre_topc(X24)
        | ~ l1_pre_topc(X24) )
      & ( ~ r2_hidden(X25,k1_tops_1(X24,X26))
        | m1_connsp_2(X26,X24,X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X24)))
        | ~ m1_subset_1(X25,u1_struct_0(X24))
        | v2_struct_0(X24)
        | ~ v2_pre_topc(X24)
        | ~ l1_pre_topc(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_connsp_2])])])])])).

fof(c_0_48,plain,(
    ! [X27,X28,X29] :
      ( v2_struct_0(X27)
      | ~ v2_pre_topc(X27)
      | ~ l1_pre_topc(X27)
      | ~ m1_subset_1(X28,u1_struct_0(X27))
      | ~ m1_connsp_2(X29,X27,X28)
      | m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X27))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m1_connsp_2])])])])).

cnf(c_0_49,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(X1,k1_yellow19(esk5_0,esk6_0))
    | ~ m1_connsp_2(X1,esk5_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_51,plain,
    ( m1_connsp_2(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ v3_pre_topc(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X3,X1) ),
    inference(csr,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_52,negated_conjecture,
    ( r2_waybel_7(esk5_0,X1,X2)
    | m1_subset_1(esk2_3(esk5_0,X1,X2),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_34]),c_0_35])])).

cnf(c_0_53,negated_conjecture,
    ( r2_waybel_7(esk5_0,X1,X2)
    | v3_pre_topc(esk2_3(esk5_0,X1,X2),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_34]),c_0_35])])).

cnf(c_0_54,plain,
    ( r2_hidden(X1,esk2_3(X2,X3,X1))
    | r2_waybel_7(X2,X3,X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_55,plain,
    ( m1_connsp_2(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,k1_yellow19(X2,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_56,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_57,plain,
    ( r2_hidden(X4,X1)
    | ~ r1_tarski(X4,X2)
    | ~ r1_tarski(X3,X4)
    | ~ r2_hidden(X3,X1)
    | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_27]),c_0_27])).

cnf(c_0_58,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(esk5_0)))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_35])])).

cnf(c_0_59,negated_conjecture,
    ( v13_waybel_0(esk7_0,k3_lattice3(k1_lattice3(u1_struct_0(esk5_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_43]),c_0_35])])).

fof(c_0_60,plain,(
    ! [X11,X12] :
      ( ( ~ m1_subset_1(X11,k1_zfmisc_1(X12))
        | r1_tarski(X11,X12) )
      & ( ~ r1_tarski(X11,X12)
        | m1_subset_1(X11,k1_zfmisc_1(X12)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_61,plain,
    ( r2_hidden(X4,X2)
    | ~ r2_waybel_7(X1,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X4,X1)
    | ~ r2_hidden(X3,X4)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_62,plain,
    ( m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_63,plain,
    ( v3_pre_topc(k1_tops_1(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_64,plain,
    ( r2_hidden(X3,k1_tops_1(X2,X1))
    | v2_struct_0(X2)
    | ~ m1_connsp_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_65,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(X1,X2)
    | ~ m1_connsp_2(X1,esk5_0,esk6_0)
    | ~ r1_tarski(k1_yellow19(esk5_0,esk6_0),X2) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_67,negated_conjecture,
    ( r2_waybel_7(esk5_0,esk7_0,esk6_0)
    | r1_tarski(k1_yellow19(esk5_0,esk6_0),esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_68,negated_conjecture,
    ( r2_waybel_7(esk5_0,X1,X2)
    | m1_connsp_2(esk2_3(esk5_0,X1,X2),esk5_0,X3)
    | ~ r2_hidden(X3,esk2_3(esk5_0,X1,X2)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_34]),c_0_35])]),c_0_36]),c_0_53])).

cnf(c_0_69,negated_conjecture,
    ( r2_waybel_7(esk5_0,X1,X2)
    | r2_hidden(X2,esk2_3(esk5_0,X1,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_34]),c_0_35])])).

cnf(c_0_70,plain,
    ( m1_connsp_2(esk1_2(k1_yellow19(X1,X2),X3),X1,X2)
    | v2_struct_0(X1)
    | r1_tarski(k1_yellow19(X1,X2),X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_71,negated_conjecture,
    ( r2_hidden(X1,esk7_0)
    | ~ r2_hidden(X2,esk7_0)
    | ~ r1_tarski(X1,u1_struct_0(esk5_0))
    | ~ r1_tarski(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59])])).

cnf(c_0_72,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

fof(c_0_73,plain,(
    ! [X22,X23] :
      ( ~ l1_pre_topc(X22)
      | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
      | r1_tarski(k1_tops_1(X22,X23),X23) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).

cnf(c_0_74,plain,
    ( r2_hidden(k1_tops_1(X1,X2),X3)
    | ~ r2_waybel_7(X1,X3,X4)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X4,k1_tops_1(X1,X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63])).

cnf(c_0_75,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,k1_tops_1(X1,X3))
    | ~ m1_connsp_2(X3,X1,X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_76,negated_conjecture,
    ( r2_waybel_7(esk5_0,esk7_0,esk6_0)
    | r2_hidden(X1,esk7_0)
    | ~ m1_connsp_2(X1,esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_77,negated_conjecture,
    ( r2_waybel_7(esk5_0,X1,X2)
    | m1_connsp_2(esk2_3(esk5_0,X1,X2),esk5_0,X2) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_78,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_connsp_2(X1,esk5_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_33]),c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_79,negated_conjecture,
    ( m1_connsp_2(esk1_2(k1_yellow19(esk5_0,esk6_0),X1),esk5_0,esk6_0)
    | r1_tarski(k1_yellow19(esk5_0,esk6_0),X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_33]),c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_80,negated_conjecture,
    ( r2_hidden(X1,esk7_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ r2_hidden(X2,esk7_0)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_81,plain,
    ( r1_tarski(k1_tops_1(X1,X2),X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_82,plain,
    ( r2_hidden(k1_tops_1(X1,k1_tops_1(X1,X2)),X3)
    | ~ r2_waybel_7(X1,X3,X4)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X4,k1_tops_1(X1,k1_tops_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_74,c_0_62])).

cnf(c_0_83,negated_conjecture,
    ( r2_hidden(esk6_0,k1_tops_1(esk5_0,X1))
    | ~ m1_connsp_2(X1,esk5_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_33]),c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_84,plain,
    ( r2_waybel_7(X1,X2,X3)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_85,negated_conjecture,
    ( r2_waybel_7(esk5_0,esk7_0,esk6_0)
    | r2_waybel_7(esk5_0,X1,esk6_0)
    | r2_hidden(esk2_3(esk5_0,X1,esk6_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_86,plain,
    ( m1_connsp_2(k1_tops_1(X1,X2),X1,X3)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X3,k1_tops_1(X1,X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_62]),c_0_63])).

cnf(c_0_87,negated_conjecture,
    ( m1_subset_1(esk1_2(k1_yellow19(esk5_0,esk6_0),X1),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | r1_tarski(k1_yellow19(esk5_0,esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_88,negated_conjecture,
    ( r2_hidden(X1,esk7_0)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(k1_tops_1(X2,X1),esk7_0) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_89,negated_conjecture,
    ( r2_hidden(k1_tops_1(esk5_0,k1_tops_1(esk5_0,X1)),X2)
    | ~ r2_waybel_7(esk5_0,X2,esk6_0)
    | ~ m1_connsp_2(k1_tops_1(esk5_0,X1),esk5_0,esk6_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_34]),c_0_35])])).

cnf(c_0_90,negated_conjecture,
    ( r2_waybel_7(esk5_0,esk7_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_34]),c_0_35])])).

cnf(c_0_91,negated_conjecture,
    ( m1_connsp_2(k1_tops_1(esk5_0,esk1_2(k1_yellow19(esk5_0,esk6_0),X1)),esk5_0,X2)
    | r1_tarski(k1_yellow19(esk5_0,esk6_0),X1)
    | ~ r2_hidden(X2,k1_tops_1(esk5_0,esk1_2(k1_yellow19(esk5_0,esk6_0),X1))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_92,negated_conjecture,
    ( r2_hidden(k1_tops_1(esk5_0,X1),esk7_0)
    | ~ m1_connsp_2(k1_tops_1(esk5_0,X1),esk5_0,esk6_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_35]),c_0_90])]),c_0_78])).

cnf(c_0_93,negated_conjecture,
    ( m1_connsp_2(k1_tops_1(esk5_0,esk1_2(k1_yellow19(esk5_0,esk6_0),X1)),esk5_0,esk6_0)
    | r1_tarski(k1_yellow19(esk5_0,esk6_0),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_83]),c_0_79])).

cnf(c_0_94,negated_conjecture,
    ( r2_hidden(k1_tops_1(esk5_0,esk1_2(k1_yellow19(esk5_0,esk6_0),X1)),esk7_0)
    | r1_tarski(k1_yellow19(esk5_0,esk6_0),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_87])).

cnf(c_0_95,negated_conjecture,
    ( ~ r2_waybel_7(esk5_0,esk7_0,esk6_0)
    | ~ r1_tarski(k1_yellow19(esk5_0,esk6_0),esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_96,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_97,negated_conjecture,
    ( r2_hidden(esk1_2(k1_yellow19(esk5_0,esk6_0),X1),esk7_0)
    | r1_tarski(k1_yellow19(esk5_0,esk6_0),X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_94]),c_0_35])]),c_0_87])).

cnf(c_0_98,negated_conjecture,
    ( ~ r1_tarski(k1_yellow19(esk5_0,esk6_0),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_95,c_0_90])])).

cnf(c_0_99,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_98]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:26:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.50/0.65  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 0.50/0.65  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.50/0.65  #
% 0.50/0.65  # Preprocessing time       : 0.037 s
% 0.50/0.65  
% 0.50/0.65  # Proof found!
% 0.50/0.65  # SZS status Theorem
% 0.50/0.65  # SZS output start CNFRefutation
% 0.50/0.65  fof(t4_yellow19, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:((v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X1)))&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))))=>(r2_waybel_7(X1,X3,X2)<=>r1_tarski(k1_yellow19(X1,X2),X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_yellow19)).
% 0.50/0.65  fof(d2_yellow_1, axiom, ![X1]:k3_yellow_1(X1)=k3_lattice3(k1_lattice3(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_yellow_1)).
% 0.50/0.65  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 0.50/0.65  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.50/0.65  fof(t3_yellow19, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(r2_hidden(X3,k1_yellow19(X1,X2))<=>m1_connsp_2(X3,X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_yellow19)).
% 0.50/0.65  fof(t5_connsp_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>((v3_pre_topc(X2,X1)&r2_hidden(X3,X2))=>m1_connsp_2(X2,X1,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_connsp_2)).
% 0.50/0.65  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.50/0.65  fof(d5_waybel_7, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2, X3]:(r2_waybel_7(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>((v3_pre_topc(X4,X1)&r2_hidden(X3,X4))=>r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_waybel_7)).
% 0.50/0.65  fof(t11_waybel_7, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))=>(v13_waybel_0(X2,k3_yellow_1(X1))<=>![X3, X4]:(((r1_tarski(X3,X4)&r1_tarski(X4,X1))&r2_hidden(X3,X2))=>r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_waybel_7)).
% 0.50/0.65  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.50/0.65  fof(dt_k1_tops_1, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 0.50/0.65  fof(fc9_tops_1, axiom, ![X1, X2]:(((v2_pre_topc(X1)&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>v3_pre_topc(k1_tops_1(X1,X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 0.50/0.65  fof(d1_connsp_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(m1_connsp_2(X3,X1,X2)<=>r2_hidden(X2,k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_connsp_2)).
% 0.50/0.65  fof(dt_m1_connsp_2, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>![X3]:(m1_connsp_2(X3,X1,X2)=>m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 0.50/0.65  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.50/0.65  fof(t44_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k1_tops_1(X1,X2),X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 0.50/0.65  fof(c_0_16, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:((v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X1)))&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))))=>(r2_waybel_7(X1,X3,X2)<=>r1_tarski(k1_yellow19(X1,X2),X3)))))), inference(assume_negation,[status(cth)],[t4_yellow19])).
% 0.50/0.65  fof(c_0_17, negated_conjecture, (((~v2_struct_0(esk5_0)&v2_pre_topc(esk5_0))&l1_pre_topc(esk5_0))&(m1_subset_1(esk6_0,u1_struct_0(esk5_0))&((v13_waybel_0(esk7_0,k3_yellow_1(k2_struct_0(esk5_0)))&m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk5_0))))))&((~r2_waybel_7(esk5_0,esk7_0,esk6_0)|~r1_tarski(k1_yellow19(esk5_0,esk6_0),esk7_0))&(r2_waybel_7(esk5_0,esk7_0,esk6_0)|r1_tarski(k1_yellow19(esk5_0,esk6_0),esk7_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])).
% 0.50/0.65  fof(c_0_18, plain, ![X33]:k3_yellow_1(X33)=k3_lattice3(k1_lattice3(X33)), inference(variable_rename,[status(thm)],[d2_yellow_1])).
% 0.50/0.65  fof(c_0_19, plain, ![X16]:(~l1_struct_0(X16)|k2_struct_0(X16)=u1_struct_0(X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.50/0.65  fof(c_0_20, plain, ![X17]:(~l1_pre_topc(X17)|l1_struct_0(X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.50/0.65  fof(c_0_21, plain, ![X47, X48, X49]:((~r2_hidden(X49,k1_yellow19(X47,X48))|m1_connsp_2(X49,X47,X48)|~m1_subset_1(X48,u1_struct_0(X47))|(v2_struct_0(X47)|~v2_pre_topc(X47)|~l1_pre_topc(X47)))&(~m1_connsp_2(X49,X47,X48)|r2_hidden(X49,k1_yellow19(X47,X48))|~m1_subset_1(X48,u1_struct_0(X47))|(v2_struct_0(X47)|~v2_pre_topc(X47)|~l1_pre_topc(X47)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_yellow19])])])])])).
% 0.50/0.65  fof(c_0_22, plain, ![X30, X31, X32]:(v2_struct_0(X30)|~v2_pre_topc(X30)|~l1_pre_topc(X30)|(~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))|(~m1_subset_1(X32,u1_struct_0(X30))|(~v3_pre_topc(X31,X30)|~r2_hidden(X32,X31)|m1_connsp_2(X31,X30,X32))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t5_connsp_2])])])])).
% 0.50/0.65  fof(c_0_23, plain, ![X13, X14, X15]:(~r2_hidden(X13,X14)|~m1_subset_1(X14,k1_zfmisc_1(X15))|m1_subset_1(X13,X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.50/0.65  fof(c_0_24, plain, ![X34, X35, X36, X37, X38, X39]:((~r2_waybel_7(X34,X35,X36)|(~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X34)))|(~v3_pre_topc(X37,X34)|~r2_hidden(X36,X37)|r2_hidden(X37,X35)))|(~v2_pre_topc(X34)|~l1_pre_topc(X34)))&((m1_subset_1(esk2_3(X34,X38,X39),k1_zfmisc_1(u1_struct_0(X34)))|r2_waybel_7(X34,X38,X39)|(~v2_pre_topc(X34)|~l1_pre_topc(X34)))&(((v3_pre_topc(esk2_3(X34,X38,X39),X34)|r2_waybel_7(X34,X38,X39)|(~v2_pre_topc(X34)|~l1_pre_topc(X34)))&(r2_hidden(X39,esk2_3(X34,X38,X39))|r2_waybel_7(X34,X38,X39)|(~v2_pre_topc(X34)|~l1_pre_topc(X34))))&(~r2_hidden(esk2_3(X34,X38,X39),X38)|r2_waybel_7(X34,X38,X39)|(~v2_pre_topc(X34)|~l1_pre_topc(X34)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_waybel_7])])])])])])).
% 0.50/0.65  fof(c_0_25, plain, ![X41, X42, X43, X44]:((~v13_waybel_0(X42,k3_yellow_1(X41))|(~r1_tarski(X43,X44)|~r1_tarski(X44,X41)|~r2_hidden(X43,X42)|r2_hidden(X44,X42))|~m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X41)))))&((((r1_tarski(esk3_2(X41,X42),esk4_2(X41,X42))|v13_waybel_0(X42,k3_yellow_1(X41))|~m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X41)))))&(r1_tarski(esk4_2(X41,X42),X41)|v13_waybel_0(X42,k3_yellow_1(X41))|~m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X41))))))&(r2_hidden(esk3_2(X41,X42),X42)|v13_waybel_0(X42,k3_yellow_1(X41))|~m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X41))))))&(~r2_hidden(esk4_2(X41,X42),X42)|v13_waybel_0(X42,k3_yellow_1(X41))|~m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X41))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_waybel_7])])])])])).
% 0.50/0.65  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk5_0)))))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.50/0.65  cnf(c_0_27, plain, (k3_yellow_1(X1)=k3_lattice3(k1_lattice3(X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.50/0.65  cnf(c_0_28, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.50/0.65  cnf(c_0_29, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.50/0.65  cnf(c_0_30, negated_conjecture, (v13_waybel_0(esk7_0,k3_yellow_1(k2_struct_0(esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.50/0.65  fof(c_0_31, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.50/0.65  cnf(c_0_32, plain, (r2_hidden(X1,k1_yellow19(X2,X3))|v2_struct_0(X2)|~m1_connsp_2(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X2))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.50/0.65  cnf(c_0_33, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.50/0.65  cnf(c_0_34, negated_conjecture, (v2_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.50/0.65  cnf(c_0_35, negated_conjecture, (l1_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.50/0.65  cnf(c_0_36, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.50/0.65  cnf(c_0_37, plain, (v2_struct_0(X1)|m1_connsp_2(X2,X1,X3)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,u1_struct_0(X1))|~v3_pre_topc(X2,X1)|~r2_hidden(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.50/0.65  cnf(c_0_38, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.50/0.65  cnf(c_0_39, plain, (m1_subset_1(esk2_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|r2_waybel_7(X1,X2,X3)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.50/0.65  cnf(c_0_40, plain, (v3_pre_topc(esk2_3(X1,X2,X3),X1)|r2_waybel_7(X1,X2,X3)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.50/0.65  cnf(c_0_41, plain, (r2_hidden(X4,X1)|~v13_waybel_0(X1,k3_yellow_1(X2))|~r1_tarski(X3,X4)|~r1_tarski(X4,X2)|~r2_hidden(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2))))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.50/0.65  cnf(c_0_42, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk5_0))))))), inference(rw,[status(thm)],[c_0_26, c_0_27])).
% 0.50/0.65  cnf(c_0_43, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.50/0.65  cnf(c_0_44, negated_conjecture, (v13_waybel_0(esk7_0,k3_lattice3(k1_lattice3(k2_struct_0(esk5_0))))), inference(rw,[status(thm)],[c_0_30, c_0_27])).
% 0.50/0.65  fof(c_0_45, plain, ![X18, X19]:(~l1_pre_topc(X18)|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|m1_subset_1(k1_tops_1(X18,X19),k1_zfmisc_1(u1_struct_0(X18)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_tops_1])])).
% 0.50/0.65  fof(c_0_46, plain, ![X20, X21]:(~v2_pre_topc(X20)|~l1_pre_topc(X20)|~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))|v3_pre_topc(k1_tops_1(X20,X21),X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).
% 0.50/0.65  fof(c_0_47, plain, ![X24, X25, X26]:((~m1_connsp_2(X26,X24,X25)|r2_hidden(X25,k1_tops_1(X24,X26))|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X24)))|~m1_subset_1(X25,u1_struct_0(X24))|(v2_struct_0(X24)|~v2_pre_topc(X24)|~l1_pre_topc(X24)))&(~r2_hidden(X25,k1_tops_1(X24,X26))|m1_connsp_2(X26,X24,X25)|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X24)))|~m1_subset_1(X25,u1_struct_0(X24))|(v2_struct_0(X24)|~v2_pre_topc(X24)|~l1_pre_topc(X24)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_connsp_2])])])])])).
% 0.50/0.65  fof(c_0_48, plain, ![X27, X28, X29]:(v2_struct_0(X27)|~v2_pre_topc(X27)|~l1_pre_topc(X27)|~m1_subset_1(X28,u1_struct_0(X27))|(~m1_connsp_2(X29,X27,X28)|m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X27))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m1_connsp_2])])])])).
% 0.50/0.65  cnf(c_0_49, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.50/0.65  cnf(c_0_50, negated_conjecture, (r2_hidden(X1,k1_yellow19(esk5_0,esk6_0))|~m1_connsp_2(X1,esk5_0,esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34]), c_0_35])]), c_0_36])).
% 0.50/0.65  cnf(c_0_51, plain, (m1_connsp_2(X1,X2,X3)|v2_struct_0(X2)|~v3_pre_topc(X1,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~r2_hidden(X3,X1)), inference(csr,[status(thm)],[c_0_37, c_0_38])).
% 0.50/0.65  cnf(c_0_52, negated_conjecture, (r2_waybel_7(esk5_0,X1,X2)|m1_subset_1(esk2_3(esk5_0,X1,X2),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_34]), c_0_35])])).
% 0.50/0.65  cnf(c_0_53, negated_conjecture, (r2_waybel_7(esk5_0,X1,X2)|v3_pre_topc(esk2_3(esk5_0,X1,X2),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_34]), c_0_35])])).
% 0.50/0.65  cnf(c_0_54, plain, (r2_hidden(X1,esk2_3(X2,X3,X1))|r2_waybel_7(X2,X3,X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.50/0.65  cnf(c_0_55, plain, (m1_connsp_2(X1,X2,X3)|v2_struct_0(X2)|~r2_hidden(X1,k1_yellow19(X2,X3))|~m1_subset_1(X3,u1_struct_0(X2))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.50/0.65  cnf(c_0_56, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.50/0.65  cnf(c_0_57, plain, (r2_hidden(X4,X1)|~r1_tarski(X4,X2)|~r1_tarski(X3,X4)|~r2_hidden(X3,X1)|~v13_waybel_0(X1,k3_lattice3(k1_lattice3(X2)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_27]), c_0_27])).
% 0.50/0.65  cnf(c_0_58, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(esk5_0))))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_35])])).
% 0.50/0.65  cnf(c_0_59, negated_conjecture, (v13_waybel_0(esk7_0,k3_lattice3(k1_lattice3(u1_struct_0(esk5_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_43]), c_0_35])])).
% 0.50/0.65  fof(c_0_60, plain, ![X11, X12]:((~m1_subset_1(X11,k1_zfmisc_1(X12))|r1_tarski(X11,X12))&(~r1_tarski(X11,X12)|m1_subset_1(X11,k1_zfmisc_1(X12)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.50/0.65  cnf(c_0_61, plain, (r2_hidden(X4,X2)|~r2_waybel_7(X1,X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))|~v3_pre_topc(X4,X1)|~r2_hidden(X3,X4)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.50/0.65  cnf(c_0_62, plain, (m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.50/0.65  cnf(c_0_63, plain, (v3_pre_topc(k1_tops_1(X1,X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.50/0.65  cnf(c_0_64, plain, (r2_hidden(X3,k1_tops_1(X2,X1))|v2_struct_0(X2)|~m1_connsp_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,u1_struct_0(X2))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.50/0.65  cnf(c_0_65, plain, (v2_struct_0(X1)|m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_connsp_2(X3,X1,X2)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.50/0.65  cnf(c_0_66, negated_conjecture, (r2_hidden(X1,X2)|~m1_connsp_2(X1,esk5_0,esk6_0)|~r1_tarski(k1_yellow19(esk5_0,esk6_0),X2)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.50/0.65  cnf(c_0_67, negated_conjecture, (r2_waybel_7(esk5_0,esk7_0,esk6_0)|r1_tarski(k1_yellow19(esk5_0,esk6_0),esk7_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.50/0.65  cnf(c_0_68, negated_conjecture, (r2_waybel_7(esk5_0,X1,X2)|m1_connsp_2(esk2_3(esk5_0,X1,X2),esk5_0,X3)|~r2_hidden(X3,esk2_3(esk5_0,X1,X2))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_34]), c_0_35])]), c_0_36]), c_0_53])).
% 0.50/0.65  cnf(c_0_69, negated_conjecture, (r2_waybel_7(esk5_0,X1,X2)|r2_hidden(X2,esk2_3(esk5_0,X1,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_34]), c_0_35])])).
% 0.50/0.65  cnf(c_0_70, plain, (m1_connsp_2(esk1_2(k1_yellow19(X1,X2),X3),X1,X2)|v2_struct_0(X1)|r1_tarski(k1_yellow19(X1,X2),X3)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.50/0.65  cnf(c_0_71, negated_conjecture, (r2_hidden(X1,esk7_0)|~r2_hidden(X2,esk7_0)|~r1_tarski(X1,u1_struct_0(esk5_0))|~r1_tarski(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_59])])).
% 0.50/0.65  cnf(c_0_72, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.50/0.65  fof(c_0_73, plain, ![X22, X23]:(~l1_pre_topc(X22)|(~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))|r1_tarski(k1_tops_1(X22,X23),X23))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).
% 0.50/0.65  cnf(c_0_74, plain, (r2_hidden(k1_tops_1(X1,X2),X3)|~r2_waybel_7(X1,X3,X4)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(X4,k1_tops_1(X1,X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_63])).
% 0.50/0.65  cnf(c_0_75, plain, (v2_struct_0(X1)|r2_hidden(X2,k1_tops_1(X1,X3))|~m1_connsp_2(X3,X1,X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(csr,[status(thm)],[c_0_64, c_0_65])).
% 0.50/0.65  cnf(c_0_76, negated_conjecture, (r2_waybel_7(esk5_0,esk7_0,esk6_0)|r2_hidden(X1,esk7_0)|~m1_connsp_2(X1,esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.50/0.65  cnf(c_0_77, negated_conjecture, (r2_waybel_7(esk5_0,X1,X2)|m1_connsp_2(esk2_3(esk5_0,X1,X2),esk5_0,X2)), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.50/0.65  cnf(c_0_78, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))|~m1_connsp_2(X1,esk5_0,esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_33]), c_0_34]), c_0_35])]), c_0_36])).
% 0.50/0.65  cnf(c_0_79, negated_conjecture, (m1_connsp_2(esk1_2(k1_yellow19(esk5_0,esk6_0),X1),esk5_0,esk6_0)|r1_tarski(k1_yellow19(esk5_0,esk6_0),X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_33]), c_0_34]), c_0_35])]), c_0_36])).
% 0.50/0.65  cnf(c_0_80, negated_conjecture, (r2_hidden(X1,esk7_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))|~r2_hidden(X2,esk7_0)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.50/0.65  cnf(c_0_81, plain, (r1_tarski(k1_tops_1(X1,X2),X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.50/0.65  cnf(c_0_82, plain, (r2_hidden(k1_tops_1(X1,k1_tops_1(X1,X2)),X3)|~r2_waybel_7(X1,X3,X4)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(X4,k1_tops_1(X1,k1_tops_1(X1,X2)))), inference(spm,[status(thm)],[c_0_74, c_0_62])).
% 0.50/0.65  cnf(c_0_83, negated_conjecture, (r2_hidden(esk6_0,k1_tops_1(esk5_0,X1))|~m1_connsp_2(X1,esk5_0,esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_33]), c_0_34]), c_0_35])]), c_0_36])).
% 0.50/0.65  cnf(c_0_84, plain, (r2_waybel_7(X1,X2,X3)|~r2_hidden(esk2_3(X1,X2,X3),X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.50/0.65  cnf(c_0_85, negated_conjecture, (r2_waybel_7(esk5_0,esk7_0,esk6_0)|r2_waybel_7(esk5_0,X1,esk6_0)|r2_hidden(esk2_3(esk5_0,X1,esk6_0),esk7_0)), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 0.50/0.65  cnf(c_0_86, plain, (m1_connsp_2(k1_tops_1(X1,X2),X1,X3)|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(X3,k1_tops_1(X1,X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_62]), c_0_63])).
% 0.50/0.65  cnf(c_0_87, negated_conjecture, (m1_subset_1(esk1_2(k1_yellow19(esk5_0,esk6_0),X1),k1_zfmisc_1(u1_struct_0(esk5_0)))|r1_tarski(k1_yellow19(esk5_0,esk6_0),X1)), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 0.50/0.65  cnf(c_0_88, negated_conjecture, (r2_hidden(X1,esk7_0)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~r2_hidden(k1_tops_1(X2,X1),esk7_0)), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 0.50/0.65  cnf(c_0_89, negated_conjecture, (r2_hidden(k1_tops_1(esk5_0,k1_tops_1(esk5_0,X1)),X2)|~r2_waybel_7(esk5_0,X2,esk6_0)|~m1_connsp_2(k1_tops_1(esk5_0,X1),esk5_0,esk6_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_34]), c_0_35])])).
% 0.50/0.65  cnf(c_0_90, negated_conjecture, (r2_waybel_7(esk5_0,esk7_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_34]), c_0_35])])).
% 0.50/0.65  cnf(c_0_91, negated_conjecture, (m1_connsp_2(k1_tops_1(esk5_0,esk1_2(k1_yellow19(esk5_0,esk6_0),X1)),esk5_0,X2)|r1_tarski(k1_yellow19(esk5_0,esk6_0),X1)|~r2_hidden(X2,k1_tops_1(esk5_0,esk1_2(k1_yellow19(esk5_0,esk6_0),X1)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_34]), c_0_35])]), c_0_36])).
% 0.50/0.65  cnf(c_0_92, negated_conjecture, (r2_hidden(k1_tops_1(esk5_0,X1),esk7_0)|~m1_connsp_2(k1_tops_1(esk5_0,X1),esk5_0,esk6_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_89]), c_0_35]), c_0_90])]), c_0_78])).
% 0.50/0.65  cnf(c_0_93, negated_conjecture, (m1_connsp_2(k1_tops_1(esk5_0,esk1_2(k1_yellow19(esk5_0,esk6_0),X1)),esk5_0,esk6_0)|r1_tarski(k1_yellow19(esk5_0,esk6_0),X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_83]), c_0_79])).
% 0.50/0.65  cnf(c_0_94, negated_conjecture, (r2_hidden(k1_tops_1(esk5_0,esk1_2(k1_yellow19(esk5_0,esk6_0),X1)),esk7_0)|r1_tarski(k1_yellow19(esk5_0,esk6_0),X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_87])).
% 0.50/0.65  cnf(c_0_95, negated_conjecture, (~r2_waybel_7(esk5_0,esk7_0,esk6_0)|~r1_tarski(k1_yellow19(esk5_0,esk6_0),esk7_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.50/0.65  cnf(c_0_96, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.50/0.65  cnf(c_0_97, negated_conjecture, (r2_hidden(esk1_2(k1_yellow19(esk5_0,esk6_0),X1),esk7_0)|r1_tarski(k1_yellow19(esk5_0,esk6_0),X1)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_94]), c_0_35])]), c_0_87])).
% 0.50/0.65  cnf(c_0_98, negated_conjecture, (~r1_tarski(k1_yellow19(esk5_0,esk6_0),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_95, c_0_90])])).
% 0.50/0.65  cnf(c_0_99, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_97]), c_0_98]), ['proof']).
% 0.50/0.65  # SZS output end CNFRefutation
% 0.50/0.65  # Proof object total steps             : 100
% 0.50/0.65  # Proof object clause steps            : 67
% 0.50/0.65  # Proof object formula steps           : 33
% 0.50/0.65  # Proof object conjectures             : 40
% 0.50/0.65  # Proof object clause conjectures      : 37
% 0.50/0.65  # Proof object formula conjectures     : 3
% 0.50/0.65  # Proof object initial clauses used    : 30
% 0.50/0.65  # Proof object initial formulas used   : 16
% 0.50/0.65  # Proof object generating inferences   : 31
% 0.50/0.65  # Proof object simplifying inferences  : 63
% 0.50/0.65  # Training examples: 0 positive, 0 negative
% 0.50/0.65  # Parsed axioms                        : 16
% 0.50/0.65  # Removed by relevancy pruning/SinE    : 0
% 0.50/0.65  # Initial clauses                      : 36
% 0.50/0.65  # Removed in clause preprocessing      : 1
% 0.50/0.65  # Initial clauses in saturation        : 35
% 0.50/0.65  # Processed clauses                    : 1301
% 0.50/0.65  # ...of these trivial                  : 6
% 0.50/0.65  # ...subsumed                          : 386
% 0.50/0.65  # ...remaining for further processing  : 909
% 0.50/0.65  # Other redundant clauses eliminated   : 0
% 0.50/0.65  # Clauses deleted for lack of memory   : 0
% 0.50/0.65  # Backward-subsumed                    : 54
% 0.50/0.65  # Backward-rewritten                   : 28
% 0.50/0.65  # Generated clauses                    : 3561
% 0.50/0.65  # ...of the previous two non-trivial   : 3347
% 0.50/0.65  # Contextual simplify-reflections      : 79
% 0.50/0.65  # Paramodulations                      : 3557
% 0.50/0.65  # Factorizations                       : 4
% 0.50/0.65  # Equation resolutions                 : 0
% 0.50/0.65  # Propositional unsat checks           : 0
% 0.50/0.65  #    Propositional check models        : 0
% 0.50/0.65  #    Propositional check unsatisfiable : 0
% 0.50/0.65  #    Propositional clauses             : 0
% 0.50/0.65  #    Propositional clauses after purity: 0
% 0.50/0.65  #    Propositional unsat core size     : 0
% 0.50/0.65  #    Propositional preprocessing time  : 0.000
% 0.50/0.65  #    Propositional encoding time       : 0.000
% 0.50/0.65  #    Propositional solver time         : 0.000
% 0.50/0.65  #    Success case prop preproc time    : 0.000
% 0.50/0.65  #    Success case prop encoding time   : 0.000
% 0.50/0.65  #    Success case prop solver time     : 0.000
% 0.50/0.65  # Current number of processed clauses  : 827
% 0.50/0.65  #    Positive orientable unit clauses  : 23
% 0.50/0.65  #    Positive unorientable unit clauses: 0
% 0.50/0.65  #    Negative unit clauses             : 3
% 0.50/0.65  #    Non-unit-clauses                  : 801
% 0.50/0.65  # Current number of unprocessed clauses: 2015
% 0.50/0.65  # ...number of literals in the above   : 10994
% 0.50/0.65  # Current number of archived formulas  : 0
% 0.50/0.65  # Current number of archived clauses   : 83
% 0.50/0.65  # Clause-clause subsumption calls (NU) : 74602
% 0.50/0.65  # Rec. Clause-clause subsumption calls : 16702
% 0.50/0.65  # Non-unit clause-clause subsumptions  : 510
% 0.50/0.65  # Unit Clause-clause subsumption calls : 620
% 0.50/0.65  # Rewrite failures with RHS unbound    : 0
% 0.50/0.65  # BW rewrite match attempts            : 28
% 0.50/0.65  # BW rewrite match successes           : 4
% 0.50/0.65  # Condensation attempts                : 0
% 0.50/0.65  # Condensation successes               : 0
% 0.50/0.65  # Termbank termtop insertions          : 134436
% 0.50/0.65  
% 0.50/0.65  # -------------------------------------------------
% 0.50/0.65  # User time                : 0.303 s
% 0.50/0.65  # System time              : 0.008 s
% 0.50/0.65  # Total time               : 0.311 s
% 0.50/0.65  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
