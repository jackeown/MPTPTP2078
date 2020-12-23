%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : yellow_6__t50_yellow_6.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:56 EDT 2019

% Result     : Theorem 154.94s
% Output     : CNFRefutation 154.94s
% Verified   : 
% Statistics : Number of formulae       :   89 (2686 expanded)
%              Number of clauses        :   74 ( 996 expanded)
%              Number of leaves         :    7 ( 654 expanded)
%              Depth                    :   13
%              Number of atoms          :  467 (34046 expanded)
%              Number of equality atoms :   37 (1450 expanded)
%              Maximal formula depth    :   25 (   5 average)
%              Maximal clause size      :   78 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t50_yellow_6,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( v8_yellow_6(X2,X1)
            & m4_yellow_6(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k13_yellow_6(X1,X2))))
             => ( v3_pre_topc(X3,k13_yellow_6(X1,X2))
              <=> ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( r2_hidden(X4,X3)
                     => ! [X5] :
                          ( ( ~ v2_struct_0(X5)
                            & v4_orders_2(X5)
                            & v7_waybel_0(X5)
                            & l1_waybel_0(X5,X1) )
                         => ( r2_hidden(k4_tarski(X5,X4),X2)
                           => r1_waybel_0(X1,X5,X3) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t50_yellow_6.p',t50_yellow_6)).

fof(d27_yellow_6,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( m4_yellow_6(X2,X1)
         => ! [X3] :
              ( ( v1_pre_topc(X3)
                & l1_pre_topc(X3) )
             => ( X3 = k13_yellow_6(X1,X2)
              <=> ( u1_struct_0(X3) = u1_struct_0(X1)
                  & u1_pre_topc(X3) = a_2_1_yellow_6(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t50_yellow_6.p',d27_yellow_6)).

fof(dt_k13_yellow_6,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1)
        & m4_yellow_6(X2,X1) )
     => ( v1_pre_topc(k13_yellow_6(X1,X2))
        & l1_pre_topc(k13_yellow_6(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t50_yellow_6.p',dt_k13_yellow_6)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t50_yellow_6.p',t4_subset)).

fof(d5_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> r2_hidden(X2,u1_pre_topc(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t50_yellow_6.p',d5_pre_topc)).

fof(fraenkel_a_2_1_yellow_6,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X2)
        & l1_struct_0(X2)
        & m4_yellow_6(X3,X2) )
     => ( r2_hidden(X1,a_2_1_yellow_6(X2,X3))
      <=> ? [X4] :
            ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
            & X1 = X4
            & ! [X5] :
                ( m1_subset_1(X5,u1_struct_0(X2))
               => ( r2_hidden(X5,X4)
                 => ! [X6] :
                      ( ( ~ v2_struct_0(X6)
                        & v4_orders_2(X6)
                        & v7_waybel_0(X6)
                        & l1_waybel_0(X6,X2) )
                     => ( r2_hidden(k4_tarski(X6,X5),X3)
                       => r1_waybel_0(X2,X6,X4) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t50_yellow_6.p',fraenkel_a_2_1_yellow_6)).

fof(dt_u1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t50_yellow_6.p',dt_u1_pre_topc)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_struct_0(X1) )
       => ! [X2] :
            ( ( v8_yellow_6(X2,X1)
              & m4_yellow_6(X2,X1) )
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k13_yellow_6(X1,X2))))
               => ( v3_pre_topc(X3,k13_yellow_6(X1,X2))
                <=> ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( r2_hidden(X4,X3)
                       => ! [X5] :
                            ( ( ~ v2_struct_0(X5)
                              & v4_orders_2(X5)
                              & v7_waybel_0(X5)
                              & l1_waybel_0(X5,X1) )
                           => ( r2_hidden(k4_tarski(X5,X4),X2)
                             => r1_waybel_0(X1,X5,X3) ) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t50_yellow_6])).

fof(c_0_8,plain,(
    ! [X17,X18,X19] :
      ( ( u1_struct_0(X19) = u1_struct_0(X17)
        | X19 != k13_yellow_6(X17,X18)
        | ~ v1_pre_topc(X19)
        | ~ l1_pre_topc(X19)
        | ~ m4_yellow_6(X18,X17)
        | v2_struct_0(X17)
        | ~ l1_struct_0(X17) )
      & ( u1_pre_topc(X19) = a_2_1_yellow_6(X17,X18)
        | X19 != k13_yellow_6(X17,X18)
        | ~ v1_pre_topc(X19)
        | ~ l1_pre_topc(X19)
        | ~ m4_yellow_6(X18,X17)
        | v2_struct_0(X17)
        | ~ l1_struct_0(X17) )
      & ( u1_struct_0(X19) != u1_struct_0(X17)
        | u1_pre_topc(X19) != a_2_1_yellow_6(X17,X18)
        | X19 = k13_yellow_6(X17,X18)
        | ~ v1_pre_topc(X19)
        | ~ l1_pre_topc(X19)
        | ~ m4_yellow_6(X18,X17)
        | v2_struct_0(X17)
        | ~ l1_struct_0(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d27_yellow_6])])])])])).

fof(c_0_9,plain,(
    ! [X24,X25] :
      ( ( v1_pre_topc(k13_yellow_6(X24,X25))
        | v2_struct_0(X24)
        | ~ l1_struct_0(X24)
        | ~ m4_yellow_6(X25,X24) )
      & ( l1_pre_topc(k13_yellow_6(X24,X25))
        | v2_struct_0(X24)
        | ~ l1_struct_0(X24)
        | ~ m4_yellow_6(X25,X24) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k13_yellow_6])])])])).

fof(c_0_10,plain,(
    ! [X71,X72,X73] :
      ( ~ r2_hidden(X71,X72)
      | ~ m1_subset_1(X72,k1_zfmisc_1(X73))
      | m1_subset_1(X71,X73) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_11,negated_conjecture,(
    ! [X12,X13] :
      ( ~ v2_struct_0(esk1_0)
      & l1_struct_0(esk1_0)
      & v8_yellow_6(esk2_0,esk1_0)
      & m4_yellow_6(esk2_0,esk1_0)
      & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(k13_yellow_6(esk1_0,esk2_0))))
      & ( m1_subset_1(esk4_0,u1_struct_0(esk1_0))
        | ~ v3_pre_topc(esk3_0,k13_yellow_6(esk1_0,esk2_0)) )
      & ( r2_hidden(esk4_0,esk3_0)
        | ~ v3_pre_topc(esk3_0,k13_yellow_6(esk1_0,esk2_0)) )
      & ( ~ v2_struct_0(esk5_0)
        | ~ v3_pre_topc(esk3_0,k13_yellow_6(esk1_0,esk2_0)) )
      & ( v4_orders_2(esk5_0)
        | ~ v3_pre_topc(esk3_0,k13_yellow_6(esk1_0,esk2_0)) )
      & ( v7_waybel_0(esk5_0)
        | ~ v3_pre_topc(esk3_0,k13_yellow_6(esk1_0,esk2_0)) )
      & ( l1_waybel_0(esk5_0,esk1_0)
        | ~ v3_pre_topc(esk3_0,k13_yellow_6(esk1_0,esk2_0)) )
      & ( r2_hidden(k4_tarski(esk5_0,esk4_0),esk2_0)
        | ~ v3_pre_topc(esk3_0,k13_yellow_6(esk1_0,esk2_0)) )
      & ( ~ r1_waybel_0(esk1_0,esk5_0,esk3_0)
        | ~ v3_pre_topc(esk3_0,k13_yellow_6(esk1_0,esk2_0)) )
      & ( v3_pre_topc(esk3_0,k13_yellow_6(esk1_0,esk2_0))
        | ~ m1_subset_1(X12,u1_struct_0(esk1_0))
        | ~ r2_hidden(X12,esk3_0)
        | v2_struct_0(X13)
        | ~ v4_orders_2(X13)
        | ~ v7_waybel_0(X13)
        | ~ l1_waybel_0(X13,esk1_0)
        | ~ r2_hidden(k4_tarski(X13,X12),esk2_0)
        | r1_waybel_0(esk1_0,X13,esk3_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])])])).

cnf(c_0_12,plain,
    ( u1_struct_0(X1) = u1_struct_0(X2)
    | v2_struct_0(X2)
    | X1 != k13_yellow_6(X2,X3)
    | ~ v1_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m4_yellow_6(X3,X2)
    | ~ l1_struct_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( l1_pre_topc(k13_yellow_6(X1,X2))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ m4_yellow_6(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( v1_pre_topc(k13_yellow_6(X1,X2))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ m4_yellow_6(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_15,plain,(
    ! [X20,X21] :
      ( ( ~ v3_pre_topc(X21,X20)
        | r2_hidden(X21,u1_pre_topc(X20))
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))
        | ~ l1_pre_topc(X20) )
      & ( ~ r2_hidden(X21,u1_pre_topc(X20))
        | v3_pre_topc(X21,X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))
        | ~ l1_pre_topc(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).

fof(c_0_16,plain,(
    ! [X40,X41,X42,X44,X45,X46] :
      ( ( m1_subset_1(esk12_3(X40,X41,X42),k1_zfmisc_1(u1_struct_0(X41)))
        | ~ r2_hidden(X40,a_2_1_yellow_6(X41,X42))
        | v2_struct_0(X41)
        | ~ l1_struct_0(X41)
        | ~ m4_yellow_6(X42,X41) )
      & ( X40 = esk12_3(X40,X41,X42)
        | ~ r2_hidden(X40,a_2_1_yellow_6(X41,X42))
        | v2_struct_0(X41)
        | ~ l1_struct_0(X41)
        | ~ m4_yellow_6(X42,X41) )
      & ( ~ m1_subset_1(X44,u1_struct_0(X41))
        | ~ r2_hidden(X44,esk12_3(X40,X41,X42))
        | v2_struct_0(X45)
        | ~ v4_orders_2(X45)
        | ~ v7_waybel_0(X45)
        | ~ l1_waybel_0(X45,X41)
        | ~ r2_hidden(k4_tarski(X45,X44),X42)
        | r1_waybel_0(X41,X45,esk12_3(X40,X41,X42))
        | ~ r2_hidden(X40,a_2_1_yellow_6(X41,X42))
        | v2_struct_0(X41)
        | ~ l1_struct_0(X41)
        | ~ m4_yellow_6(X42,X41) )
      & ( m1_subset_1(esk13_4(X40,X41,X42,X46),u1_struct_0(X41))
        | ~ m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X41)))
        | X40 != X46
        | r2_hidden(X40,a_2_1_yellow_6(X41,X42))
        | v2_struct_0(X41)
        | ~ l1_struct_0(X41)
        | ~ m4_yellow_6(X42,X41) )
      & ( r2_hidden(esk13_4(X40,X41,X42,X46),X46)
        | ~ m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X41)))
        | X40 != X46
        | r2_hidden(X40,a_2_1_yellow_6(X41,X42))
        | v2_struct_0(X41)
        | ~ l1_struct_0(X41)
        | ~ m4_yellow_6(X42,X41) )
      & ( ~ v2_struct_0(esk14_4(X40,X41,X42,X46))
        | ~ m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X41)))
        | X40 != X46
        | r2_hidden(X40,a_2_1_yellow_6(X41,X42))
        | v2_struct_0(X41)
        | ~ l1_struct_0(X41)
        | ~ m4_yellow_6(X42,X41) )
      & ( v4_orders_2(esk14_4(X40,X41,X42,X46))
        | ~ m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X41)))
        | X40 != X46
        | r2_hidden(X40,a_2_1_yellow_6(X41,X42))
        | v2_struct_0(X41)
        | ~ l1_struct_0(X41)
        | ~ m4_yellow_6(X42,X41) )
      & ( v7_waybel_0(esk14_4(X40,X41,X42,X46))
        | ~ m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X41)))
        | X40 != X46
        | r2_hidden(X40,a_2_1_yellow_6(X41,X42))
        | v2_struct_0(X41)
        | ~ l1_struct_0(X41)
        | ~ m4_yellow_6(X42,X41) )
      & ( l1_waybel_0(esk14_4(X40,X41,X42,X46),X41)
        | ~ m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X41)))
        | X40 != X46
        | r2_hidden(X40,a_2_1_yellow_6(X41,X42))
        | v2_struct_0(X41)
        | ~ l1_struct_0(X41)
        | ~ m4_yellow_6(X42,X41) )
      & ( r2_hidden(k4_tarski(esk14_4(X40,X41,X42,X46),esk13_4(X40,X41,X42,X46)),X42)
        | ~ m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X41)))
        | X40 != X46
        | r2_hidden(X40,a_2_1_yellow_6(X41,X42))
        | v2_struct_0(X41)
        | ~ l1_struct_0(X41)
        | ~ m4_yellow_6(X42,X41) )
      & ( ~ r1_waybel_0(X41,esk14_4(X40,X41,X42,X46),X46)
        | ~ m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X41)))
        | X40 != X46
        | r2_hidden(X40,a_2_1_yellow_6(X41,X42))
        | v2_struct_0(X41)
        | ~ l1_struct_0(X41)
        | ~ m4_yellow_6(X42,X41) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_1_yellow_6])])])])])])).

cnf(c_0_17,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(k13_yellow_6(esk1_0,esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( u1_struct_0(k13_yellow_6(X1,X2)) = u1_struct_0(X1)
    | v2_struct_0(X1)
    | ~ m4_yellow_6(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_12]),c_0_13]),c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( m4_yellow_6(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_21,negated_conjecture,
    ( l1_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_22,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,u1_pre_topc(X2))
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( u1_pre_topc(X1) = a_2_1_yellow_6(X2,X3)
    | v2_struct_0(X2)
    | X1 != k13_yellow_6(X2,X3)
    | ~ v1_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m4_yellow_6(X3,X2)
    | ~ l1_struct_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_25,plain,
    ( r2_hidden(k4_tarski(esk14_4(X1,X2,X3,X4),esk13_4(X1,X2,X3,X4)),X3)
    | r2_hidden(X1,a_2_1_yellow_6(X2,X3))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | X1 != X4
    | ~ l1_struct_0(X2)
    | ~ m4_yellow_6(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(k13_yellow_6(esk1_0,esk2_0)))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_27,negated_conjecture,
    ( u1_struct_0(k13_yellow_6(esk1_0,esk2_0)) = u1_struct_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_28,plain,
    ( v4_orders_2(esk14_4(X1,X2,X3,X4))
    | r2_hidden(X1,a_2_1_yellow_6(X2,X3))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | X1 != X4
    | ~ l1_struct_0(X2)
    | ~ m4_yellow_6(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_29,plain,
    ( v7_waybel_0(esk14_4(X1,X2,X3,X4))
    | r2_hidden(X1,a_2_1_yellow_6(X2,X3))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | X1 != X4
    | ~ l1_struct_0(X2)
    | ~ m4_yellow_6(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,a_2_1_yellow_6(X2,X3))
    | v2_struct_0(X2)
    | ~ v2_struct_0(esk14_4(X1,X2,X3,X4))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | X1 != X4
    | ~ l1_struct_0(X2)
    | ~ m4_yellow_6(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_31,plain,
    ( l1_waybel_0(esk14_4(X1,X2,X3,X4),X2)
    | r2_hidden(X1,a_2_1_yellow_6(X2,X3))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | X1 != X4
    | ~ l1_struct_0(X2)
    | ~ m4_yellow_6(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk3_0,u1_pre_topc(k13_yellow_6(esk1_0,esk2_0)))
    | ~ l1_pre_topc(k13_yellow_6(esk1_0,esk2_0))
    | ~ v3_pre_topc(esk3_0,k13_yellow_6(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_18])).

cnf(c_0_33,negated_conjecture,
    ( l1_pre_topc(k13_yellow_6(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_34,plain,
    ( u1_pre_topc(k13_yellow_6(X1,X2)) = a_2_1_yellow_6(X1,X2)
    | v2_struct_0(X1)
    | ~ m4_yellow_6(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_24]),c_0_13]),c_0_14])).

cnf(c_0_35,negated_conjecture,
    ( v3_pre_topc(esk3_0,k13_yellow_6(esk1_0,esk2_0))
    | v2_struct_0(X2)
    | r1_waybel_0(esk1_0,X2,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ r2_hidden(X1,esk3_0)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,esk1_0)
    | ~ r2_hidden(k4_tarski(X2,X1),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_36,plain,
    ( r2_hidden(k4_tarski(esk14_4(X1,X2,X3,X1),esk13_4(X1,X2,X3,X1)),X3)
    | r2_hidden(X1,a_2_1_yellow_6(X2,X3))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m4_yellow_6(X3,X2)
    | ~ l1_struct_0(X2) ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(rw,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_38,plain,
    ( v4_orders_2(esk14_4(X1,X2,X3,X1))
    | r2_hidden(X1,a_2_1_yellow_6(X2,X3))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m4_yellow_6(X3,X2)
    | ~ l1_struct_0(X2) ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_39,plain,
    ( v7_waybel_0(esk14_4(X1,X2,X3,X1))
    | r2_hidden(X1,a_2_1_yellow_6(X2,X3))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m4_yellow_6(X3,X2)
    | ~ l1_struct_0(X2) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,a_2_1_yellow_6(X2,X3))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m4_yellow_6(X3,X2)
    | ~ l1_struct_0(X2)
    | ~ v2_struct_0(esk14_4(X1,X2,X3,X1)) ),
    inference(er,[status(thm)],[c_0_30])).

cnf(c_0_41,plain,
    ( l1_waybel_0(esk14_4(X1,X2,X3,X1),X2)
    | r2_hidden(X1,a_2_1_yellow_6(X2,X3))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m4_yellow_6(X3,X2)
    | ~ l1_struct_0(X2) ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(rw,[status(thm)],[c_0_18,c_0_27])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk3_0,u1_pre_topc(k13_yellow_6(esk1_0,esk2_0)))
    | ~ v3_pre_topc(esk3_0,k13_yellow_6(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_33])])).

cnf(c_0_44,negated_conjecture,
    ( u1_pre_topc(k13_yellow_6(esk1_0,esk2_0)) = a_2_1_yellow_6(esk1_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_45,plain,
    ( r2_hidden(X2,a_2_1_yellow_6(X1,X3))
    | v2_struct_0(X1)
    | ~ r1_waybel_0(X1,esk14_4(X2,X1,X3,X4),X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | X2 != X4
    | ~ l1_struct_0(X1)
    | ~ m4_yellow_6(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_46,negated_conjecture,
    ( r1_waybel_0(esk1_0,esk14_4(X1,X2,esk2_0,X1),esk3_0)
    | r2_hidden(X1,a_2_1_yellow_6(X2,esk2_0))
    | v3_pre_topc(esk3_0,k13_yellow_6(esk1_0,esk2_0))
    | v2_struct_0(X2)
    | ~ l1_waybel_0(esk14_4(X1,X2,esk2_0,X1),esk1_0)
    | ~ r2_hidden(esk13_4(X1,X2,esk2_0,X1),esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m4_yellow_6(esk2_0,X2)
    | ~ l1_struct_0(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37]),c_0_38]),c_0_39]),c_0_40])).

cnf(c_0_47,negated_conjecture,
    ( l1_waybel_0(esk14_4(esk3_0,esk1_0,X1,esk3_0),esk1_0)
    | r2_hidden(esk3_0,a_2_1_yellow_6(esk1_0,X1))
    | ~ m4_yellow_6(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_21])]),c_0_22])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk3_0,a_2_1_yellow_6(esk1_0,esk2_0))
    | ~ v3_pre_topc(esk3_0,k13_yellow_6(esk1_0,esk2_0)) ),
    inference(rw,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_49,plain,
    ( r2_hidden(esk13_4(X1,X2,X3,X4),X4)
    | r2_hidden(X1,a_2_1_yellow_6(X2,X3))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | X1 != X4
    | ~ l1_struct_0(X2)
    | ~ m4_yellow_6(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_50,plain,
    ( v3_pre_topc(X1,X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_51,plain,
    ( r2_hidden(X1,a_2_1_yellow_6(X2,X3))
    | v2_struct_0(X2)
    | ~ r1_waybel_0(X2,esk14_4(X1,X2,X3,X1),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m4_yellow_6(X3,X2)
    | ~ l1_struct_0(X2) ),
    inference(er,[status(thm)],[c_0_45])).

cnf(c_0_52,negated_conjecture,
    ( r1_waybel_0(esk1_0,esk14_4(esk3_0,esk1_0,esk2_0,esk3_0),esk3_0)
    | r2_hidden(esk3_0,a_2_1_yellow_6(esk1_0,esk2_0))
    | ~ r2_hidden(esk13_4(esk3_0,esk1_0,esk2_0,esk3_0),esk3_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_42]),c_0_20]),c_0_21])]),c_0_22]),c_0_48])).

cnf(c_0_53,plain,
    ( r2_hidden(esk13_4(X1,X2,X3,X1),X1)
    | r2_hidden(X1,a_2_1_yellow_6(X2,X3))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m4_yellow_6(X3,X2)
    | ~ l1_struct_0(X2) ),
    inference(er,[status(thm)],[c_0_49])).

cnf(c_0_54,negated_conjecture,
    ( v3_pre_topc(esk3_0,k13_yellow_6(esk1_0,esk2_0))
    | ~ l1_pre_topc(k13_yellow_6(esk1_0,esk2_0))
    | ~ r2_hidden(esk3_0,u1_pre_topc(k13_yellow_6(esk1_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_50,c_0_18])).

fof(c_0_55,plain,(
    ! [X30] :
      ( ~ l1_pre_topc(X30)
      | m1_subset_1(u1_pre_topc(X30),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X30)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk3_0,a_2_1_yellow_6(esk1_0,esk2_0))
    | ~ r2_hidden(esk13_4(esk3_0,esk1_0,esk2_0,esk3_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_42]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(esk13_4(esk3_0,esk1_0,X1,esk3_0),esk3_0)
    | r2_hidden(esk3_0,a_2_1_yellow_6(esk1_0,X1))
    | ~ m4_yellow_6(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_42]),c_0_21])]),c_0_22])).

cnf(c_0_58,negated_conjecture,
    ( v3_pre_topc(esk3_0,k13_yellow_6(esk1_0,esk2_0))
    | ~ r2_hidden(esk3_0,u1_pre_topc(k13_yellow_6(esk1_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_33])])).

cnf(c_0_59,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_60,plain,
    ( X1 = esk12_3(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_1_yellow_6(X2,X3))
    | ~ l1_struct_0(X2)
    | ~ m4_yellow_6(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(esk3_0,a_2_1_yellow_6(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_20])])).

cnf(c_0_62,negated_conjecture,
    ( l1_waybel_0(esk5_0,esk1_0)
    | ~ v3_pre_topc(esk3_0,k13_yellow_6(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_63,negated_conjecture,
    ( v3_pre_topc(esk3_0,k13_yellow_6(esk1_0,esk2_0))
    | ~ r2_hidden(esk3_0,a_2_1_yellow_6(esk1_0,esk2_0)) ),
    inference(rw,[status(thm)],[c_0_58,c_0_44])).

cnf(c_0_64,negated_conjecture,
    ( v7_waybel_0(esk5_0)
    | ~ v3_pre_topc(esk3_0,k13_yellow_6(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_65,negated_conjecture,
    ( v4_orders_2(esk5_0)
    | ~ v3_pre_topc(esk3_0,k13_yellow_6(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(esk4_0,esk3_0)
    | ~ v3_pre_topc(esk3_0,k13_yellow_6(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_67,negated_conjecture,
    ( ~ r1_waybel_0(esk1_0,esk5_0,esk3_0)
    | ~ v3_pre_topc(esk3_0,k13_yellow_6(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_68,negated_conjecture,
    ( m1_subset_1(u1_pre_topc(k13_yellow_6(esk1_0,esk2_0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_27]),c_0_33])])).

cnf(c_0_69,plain,
    ( v2_struct_0(X5)
    | r1_waybel_0(X2,X5,esk12_3(X3,X2,X4))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_hidden(X1,esk12_3(X3,X2,X4))
    | ~ v4_orders_2(X5)
    | ~ v7_waybel_0(X5)
    | ~ l1_waybel_0(X5,X2)
    | ~ r2_hidden(k4_tarski(X5,X1),X4)
    | ~ r2_hidden(X3,a_2_1_yellow_6(X2,X4))
    | ~ l1_struct_0(X2)
    | ~ m4_yellow_6(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_70,negated_conjecture,
    ( esk12_3(esk3_0,esk1_0,esk2_0) = esk3_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_71,negated_conjecture,
    ( l1_waybel_0(esk5_0,esk1_0)
    | ~ r2_hidden(esk3_0,a_2_1_yellow_6(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_72,negated_conjecture,
    ( v7_waybel_0(esk5_0)
    | ~ r2_hidden(esk3_0,a_2_1_yellow_6(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_63])).

cnf(c_0_73,negated_conjecture,
    ( v4_orders_2(esk5_0)
    | ~ r2_hidden(esk3_0,a_2_1_yellow_6(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_63])).

cnf(c_0_74,negated_conjecture,
    ( r2_hidden(esk4_0,esk3_0)
    | ~ r2_hidden(esk3_0,a_2_1_yellow_6(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_63])).

cnf(c_0_75,negated_conjecture,
    ( ~ r1_waybel_0(esk1_0,esk5_0,esk3_0)
    | ~ r2_hidden(esk3_0,a_2_1_yellow_6(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_63])).

cnf(c_0_76,negated_conjecture,
    ( m1_subset_1(a_2_1_yellow_6(esk1_0,esk2_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(rw,[status(thm)],[c_0_68,c_0_44])).

cnf(c_0_77,negated_conjecture,
    ( r1_waybel_0(esk1_0,X1,esk3_0)
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X1,esk1_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ r2_hidden(k4_tarski(X1,X2),esk2_0)
    | ~ r2_hidden(X2,esk3_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_61]),c_0_20]),c_0_21])]),c_0_22]),c_0_37])).

cnf(c_0_78,negated_conjecture,
    ( r2_hidden(k4_tarski(esk5_0,esk4_0),esk2_0)
    | ~ v3_pre_topc(esk3_0,k13_yellow_6(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_79,negated_conjecture,
    ( l1_waybel_0(esk5_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_61])])).

cnf(c_0_80,negated_conjecture,
    ( v7_waybel_0(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_72,c_0_61])])).

cnf(c_0_81,negated_conjecture,
    ( v4_orders_2(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_61])])).

cnf(c_0_82,negated_conjecture,
    ( r2_hidden(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_61])])).

cnf(c_0_83,negated_conjecture,
    ( ~ r1_waybel_0(esk1_0,esk5_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_61])])).

cnf(c_0_84,negated_conjecture,
    ( ~ v2_struct_0(esk5_0)
    | ~ v3_pre_topc(esk3_0,k13_yellow_6(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_85,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r2_hidden(X1,a_2_1_yellow_6(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_76])).

cnf(c_0_86,negated_conjecture,
    ( ~ v3_pre_topc(esk3_0,k13_yellow_6(esk1_0,esk2_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_79]),c_0_80]),c_0_81]),c_0_82])]),c_0_83]),c_0_84])).

cnf(c_0_87,negated_conjecture,
    ( v3_pre_topc(X1,k13_yellow_6(esk1_0,esk2_0))
    | ~ r2_hidden(X1,a_2_1_yellow_6(esk1_0,esk2_0)) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_27]),c_0_33])]),c_0_44]),c_0_85])).

cnf(c_0_88,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_61])]),
    [proof]).
%------------------------------------------------------------------------------
