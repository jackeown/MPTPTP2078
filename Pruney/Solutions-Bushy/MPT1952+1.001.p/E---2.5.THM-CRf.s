%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1952+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:04 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   93 (4329 expanded)
%              Number of clauses        :   80 (1604 expanded)
%              Number of leaves         :    6 (1047 expanded)
%              Depth                    :   16
%              Number of atoms          :  488 (52711 expanded)
%              Number of equality atoms :   37 (2136 expanded)
%              Maximal formula depth    :   25 (   5 average)
%              Maximal clause size      :   78 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d27_yellow_6)).

fof(dt_k13_yellow_6,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1)
        & m4_yellow_6(X2,X1) )
     => ( v1_pre_topc(k13_yellow_6(X1,X2))
        & l1_pre_topc(k13_yellow_6(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k13_yellow_6)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_yellow_6)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_1_yellow_6)).

fof(d5_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> r2_hidden(X2,u1_pre_topc(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

fof(c_0_6,plain,(
    ! [X7,X8,X9] :
      ( ( u1_struct_0(X9) = u1_struct_0(X7)
        | X9 != k13_yellow_6(X7,X8)
        | ~ v1_pre_topc(X9)
        | ~ l1_pre_topc(X9)
        | ~ m4_yellow_6(X8,X7)
        | v2_struct_0(X7)
        | ~ l1_struct_0(X7) )
      & ( u1_pre_topc(X9) = a_2_1_yellow_6(X7,X8)
        | X9 != k13_yellow_6(X7,X8)
        | ~ v1_pre_topc(X9)
        | ~ l1_pre_topc(X9)
        | ~ m4_yellow_6(X8,X7)
        | v2_struct_0(X7)
        | ~ l1_struct_0(X7) )
      & ( u1_struct_0(X9) != u1_struct_0(X7)
        | u1_pre_topc(X9) != a_2_1_yellow_6(X7,X8)
        | X9 = k13_yellow_6(X7,X8)
        | ~ v1_pre_topc(X9)
        | ~ l1_pre_topc(X9)
        | ~ m4_yellow_6(X8,X7)
        | v2_struct_0(X7)
        | ~ l1_struct_0(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d27_yellow_6])])])])])).

fof(c_0_7,plain,(
    ! [X12,X13] :
      ( ( v1_pre_topc(k13_yellow_6(X12,X13))
        | v2_struct_0(X12)
        | ~ l1_struct_0(X12)
        | ~ m4_yellow_6(X13,X12) )
      & ( l1_pre_topc(k13_yellow_6(X12,X13))
        | v2_struct_0(X12)
        | ~ l1_struct_0(X12)
        | ~ m4_yellow_6(X13,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k13_yellow_6])])])])).

fof(c_0_8,negated_conjecture,(
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

cnf(c_0_9,plain,
    ( u1_struct_0(X1) = u1_struct_0(X2)
    | v2_struct_0(X2)
    | X1 != k13_yellow_6(X2,X3)
    | ~ v1_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m4_yellow_6(X3,X2)
    | ~ l1_struct_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( v1_pre_topc(k13_yellow_6(X1,X2))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ m4_yellow_6(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( l1_pre_topc(k13_yellow_6(X1,X2))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ m4_yellow_6(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_12,negated_conjecture,(
    ! [X31,X32] :
      ( ~ v2_struct_0(esk4_0)
      & l1_struct_0(esk4_0)
      & v8_yellow_6(esk5_0,esk4_0)
      & m4_yellow_6(esk5_0,esk4_0)
      & m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(k13_yellow_6(esk4_0,esk5_0))))
      & ( m1_subset_1(esk7_0,u1_struct_0(esk4_0))
        | ~ v3_pre_topc(esk6_0,k13_yellow_6(esk4_0,esk5_0)) )
      & ( r2_hidden(esk7_0,esk6_0)
        | ~ v3_pre_topc(esk6_0,k13_yellow_6(esk4_0,esk5_0)) )
      & ( ~ v2_struct_0(esk8_0)
        | ~ v3_pre_topc(esk6_0,k13_yellow_6(esk4_0,esk5_0)) )
      & ( v4_orders_2(esk8_0)
        | ~ v3_pre_topc(esk6_0,k13_yellow_6(esk4_0,esk5_0)) )
      & ( v7_waybel_0(esk8_0)
        | ~ v3_pre_topc(esk6_0,k13_yellow_6(esk4_0,esk5_0)) )
      & ( l1_waybel_0(esk8_0,esk4_0)
        | ~ v3_pre_topc(esk6_0,k13_yellow_6(esk4_0,esk5_0)) )
      & ( r2_hidden(k4_tarski(esk8_0,esk7_0),esk5_0)
        | ~ v3_pre_topc(esk6_0,k13_yellow_6(esk4_0,esk5_0)) )
      & ( ~ r1_waybel_0(esk4_0,esk8_0,esk6_0)
        | ~ v3_pre_topc(esk6_0,k13_yellow_6(esk4_0,esk5_0)) )
      & ( v3_pre_topc(esk6_0,k13_yellow_6(esk4_0,esk5_0))
        | ~ m1_subset_1(X31,u1_struct_0(esk4_0))
        | ~ r2_hidden(X31,esk6_0)
        | v2_struct_0(X32)
        | ~ v4_orders_2(X32)
        | ~ v7_waybel_0(X32)
        | ~ l1_waybel_0(X32,esk4_0)
        | ~ r2_hidden(k4_tarski(X32,X31),esk5_0)
        | r1_waybel_0(esk4_0,X32,esk6_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])])])).

fof(c_0_13,plain,(
    ! [X23,X24,X25] :
      ( ~ r2_hidden(X23,X24)
      | ~ m1_subset_1(X24,k1_zfmisc_1(X25))
      | m1_subset_1(X23,X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_14,plain,(
    ! [X14,X15,X16,X18,X19,X20] :
      ( ( m1_subset_1(esk1_3(X14,X15,X16),k1_zfmisc_1(u1_struct_0(X15)))
        | ~ r2_hidden(X14,a_2_1_yellow_6(X15,X16))
        | v2_struct_0(X15)
        | ~ l1_struct_0(X15)
        | ~ m4_yellow_6(X16,X15) )
      & ( X14 = esk1_3(X14,X15,X16)
        | ~ r2_hidden(X14,a_2_1_yellow_6(X15,X16))
        | v2_struct_0(X15)
        | ~ l1_struct_0(X15)
        | ~ m4_yellow_6(X16,X15) )
      & ( ~ m1_subset_1(X18,u1_struct_0(X15))
        | ~ r2_hidden(X18,esk1_3(X14,X15,X16))
        | v2_struct_0(X19)
        | ~ v4_orders_2(X19)
        | ~ v7_waybel_0(X19)
        | ~ l1_waybel_0(X19,X15)
        | ~ r2_hidden(k4_tarski(X19,X18),X16)
        | r1_waybel_0(X15,X19,esk1_3(X14,X15,X16))
        | ~ r2_hidden(X14,a_2_1_yellow_6(X15,X16))
        | v2_struct_0(X15)
        | ~ l1_struct_0(X15)
        | ~ m4_yellow_6(X16,X15) )
      & ( m1_subset_1(esk2_4(X14,X15,X16,X20),u1_struct_0(X15))
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X15)))
        | X14 != X20
        | r2_hidden(X14,a_2_1_yellow_6(X15,X16))
        | v2_struct_0(X15)
        | ~ l1_struct_0(X15)
        | ~ m4_yellow_6(X16,X15) )
      & ( r2_hidden(esk2_4(X14,X15,X16,X20),X20)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X15)))
        | X14 != X20
        | r2_hidden(X14,a_2_1_yellow_6(X15,X16))
        | v2_struct_0(X15)
        | ~ l1_struct_0(X15)
        | ~ m4_yellow_6(X16,X15) )
      & ( ~ v2_struct_0(esk3_4(X14,X15,X16,X20))
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X15)))
        | X14 != X20
        | r2_hidden(X14,a_2_1_yellow_6(X15,X16))
        | v2_struct_0(X15)
        | ~ l1_struct_0(X15)
        | ~ m4_yellow_6(X16,X15) )
      & ( v4_orders_2(esk3_4(X14,X15,X16,X20))
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X15)))
        | X14 != X20
        | r2_hidden(X14,a_2_1_yellow_6(X15,X16))
        | v2_struct_0(X15)
        | ~ l1_struct_0(X15)
        | ~ m4_yellow_6(X16,X15) )
      & ( v7_waybel_0(esk3_4(X14,X15,X16,X20))
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X15)))
        | X14 != X20
        | r2_hidden(X14,a_2_1_yellow_6(X15,X16))
        | v2_struct_0(X15)
        | ~ l1_struct_0(X15)
        | ~ m4_yellow_6(X16,X15) )
      & ( l1_waybel_0(esk3_4(X14,X15,X16,X20),X15)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X15)))
        | X14 != X20
        | r2_hidden(X14,a_2_1_yellow_6(X15,X16))
        | v2_struct_0(X15)
        | ~ l1_struct_0(X15)
        | ~ m4_yellow_6(X16,X15) )
      & ( r2_hidden(k4_tarski(esk3_4(X14,X15,X16,X20),esk2_4(X14,X15,X16,X20)),X16)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X15)))
        | X14 != X20
        | r2_hidden(X14,a_2_1_yellow_6(X15,X16))
        | v2_struct_0(X15)
        | ~ l1_struct_0(X15)
        | ~ m4_yellow_6(X16,X15) )
      & ( ~ r1_waybel_0(X15,esk3_4(X14,X15,X16,X20),X20)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X15)))
        | X14 != X20
        | r2_hidden(X14,a_2_1_yellow_6(X15,X16))
        | v2_struct_0(X15)
        | ~ l1_struct_0(X15)
        | ~ m4_yellow_6(X16,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_1_yellow_6])])])])])])).

cnf(c_0_15,plain,
    ( u1_struct_0(k13_yellow_6(X1,X2)) = u1_struct_0(X1)
    | v2_struct_0(X1)
    | ~ m4_yellow_6(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_9]),c_0_10]),c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( m4_yellow_6(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( l1_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(k13_yellow_6(esk4_0,esk5_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,plain,
    ( r2_hidden(k4_tarski(esk3_4(X1,X2,X3,X4),esk2_4(X1,X2,X3,X4)),X3)
    | r2_hidden(X1,a_2_1_yellow_6(X2,X3))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | X1 != X4
    | ~ l1_struct_0(X2)
    | ~ m4_yellow_6(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,negated_conjecture,
    ( u1_struct_0(k13_yellow_6(esk4_0,esk5_0)) = u1_struct_0(esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])]),c_0_18])).

cnf(c_0_23,plain,
    ( r2_hidden(esk2_4(X1,X2,X3,X4),X4)
    | r2_hidden(X1,a_2_1_yellow_6(X2,X3))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | X1 != X4
    | ~ l1_struct_0(X2)
    | ~ m4_yellow_6(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,plain,
    ( v4_orders_2(esk3_4(X1,X2,X3,X4))
    | r2_hidden(X1,a_2_1_yellow_6(X2,X3))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | X1 != X4
    | ~ l1_struct_0(X2)
    | ~ m4_yellow_6(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_25,plain,
    ( v7_waybel_0(esk3_4(X1,X2,X3,X4))
    | r2_hidden(X1,a_2_1_yellow_6(X2,X3))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | X1 != X4
    | ~ l1_struct_0(X2)
    | ~ m4_yellow_6(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_26,plain,
    ( l1_waybel_0(esk3_4(X1,X2,X3,X4),X2)
    | r2_hidden(X1,a_2_1_yellow_6(X2,X3))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | X1 != X4
    | ~ l1_struct_0(X2)
    | ~ m4_yellow_6(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_27,plain,(
    ! [X10,X11] :
      ( ( ~ v3_pre_topc(X11,X10)
        | r2_hidden(X11,u1_pre_topc(X10))
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
        | ~ l1_pre_topc(X10) )
      & ( ~ r2_hidden(X11,u1_pre_topc(X10))
        | v3_pre_topc(X11,X10)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
        | ~ l1_pre_topc(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(k13_yellow_6(esk4_0,esk5_0)))
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_29,plain,
    ( r2_hidden(k4_tarski(esk3_4(X1,X2,X3,X1),esk2_4(X1,X2,X3,X1)),X3)
    | r2_hidden(X1,a_2_1_yellow_6(X2,X3))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m4_yellow_6(X3,X2)
    | ~ l1_struct_0(X2) ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(rw,[status(thm)],[c_0_20,c_0_22])).

cnf(c_0_31,plain,
    ( r2_hidden(esk2_4(X1,X2,X3,X1),X1)
    | r2_hidden(X1,a_2_1_yellow_6(X2,X3))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m4_yellow_6(X3,X2)
    | ~ l1_struct_0(X2) ),
    inference(er,[status(thm)],[c_0_23])).

cnf(c_0_32,plain,
    ( v4_orders_2(esk3_4(X1,X2,X3,X1))
    | r2_hidden(X1,a_2_1_yellow_6(X2,X3))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m4_yellow_6(X3,X2)
    | ~ l1_struct_0(X2) ),
    inference(er,[status(thm)],[c_0_24])).

cnf(c_0_33,plain,
    ( v7_waybel_0(esk3_4(X1,X2,X3,X1))
    | r2_hidden(X1,a_2_1_yellow_6(X2,X3))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m4_yellow_6(X3,X2)
    | ~ l1_struct_0(X2) ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_34,plain,
    ( l1_waybel_0(esk3_4(X1,X2,X3,X1),X2)
    | r2_hidden(X1,a_2_1_yellow_6(X2,X3))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m4_yellow_6(X3,X2)
    | ~ l1_struct_0(X2) ),
    inference(er,[status(thm)],[c_0_26])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,u1_pre_topc(X2))
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,plain,
    ( u1_pre_topc(X1) = a_2_1_yellow_6(X2,X3)
    | v2_struct_0(X2)
    | X1 != k13_yellow_6(X2,X3)
    | ~ v1_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m4_yellow_6(X3,X2)
    | ~ l1_struct_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_37,negated_conjecture,
    ( v3_pre_topc(esk6_0,k13_yellow_6(esk4_0,esk5_0))
    | v2_struct_0(X2)
    | r1_waybel_0(esk4_0,X2,esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ r2_hidden(X1,esk6_0)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,esk4_0)
    | ~ r2_hidden(k4_tarski(X2,X1),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ r2_hidden(X1,esk6_0) ),
    inference(rw,[status(thm)],[c_0_28,c_0_22])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_4(esk6_0,esk4_0,X1,esk6_0),esk2_4(esk6_0,esk4_0,X1,esk6_0)),X1)
    | r2_hidden(esk6_0,a_2_1_yellow_6(esk4_0,X1))
    | ~ m4_yellow_6(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_17])]),c_0_18])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk2_4(esk6_0,esk4_0,X1,esk6_0),esk6_0)
    | r2_hidden(esk6_0,a_2_1_yellow_6(esk4_0,X1))
    | ~ m4_yellow_6(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_30]),c_0_17])]),c_0_18])).

cnf(c_0_41,negated_conjecture,
    ( v4_orders_2(esk3_4(esk6_0,esk4_0,X1,esk6_0))
    | r2_hidden(esk6_0,a_2_1_yellow_6(esk4_0,X1))
    | ~ m4_yellow_6(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_30]),c_0_17])]),c_0_18])).

cnf(c_0_42,negated_conjecture,
    ( v7_waybel_0(esk3_4(esk6_0,esk4_0,X1,esk6_0))
    | r2_hidden(esk6_0,a_2_1_yellow_6(esk4_0,X1))
    | ~ m4_yellow_6(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_30]),c_0_17])]),c_0_18])).

cnf(c_0_43,negated_conjecture,
    ( l1_waybel_0(esk3_4(esk6_0,esk4_0,X1,esk6_0),esk4_0)
    | r2_hidden(esk6_0,a_2_1_yellow_6(esk4_0,X1))
    | ~ m4_yellow_6(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_30]),c_0_17])]),c_0_18])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(X1,u1_pre_topc(k13_yellow_6(esk4_0,esk5_0)))
    | ~ v3_pre_topc(X1,k13_yellow_6(esk4_0,esk5_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ l1_pre_topc(k13_yellow_6(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_22])).

cnf(c_0_45,negated_conjecture,
    ( l1_pre_topc(k13_yellow_6(esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_16]),c_0_17])]),c_0_18])).

cnf(c_0_46,plain,
    ( u1_pre_topc(k13_yellow_6(X1,X2)) = a_2_1_yellow_6(X1,X2)
    | v2_struct_0(X1)
    | ~ m4_yellow_6(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_36]),c_0_10]),c_0_11])).

cnf(c_0_47,plain,
    ( r2_hidden(X2,a_2_1_yellow_6(X1,X3))
    | v2_struct_0(X1)
    | ~ r1_waybel_0(X1,esk3_4(X2,X1,X3,X4),X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | X2 != X4
    | ~ l1_struct_0(X1)
    | ~ m4_yellow_6(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_48,negated_conjecture,
    ( r1_waybel_0(esk4_0,X1,esk6_0)
    | v3_pre_topc(esk6_0,k13_yellow_6(esk4_0,esk5_0))
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X1,esk4_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ r2_hidden(k4_tarski(X1,X2),esk5_0)
    | ~ r2_hidden(X2,esk6_0) ),
    inference(csr,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_4(esk6_0,esk4_0,esk5_0,esk6_0),esk2_4(esk6_0,esk4_0,esk5_0,esk6_0)),esk5_0)
    | r2_hidden(esk6_0,a_2_1_yellow_6(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_16])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(esk2_4(esk6_0,esk4_0,esk5_0,esk6_0),esk6_0)
    | r2_hidden(esk6_0,a_2_1_yellow_6(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_16])).

cnf(c_0_51,negated_conjecture,
    ( v4_orders_2(esk3_4(esk6_0,esk4_0,esk5_0,esk6_0))
    | r2_hidden(esk6_0,a_2_1_yellow_6(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_16])).

cnf(c_0_52,negated_conjecture,
    ( v7_waybel_0(esk3_4(esk6_0,esk4_0,esk5_0,esk6_0))
    | r2_hidden(esk6_0,a_2_1_yellow_6(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_16])).

cnf(c_0_53,negated_conjecture,
    ( l1_waybel_0(esk3_4(esk6_0,esk4_0,esk5_0,esk6_0),esk4_0)
    | r2_hidden(esk6_0,a_2_1_yellow_6(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_16])).

cnf(c_0_54,plain,
    ( r2_hidden(X1,a_2_1_yellow_6(X2,X3))
    | v2_struct_0(X2)
    | ~ v2_struct_0(esk3_4(X1,X2,X3,X4))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | X1 != X4
    | ~ l1_struct_0(X2)
    | ~ m4_yellow_6(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(X1,u1_pre_topc(k13_yellow_6(esk4_0,esk5_0)))
    | ~ v3_pre_topc(X1,k13_yellow_6(esk4_0,esk5_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_45])])).

cnf(c_0_56,negated_conjecture,
    ( u1_pre_topc(k13_yellow_6(esk4_0,esk5_0)) = a_2_1_yellow_6(esk4_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_16]),c_0_17])]),c_0_18])).

cnf(c_0_57,plain,
    ( r2_hidden(X1,a_2_1_yellow_6(X2,X3))
    | v2_struct_0(X2)
    | ~ r1_waybel_0(X2,esk3_4(X1,X2,X3,X1),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m4_yellow_6(X3,X2)
    | ~ l1_struct_0(X2) ),
    inference(er,[status(thm)],[c_0_47])).

cnf(c_0_58,negated_conjecture,
    ( r1_waybel_0(esk4_0,esk3_4(esk6_0,esk4_0,esk5_0,esk6_0),esk6_0)
    | r2_hidden(esk6_0,a_2_1_yellow_6(esk4_0,esk5_0))
    | v3_pre_topc(esk6_0,k13_yellow_6(esk4_0,esk5_0))
    | v2_struct_0(esk3_4(esk6_0,esk4_0,esk5_0,esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50]),c_0_51]),c_0_52]),c_0_53])).

cnf(c_0_59,plain,
    ( v3_pre_topc(X1,X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_60,plain,
    ( r2_hidden(X1,a_2_1_yellow_6(X2,X3))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m4_yellow_6(X3,X2)
    | ~ l1_struct_0(X2)
    | ~ v2_struct_0(esk3_4(X1,X2,X3,X1)) ),
    inference(er,[status(thm)],[c_0_54])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(X1,a_2_1_yellow_6(esk4_0,esk5_0))
    | ~ v3_pre_topc(X1,k13_yellow_6(esk4_0,esk5_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(rw,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(esk6_0,a_2_1_yellow_6(esk4_0,esk5_0))
    | v3_pre_topc(esk6_0,k13_yellow_6(esk4_0,esk5_0))
    | v2_struct_0(esk3_4(esk6_0,esk4_0,esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_30]),c_0_16]),c_0_17])]),c_0_18])).

cnf(c_0_63,negated_conjecture,
    ( v3_pre_topc(X1,k13_yellow_6(esk4_0,esk5_0))
    | ~ r2_hidden(X1,u1_pre_topc(k13_yellow_6(esk4_0,esk5_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ l1_pre_topc(k13_yellow_6(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_22])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(esk6_0,a_2_1_yellow_6(esk4_0,X1))
    | ~ m4_yellow_6(X1,esk4_0)
    | ~ v2_struct_0(esk3_4(esk6_0,esk4_0,X1,esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_30]),c_0_17])]),c_0_18])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(esk6_0,a_2_1_yellow_6(esk4_0,esk5_0))
    | v2_struct_0(esk3_4(esk6_0,esk4_0,esk5_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_30])])).

cnf(c_0_66,negated_conjecture,
    ( v3_pre_topc(X1,k13_yellow_6(esk4_0,esk5_0))
    | ~ r2_hidden(X1,u1_pre_topc(k13_yellow_6(esk4_0,esk5_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_45])])).

cnf(c_0_67,plain,
    ( X1 = esk1_3(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_1_yellow_6(X2,X3))
    | ~ l1_struct_0(X2)
    | ~ m4_yellow_6(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_68,negated_conjecture,
    ( r2_hidden(esk6_0,a_2_1_yellow_6(esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_16])])).

cnf(c_0_69,negated_conjecture,
    ( r2_hidden(k4_tarski(esk8_0,esk7_0),esk5_0)
    | ~ v3_pre_topc(esk6_0,k13_yellow_6(esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_70,negated_conjecture,
    ( v3_pre_topc(X1,k13_yellow_6(esk4_0,esk5_0))
    | ~ r2_hidden(X1,a_2_1_yellow_6(esk4_0,esk5_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(rw,[status(thm)],[c_0_66,c_0_56])).

cnf(c_0_71,negated_conjecture,
    ( l1_waybel_0(esk8_0,esk4_0)
    | ~ v3_pre_topc(esk6_0,k13_yellow_6(esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_72,negated_conjecture,
    ( v7_waybel_0(esk8_0)
    | ~ v3_pre_topc(esk6_0,k13_yellow_6(esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_73,negated_conjecture,
    ( v4_orders_2(esk8_0)
    | ~ v3_pre_topc(esk6_0,k13_yellow_6(esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_74,negated_conjecture,
    ( r2_hidden(esk7_0,esk6_0)
    | ~ v3_pre_topc(esk6_0,k13_yellow_6(esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_75,plain,
    ( v2_struct_0(X5)
    | r1_waybel_0(X2,X5,esk1_3(X3,X2,X4))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_hidden(X1,esk1_3(X3,X2,X4))
    | ~ v4_orders_2(X5)
    | ~ v7_waybel_0(X5)
    | ~ l1_waybel_0(X5,X2)
    | ~ r2_hidden(k4_tarski(X5,X1),X4)
    | ~ r2_hidden(X3,a_2_1_yellow_6(X2,X4))
    | ~ l1_struct_0(X2)
    | ~ m4_yellow_6(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_76,negated_conjecture,
    ( esk1_3(esk6_0,esk4_0,esk5_0) = esk6_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_16]),c_0_17])]),c_0_18])).

cnf(c_0_77,negated_conjecture,
    ( r2_hidden(k4_tarski(esk8_0,esk7_0),esk5_0)
    | ~ r2_hidden(esk6_0,a_2_1_yellow_6(esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_30])])).

cnf(c_0_78,negated_conjecture,
    ( l1_waybel_0(esk8_0,esk4_0)
    | ~ r2_hidden(esk6_0,a_2_1_yellow_6(esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_70]),c_0_30])])).

cnf(c_0_79,negated_conjecture,
    ( v7_waybel_0(esk8_0)
    | ~ r2_hidden(esk6_0,a_2_1_yellow_6(esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_70]),c_0_30])])).

cnf(c_0_80,negated_conjecture,
    ( v4_orders_2(esk8_0)
    | ~ r2_hidden(esk6_0,a_2_1_yellow_6(esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_70]),c_0_30])])).

cnf(c_0_81,negated_conjecture,
    ( r2_hidden(esk7_0,esk6_0)
    | ~ r2_hidden(esk6_0,a_2_1_yellow_6(esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_70]),c_0_30])])).

cnf(c_0_82,negated_conjecture,
    ( r1_waybel_0(esk4_0,X1,esk6_0)
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X1,esk4_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ r2_hidden(k4_tarski(X1,X2),esk5_0)
    | ~ r2_hidden(X2,esk6_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_68]),c_0_16]),c_0_17])]),c_0_18]),c_0_38])).

cnf(c_0_83,negated_conjecture,
    ( r2_hidden(k4_tarski(esk8_0,esk7_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_77,c_0_68])])).

cnf(c_0_84,negated_conjecture,
    ( l1_waybel_0(esk8_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_68])])).

cnf(c_0_85,negated_conjecture,
    ( v7_waybel_0(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_68])])).

cnf(c_0_86,negated_conjecture,
    ( v4_orders_2(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_68])])).

cnf(c_0_87,negated_conjecture,
    ( r2_hidden(esk7_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_68])])).

cnf(c_0_88,negated_conjecture,
    ( ~ r1_waybel_0(esk4_0,esk8_0,esk6_0)
    | ~ v3_pre_topc(esk6_0,k13_yellow_6(esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_89,negated_conjecture,
    ( r1_waybel_0(esk4_0,esk8_0,esk6_0)
    | v2_struct_0(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_84]),c_0_85]),c_0_86]),c_0_87])])).

cnf(c_0_90,negated_conjecture,
    ( ~ v2_struct_0(esk8_0)
    | ~ v3_pre_topc(esk6_0,k13_yellow_6(esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_91,negated_conjecture,
    ( ~ v3_pre_topc(esk6_0,k13_yellow_6(esk4_0,esk5_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_90])).

cnf(c_0_92,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_70]),c_0_68]),c_0_30])]),
    [proof]).

%------------------------------------------------------------------------------
