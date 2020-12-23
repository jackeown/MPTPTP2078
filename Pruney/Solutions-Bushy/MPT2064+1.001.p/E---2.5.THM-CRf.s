%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT2064+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:11 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   97 (10891 expanded)
%              Number of clauses        :   76 (3392 expanded)
%              Number of leaves         :   11 (2604 expanded)
%              Depth                    :   14
%              Number of atoms          :  535 (145130 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :   23 (   6 average)
%              Maximal clause size      :   54 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t24_yellow19,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r2_hidden(X3,k2_pre_topc(X1,X2))
              <=> ? [X4] :
                    ( ~ v2_struct_0(X4)
                    & v4_orders_2(X4)
                    & v7_waybel_0(X4)
                    & v3_yellow_6(X4,X1)
                    & l1_waybel_0(X4,X1)
                    & r1_waybel_0(X1,X4,X2)
                    & r2_hidden(X3,k10_yellow_6(X1,X4)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_yellow19)).

fof(t29_waybel_9,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v4_orders_2(X2)
            & v7_waybel_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r2_hidden(X3,k10_yellow_6(X1,X2))
               => r3_waybel_9(X1,X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_waybel_9)).

fof(t23_yellow19,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r2_hidden(X3,k2_pre_topc(X1,X2))
              <=> ? [X4] :
                    ( ~ v2_struct_0(X4)
                    & v4_orders_2(X4)
                    & v7_waybel_0(X4)
                    & l1_waybel_0(X4,X1)
                    & r1_waybel_0(X1,X4,X2)
                    & r3_waybel_9(X1,X4,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_yellow19)).

fof(t32_waybel_9,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v4_orders_2(X2)
            & v7_waybel_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ~ ( r3_waybel_9(X1,X2,X3)
                  & ! [X4] :
                      ( m2_yellow_6(X4,X1,X2)
                     => ~ r2_hidden(X3,k10_yellow_6(X1,X4)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_waybel_9)).

fof(dt_m2_yellow_6,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1)
        & ~ v2_struct_0(X2)
        & v4_orders_2(X2)
        & v7_waybel_0(X2)
        & l1_waybel_0(X2,X1) )
     => ! [X3] :
          ( m2_yellow_6(X3,X1,X2)
         => ( ~ v2_struct_0(X3)
            & v4_orders_2(X3)
            & v7_waybel_0(X3)
            & l1_waybel_0(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_yellow_6)).

fof(t21_yellow19,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2,X3] :
          ( ( ~ v2_struct_0(X3)
            & v4_orders_2(X3)
            & v7_waybel_0(X3)
            & l1_waybel_0(X3,X1) )
         => ( r1_waybel_0(X1,X3,X2)
           => ! [X4] :
                ( m2_yellow_6(X4,X1,X3)
               => r1_waybel_0(X1,X4,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_yellow19)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(d19_yellow_6,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v4_orders_2(X2)
            & v7_waybel_0(X2)
            & l1_waybel_0(X2,X1) )
         => ( v3_yellow_6(X2,X1)
          <=> k10_yellow_6(X1,X2) != k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_yellow_6)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_xboole_0)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ( r2_hidden(X3,k2_pre_topc(X1,X2))
                <=> ? [X4] :
                      ( ~ v2_struct_0(X4)
                      & v4_orders_2(X4)
                      & v7_waybel_0(X4)
                      & v3_yellow_6(X4,X1)
                      & l1_waybel_0(X4,X1)
                      & r1_waybel_0(X1,X4,X2)
                      & r2_hidden(X3,k10_yellow_6(X1,X4)) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t24_yellow19])).

fof(c_0_12,plain,(
    ! [X22,X23,X24] :
      ( v2_struct_0(X22)
      | ~ v2_pre_topc(X22)
      | ~ l1_pre_topc(X22)
      | v2_struct_0(X23)
      | ~ v4_orders_2(X23)
      | ~ v7_waybel_0(X23)
      | ~ l1_waybel_0(X23,X22)
      | ~ m1_subset_1(X24,u1_struct_0(X22))
      | ~ r2_hidden(X24,k10_yellow_6(X22,X23))
      | r3_waybel_9(X22,X23,X24) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t29_waybel_9])])])])).

fof(c_0_13,negated_conjecture,(
    ! [X36] :
      ( ~ v2_struct_0(esk3_0)
      & v2_pre_topc(esk3_0)
      & l1_pre_topc(esk3_0)
      & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
      & m1_subset_1(esk5_0,u1_struct_0(esk3_0))
      & ( ~ r2_hidden(esk5_0,k2_pre_topc(esk3_0,esk4_0))
        | v2_struct_0(X36)
        | ~ v4_orders_2(X36)
        | ~ v7_waybel_0(X36)
        | ~ v3_yellow_6(X36,esk3_0)
        | ~ l1_waybel_0(X36,esk3_0)
        | ~ r1_waybel_0(esk3_0,X36,esk4_0)
        | ~ r2_hidden(esk5_0,k10_yellow_6(esk3_0,X36)) )
      & ( ~ v2_struct_0(esk6_0)
        | r2_hidden(esk5_0,k2_pre_topc(esk3_0,esk4_0)) )
      & ( v4_orders_2(esk6_0)
        | r2_hidden(esk5_0,k2_pre_topc(esk3_0,esk4_0)) )
      & ( v7_waybel_0(esk6_0)
        | r2_hidden(esk5_0,k2_pre_topc(esk3_0,esk4_0)) )
      & ( v3_yellow_6(esk6_0,esk3_0)
        | r2_hidden(esk5_0,k2_pre_topc(esk3_0,esk4_0)) )
      & ( l1_waybel_0(esk6_0,esk3_0)
        | r2_hidden(esk5_0,k2_pre_topc(esk3_0,esk4_0)) )
      & ( r1_waybel_0(esk3_0,esk6_0,esk4_0)
        | r2_hidden(esk5_0,k2_pre_topc(esk3_0,esk4_0)) )
      & ( r2_hidden(esk5_0,k10_yellow_6(esk3_0,esk6_0))
        | r2_hidden(esk5_0,k2_pre_topc(esk3_0,esk4_0)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])])])).

fof(c_0_14,plain,(
    ! [X17,X18,X19,X21] :
      ( ( ~ v2_struct_0(esk1_3(X17,X18,X19))
        | ~ r2_hidden(X19,k2_pre_topc(X17,X18))
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | v2_struct_0(X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( v4_orders_2(esk1_3(X17,X18,X19))
        | ~ r2_hidden(X19,k2_pre_topc(X17,X18))
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | v2_struct_0(X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( v7_waybel_0(esk1_3(X17,X18,X19))
        | ~ r2_hidden(X19,k2_pre_topc(X17,X18))
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | v2_struct_0(X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( l1_waybel_0(esk1_3(X17,X18,X19),X17)
        | ~ r2_hidden(X19,k2_pre_topc(X17,X18))
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | v2_struct_0(X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( r1_waybel_0(X17,esk1_3(X17,X18,X19),X18)
        | ~ r2_hidden(X19,k2_pre_topc(X17,X18))
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | v2_struct_0(X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( r3_waybel_9(X17,esk1_3(X17,X18,X19),X19)
        | ~ r2_hidden(X19,k2_pre_topc(X17,X18))
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | v2_struct_0(X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( v2_struct_0(X21)
        | ~ v4_orders_2(X21)
        | ~ v7_waybel_0(X21)
        | ~ l1_waybel_0(X21,X17)
        | ~ r1_waybel_0(X17,X21,X18)
        | ~ r3_waybel_9(X17,X21,X19)
        | r2_hidden(X19,k2_pre_topc(X17,X18))
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | v2_struct_0(X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t23_yellow19])])])])])])).

cnf(c_0_15,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | r3_waybel_9(X1,X2,X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(X3,k10_yellow_6(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X4,k2_pre_topc(X2,X3))
    | v2_struct_0(X2)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_0(X1,X2)
    | ~ r1_waybel_0(X2,X1,X3)
    | ~ r3_waybel_9(X2,X1,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( r3_waybel_9(esk3_0,X1,esk5_0)
    | v2_struct_0(X1)
    | ~ r2_hidden(esk5_0,k10_yellow_6(esk3_0,X1))
    | ~ l1_waybel_0(X1,esk3_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_18])]),c_0_19])).

cnf(c_0_22,negated_conjecture,
    ( l1_waybel_0(esk6_0,esk3_0)
    | r2_hidden(esk5_0,k2_pre_topc(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_23,negated_conjecture,
    ( v4_orders_2(esk6_0)
    | r2_hidden(esk5_0,k2_pre_topc(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_24,negated_conjecture,
    ( v7_waybel_0(esk6_0)
    | r2_hidden(esk5_0,k2_pre_topc(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk5_0,k10_yellow_6(esk3_0,esk6_0))
    | r2_hidden(esk5_0,k2_pre_topc(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk5_0,k2_pre_topc(esk3_0,esk4_0))
    | ~ v2_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_27,plain,
    ( l1_waybel_0(esk1_3(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk5_0,k2_pre_topc(esk3_0,X1))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk3_0,X2,esk5_0)
    | ~ r1_waybel_0(esk3_0,X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ l1_waybel_0(X2,esk3_0)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_16]),c_0_17]),c_0_18])]),c_0_19])).

cnf(c_0_29,negated_conjecture,
    ( r3_waybel_9(esk3_0,esk6_0,esk5_0)
    | r2_hidden(esk5_0,k2_pre_topc(esk3_0,esk4_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23]),c_0_24]),c_0_25]),c_0_26])).

cnf(c_0_30,plain,
    ( v7_waybel_0(esk1_3(X1,X2,X3))
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_31,plain,
    ( v4_orders_2(esk1_3(X1,X2,X3))
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_32,plain,
    ( v2_struct_0(X1)
    | ~ v2_struct_0(esk1_3(X1,X2,X3))
    | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_33,plain,
    ( r3_waybel_9(X1,esk1_3(X1,X2,X3),X3)
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_34,plain,(
    ! [X27,X28,X29] :
      ( ( m2_yellow_6(esk2_3(X27,X28,X29),X27,X28)
        | ~ r3_waybel_9(X27,X28,X29)
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | v2_struct_0(X28)
        | ~ v4_orders_2(X28)
        | ~ v7_waybel_0(X28)
        | ~ l1_waybel_0(X28,X27)
        | v2_struct_0(X27)
        | ~ v2_pre_topc(X27)
        | ~ l1_pre_topc(X27) )
      & ( r2_hidden(X29,k10_yellow_6(X27,esk2_3(X27,X28,X29)))
        | ~ r3_waybel_9(X27,X28,X29)
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | v2_struct_0(X28)
        | ~ v4_orders_2(X28)
        | ~ v7_waybel_0(X28)
        | ~ l1_waybel_0(X28,X27)
        | v2_struct_0(X27)
        | ~ v2_pre_topc(X27)
        | ~ l1_pre_topc(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t32_waybel_9])])])])])])).

cnf(c_0_35,negated_conjecture,
    ( l1_waybel_0(esk1_3(esk3_0,X1,esk5_0),esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r2_hidden(esk5_0,k2_pre_topc(esk3_0,X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_16]),c_0_17]),c_0_18])]),c_0_19])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk5_0,k2_pre_topc(esk3_0,esk4_0))
    | r2_hidden(esk5_0,k2_pre_topc(esk3_0,X1))
    | ~ r1_waybel_0(esk3_0,esk6_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_22]),c_0_23]),c_0_24]),c_0_29]),c_0_26])).

cnf(c_0_38,negated_conjecture,
    ( r1_waybel_0(esk3_0,esk6_0,esk4_0)
    | r2_hidden(esk5_0,k2_pre_topc(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_39,negated_conjecture,
    ( v7_waybel_0(esk1_3(esk3_0,X1,esk5_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r2_hidden(esk5_0,k2_pre_topc(esk3_0,X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_16]),c_0_17]),c_0_18])]),c_0_19])).

cnf(c_0_40,negated_conjecture,
    ( v4_orders_2(esk1_3(esk3_0,X1,esk5_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r2_hidden(esk5_0,k2_pre_topc(esk3_0,X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_16]),c_0_17]),c_0_18])]),c_0_19])).

cnf(c_0_41,negated_conjecture,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r2_hidden(esk5_0,k2_pre_topc(esk3_0,X1))
    | ~ v2_struct_0(esk1_3(esk3_0,X1,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_16]),c_0_17]),c_0_18])]),c_0_19])).

cnf(c_0_42,negated_conjecture,
    ( r3_waybel_9(esk3_0,esk1_3(esk3_0,X1,esk5_0),esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r2_hidden(esk5_0,k2_pre_topc(esk3_0,X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_16]),c_0_17]),c_0_18])]),c_0_19])).

cnf(c_0_43,plain,
    ( m2_yellow_6(esk2_3(X1,X2,X3),X1,X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r3_waybel_9(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_44,negated_conjecture,
    ( l1_waybel_0(esk1_3(esk3_0,esk4_0,esk5_0),esk3_0)
    | ~ r2_hidden(esk5_0,k2_pre_topc(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk5_0,k2_pre_topc(esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_36])])).

cnf(c_0_46,negated_conjecture,
    ( v7_waybel_0(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ r2_hidden(esk5_0,k2_pre_topc(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_36])).

cnf(c_0_47,negated_conjecture,
    ( v4_orders_2(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ r2_hidden(esk5_0,k2_pre_topc(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_36])).

cnf(c_0_48,negated_conjecture,
    ( ~ r2_hidden(esk5_0,k2_pre_topc(esk3_0,esk4_0))
    | ~ v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_36])).

cnf(c_0_49,negated_conjecture,
    ( r3_waybel_9(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk5_0)
    | ~ r2_hidden(esk5_0,k2_pre_topc(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_36])).

fof(c_0_50,plain,(
    ! [X8,X9,X10] :
      ( ( ~ v2_struct_0(X10)
        | ~ m2_yellow_6(X10,X8,X9)
        | v2_struct_0(X8)
        | ~ l1_struct_0(X8)
        | v2_struct_0(X9)
        | ~ v4_orders_2(X9)
        | ~ v7_waybel_0(X9)
        | ~ l1_waybel_0(X9,X8) )
      & ( v4_orders_2(X10)
        | ~ m2_yellow_6(X10,X8,X9)
        | v2_struct_0(X8)
        | ~ l1_struct_0(X8)
        | v2_struct_0(X9)
        | ~ v4_orders_2(X9)
        | ~ v7_waybel_0(X9)
        | ~ l1_waybel_0(X9,X8) )
      & ( v7_waybel_0(X10)
        | ~ m2_yellow_6(X10,X8,X9)
        | v2_struct_0(X8)
        | ~ l1_struct_0(X8)
        | v2_struct_0(X9)
        | ~ v4_orders_2(X9)
        | ~ v7_waybel_0(X9)
        | ~ l1_waybel_0(X9,X8) )
      & ( l1_waybel_0(X10,X8)
        | ~ m2_yellow_6(X10,X8,X9)
        | v2_struct_0(X8)
        | ~ l1_struct_0(X8)
        | v2_struct_0(X9)
        | ~ v4_orders_2(X9)
        | ~ v7_waybel_0(X9)
        | ~ l1_waybel_0(X9,X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m2_yellow_6])])])])])).

cnf(c_0_51,negated_conjecture,
    ( m2_yellow_6(esk2_3(esk3_0,X1,esk5_0),esk3_0,X1)
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk3_0,X1,esk5_0)
    | ~ l1_waybel_0(X1,esk3_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_16]),c_0_17]),c_0_18])]),c_0_19])).

cnf(c_0_52,negated_conjecture,
    ( l1_waybel_0(esk1_3(esk3_0,esk4_0,esk5_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_45])])).

cnf(c_0_53,negated_conjecture,
    ( v7_waybel_0(esk1_3(esk3_0,esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_45])])).

cnf(c_0_54,negated_conjecture,
    ( v4_orders_2(esk1_3(esk3_0,esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_45])])).

cnf(c_0_55,negated_conjecture,
    ( ~ v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_45])])).

cnf(c_0_56,negated_conjecture,
    ( r3_waybel_9(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_45])])).

fof(c_0_57,plain,(
    ! [X13,X14,X15,X16] :
      ( v2_struct_0(X13)
      | ~ l1_struct_0(X13)
      | v2_struct_0(X15)
      | ~ v4_orders_2(X15)
      | ~ v7_waybel_0(X15)
      | ~ l1_waybel_0(X15,X13)
      | ~ r1_waybel_0(X13,X15,X14)
      | ~ m2_yellow_6(X16,X13,X15)
      | r1_waybel_0(X13,X16,X14) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t21_yellow19])])])])).

cnf(c_0_58,plain,
    ( r1_waybel_0(X1,esk1_3(X1,X2,X3),X2)
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_59,plain,
    ( l1_waybel_0(X1,X2)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m2_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X2)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_60,negated_conjecture,
    ( m2_yellow_6(esk2_3(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk5_0),esk3_0,esk1_3(esk3_0,esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53]),c_0_54])]),c_0_55]),c_0_56])])).

fof(c_0_61,plain,(
    ! [X7] :
      ( ~ l1_pre_topc(X7)
      | l1_struct_0(X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_62,plain,
    ( v7_waybel_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m2_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X2)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_63,plain,
    ( v4_orders_2(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m2_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X2)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_64,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_struct_0(X1)
    | ~ m2_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X2)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_65,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | r1_waybel_0(X1,X4,X3)
    | ~ l1_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ r1_waybel_0(X1,X2,X3)
    | ~ m2_yellow_6(X4,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_66,negated_conjecture,
    ( r1_waybel_0(esk3_0,esk1_3(esk3_0,X1,esk5_0),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r2_hidden(esk5_0,k2_pre_topc(esk3_0,X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_16]),c_0_17]),c_0_18])]),c_0_19])).

cnf(c_0_67,plain,
    ( r2_hidden(X1,k10_yellow_6(X2,esk2_3(X2,X3,X1)))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ r3_waybel_9(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_68,plain,(
    ! [X5,X6] :
      ( ( ~ v3_yellow_6(X6,X5)
        | k10_yellow_6(X5,X6) != k1_xboole_0
        | v2_struct_0(X6)
        | ~ v4_orders_2(X6)
        | ~ v7_waybel_0(X6)
        | ~ l1_waybel_0(X6,X5)
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5) )
      & ( k10_yellow_6(X5,X6) = k1_xboole_0
        | v3_yellow_6(X6,X5)
        | v2_struct_0(X6)
        | ~ v4_orders_2(X6)
        | ~ v7_waybel_0(X6)
        | ~ l1_waybel_0(X6,X5)
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d19_yellow_6])])])])])).

cnf(c_0_69,negated_conjecture,
    ( l1_waybel_0(esk2_3(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk5_0),esk3_0)
    | ~ l1_struct_0(esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_52]),c_0_53]),c_0_54])]),c_0_55]),c_0_19])).

cnf(c_0_70,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_71,negated_conjecture,
    ( v7_waybel_0(esk2_3(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk5_0))
    | ~ l1_struct_0(esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_60]),c_0_52]),c_0_53]),c_0_54])]),c_0_55]),c_0_19])).

cnf(c_0_72,negated_conjecture,
    ( v4_orders_2(esk2_3(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk5_0))
    | ~ l1_struct_0(esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_60]),c_0_52]),c_0_53]),c_0_54])]),c_0_55]),c_0_19])).

cnf(c_0_73,negated_conjecture,
    ( ~ l1_struct_0(esk3_0)
    | ~ v2_struct_0(esk2_3(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_60]),c_0_52]),c_0_53]),c_0_54])]),c_0_55]),c_0_19])).

cnf(c_0_74,negated_conjecture,
    ( r1_waybel_0(esk3_0,esk2_3(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk5_0),X1)
    | ~ r1_waybel_0(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),X1)
    | ~ l1_struct_0(esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_60]),c_0_52]),c_0_53]),c_0_54])]),c_0_55]),c_0_19])).

cnf(c_0_75,negated_conjecture,
    ( r1_waybel_0(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk4_0)
    | ~ r2_hidden(esk5_0,k2_pre_topc(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_36])).

fof(c_0_76,plain,(
    ! [X31,X32] :
      ( ~ r2_hidden(X31,X32)
      | ~ v1_xboole_0(X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_77,negated_conjecture,
    ( r2_hidden(esk5_0,k10_yellow_6(esk3_0,esk2_3(esk3_0,X1,esk5_0)))
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk3_0,X1,esk5_0)
    | ~ l1_waybel_0(X1,esk3_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_16]),c_0_17]),c_0_18])]),c_0_19])).

cnf(c_0_78,negated_conjecture,
    ( v2_struct_0(X1)
    | ~ r2_hidden(esk5_0,k2_pre_topc(esk3_0,esk4_0))
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ v3_yellow_6(X1,esk3_0)
    | ~ l1_waybel_0(X1,esk3_0)
    | ~ r1_waybel_0(esk3_0,X1,esk4_0)
    | ~ r2_hidden(esk5_0,k10_yellow_6(esk3_0,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_79,plain,
    ( k10_yellow_6(X1,X2) = k1_xboole_0
    | v3_yellow_6(X2,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_80,negated_conjecture,
    ( l1_waybel_0(esk2_3(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk5_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_17])])).

cnf(c_0_81,negated_conjecture,
    ( v7_waybel_0(esk2_3(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_70]),c_0_17])])).

cnf(c_0_82,negated_conjecture,
    ( v4_orders_2(esk2_3(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_70]),c_0_17])])).

cnf(c_0_83,negated_conjecture,
    ( ~ v2_struct_0(esk2_3(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_70]),c_0_17])])).

cnf(c_0_84,negated_conjecture,
    ( r1_waybel_0(esk3_0,esk2_3(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk5_0),X1)
    | ~ r1_waybel_0(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_70]),c_0_17])])).

cnf(c_0_85,negated_conjecture,
    ( r1_waybel_0(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_45])])).

cnf(c_0_86,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_87,negated_conjecture,
    ( r2_hidden(esk5_0,k10_yellow_6(esk3_0,esk2_3(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_52]),c_0_53]),c_0_54])]),c_0_55]),c_0_56])])).

cnf(c_0_88,negated_conjecture,
    ( v2_struct_0(X1)
    | ~ r1_waybel_0(esk3_0,X1,esk4_0)
    | ~ r2_hidden(esk5_0,k10_yellow_6(esk3_0,X1))
    | ~ v3_yellow_6(X1,esk3_0)
    | ~ l1_waybel_0(X1,esk3_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_45])])).

cnf(c_0_89,negated_conjecture,
    ( k10_yellow_6(esk3_0,esk2_3(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk5_0)) = k1_xboole_0
    | v3_yellow_6(esk2_3(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk5_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_81]),c_0_82]),c_0_17]),c_0_18])]),c_0_83]),c_0_19])).

cnf(c_0_90,negated_conjecture,
    ( r1_waybel_0(esk3_0,esk2_3(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk5_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_91,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

cnf(c_0_92,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(split_conjunct,[status(thm)],[d2_xboole_0])).

cnf(c_0_93,negated_conjecture,
    ( ~ v1_xboole_0(k10_yellow_6(esk3_0,esk2_3(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk5_0))) ),
    inference(spm,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_94,negated_conjecture,
    ( k10_yellow_6(esk3_0,esk2_3(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk5_0)) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_90]),c_0_87]),c_0_80]),c_0_81]),c_0_82])]),c_0_83])).

cnf(c_0_95,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_91,c_0_92])).

cnf(c_0_96,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_93,c_0_94]),c_0_95])]),
    [proof]).

%------------------------------------------------------------------------------
