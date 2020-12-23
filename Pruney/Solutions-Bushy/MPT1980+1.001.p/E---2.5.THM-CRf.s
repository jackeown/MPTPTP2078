%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1980+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:06 EST 2020

% Result     : Theorem 1.33s
% Output     : CNFRefutation 1.33s
% Verified   : 
% Statistics : Number of formulae       :  167 (2757 expanded)
%              Number of clauses        :  132 ( 889 expanded)
%              Number of leaves         :   16 ( 697 expanded)
%              Depth                    :   27
%              Number of atoms          : 1509 (41265 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   27 (   9 average)
%              Maximal clause size      :  119 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t27_waybel_7,axiom,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & v2_waybel_1(X1)
        & v1_lattice3(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v1_waybel_0(X2,X1)
            & v12_waybel_0(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => ! [X3] :
              ( ( ~ v1_xboole_0(X3)
                & v2_waybel_0(X3,X1)
                & v13_waybel_0(X3,X1)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
             => ~ ( r1_subset_1(X2,X3)
                  & ! [X4] :
                      ( ( ~ v1_xboole_0(X4)
                        & v1_waybel_0(X4,X1)
                        & v12_waybel_0(X4,X1)
                        & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                     => ~ ( v1_waybel_7(X4,X1)
                          & r1_tarski(X2,X4)
                          & r1_subset_1(X4,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_waybel_7)).

fof(t26_yellow_7,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( ( v1_waybel_0(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
        <=> ( v2_waybel_0(X2,k7_lattice3(X1))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k7_lattice3(X1)))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_yellow_7)).

fof(dt_k7_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v1_orders_2(k7_lattice3(X1))
        & l1_orders_2(k7_lattice3(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_lattice3)).

fof(t27_yellow_7,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( ( v1_waybel_0(X2,k7_lattice3(X1))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k7_lattice3(X1)))) )
        <=> ( v2_waybel_0(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_yellow_7)).

fof(t29_waybel_7,conjecture,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & v2_waybel_1(X1)
        & v1_lattice3(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v1_waybel_0(X2,X1)
            & v12_waybel_0(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => ! [X3] :
              ( ( ~ v1_xboole_0(X3)
                & v2_waybel_0(X3,X1)
                & v13_waybel_0(X3,X1)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
             => ~ ( r1_subset_1(X2,X3)
                  & ! [X4] :
                      ( ( ~ v1_xboole_0(X4)
                        & v2_waybel_0(X4,X1)
                        & v13_waybel_0(X4,X1)
                        & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                     => ~ ( v2_waybel_7(X4,X1)
                          & r1_tarski(X3,X4)
                          & r1_subset_1(X2,X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_waybel_7)).

fof(fc8_yellow_7,axiom,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & v1_lattice3(X1)
        & v2_lattice3(X1)
        & v2_waybel_1(X1)
        & l1_orders_2(X1) )
     => ( v1_orders_2(k7_lattice3(X1))
        & v2_waybel_1(k7_lattice3(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_yellow_7)).

fof(fc5_yellow_7,axiom,(
    ! [X1] :
      ( ( v2_lattice3(X1)
        & l1_orders_2(X1) )
     => ( v1_orders_2(k7_lattice3(X1))
        & v1_lattice3(k7_lattice3(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow_7)).

fof(fc6_yellow_7,axiom,(
    ! [X1] :
      ( ( v1_lattice3(X1)
        & l1_orders_2(X1) )
     => ( v1_orders_2(k7_lattice3(X1))
        & v2_lattice3(k7_lattice3(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_yellow_7)).

fof(fc3_yellow_7,axiom,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ( v1_orders_2(k7_lattice3(X1))
        & v5_orders_2(k7_lattice3(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_yellow_7)).

fof(fc2_yellow_7,axiom,(
    ! [X1] :
      ( ( v4_orders_2(X1)
        & l1_orders_2(X1) )
     => ( v1_orders_2(k7_lattice3(X1))
        & v4_orders_2(k7_lattice3(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_yellow_7)).

fof(fc1_yellow_7,axiom,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & l1_orders_2(X1) )
     => ( v1_orders_2(k7_lattice3(X1))
        & v3_orders_2(k7_lattice3(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_yellow_7)).

fof(t28_yellow_7,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( ( v12_waybel_0(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
        <=> ( v13_waybel_0(X2,k7_lattice3(X1))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k7_lattice3(X1)))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_yellow_7)).

fof(symmetry_r1_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X2) )
     => ( r1_subset_1(X1,X2)
       => r1_subset_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_subset_1)).

fof(t21_waybel_7,axiom,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & v1_lattice3(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v2_waybel_0(X2,X1)
            & v13_waybel_0(X2,X1)
            & v2_waybel_7(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
        <=> ( ~ v1_xboole_0(X2)
            & v1_waybel_0(X2,k7_lattice3(X1))
            & v12_waybel_0(X2,k7_lattice3(X1))
            & v1_waybel_7(X2,k7_lattice3(X1))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k7_lattice3(X1)))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_waybel_7)).

fof(t29_yellow_7,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( ( v12_waybel_0(X2,k7_lattice3(X1))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k7_lattice3(X1)))) )
        <=> ( v13_waybel_0(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_yellow_7)).

fof(c_0_15,plain,(
    ! [X17,X18,X19] :
      ( ( ~ v1_xboole_0(esk1_3(X17,X18,X19))
        | ~ r1_subset_1(X18,X19)
        | v1_xboole_0(X19)
        | ~ v2_waybel_0(X19,X17)
        | ~ v13_waybel_0(X19,X17)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X17)))
        | v1_xboole_0(X18)
        | ~ v1_waybel_0(X18,X17)
        | ~ v12_waybel_0(X18,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ v3_orders_2(X17)
        | ~ v4_orders_2(X17)
        | ~ v5_orders_2(X17)
        | ~ v2_waybel_1(X17)
        | ~ v1_lattice3(X17)
        | ~ v2_lattice3(X17)
        | ~ l1_orders_2(X17) )
      & ( v1_waybel_0(esk1_3(X17,X18,X19),X17)
        | ~ r1_subset_1(X18,X19)
        | v1_xboole_0(X19)
        | ~ v2_waybel_0(X19,X17)
        | ~ v13_waybel_0(X19,X17)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X17)))
        | v1_xboole_0(X18)
        | ~ v1_waybel_0(X18,X17)
        | ~ v12_waybel_0(X18,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ v3_orders_2(X17)
        | ~ v4_orders_2(X17)
        | ~ v5_orders_2(X17)
        | ~ v2_waybel_1(X17)
        | ~ v1_lattice3(X17)
        | ~ v2_lattice3(X17)
        | ~ l1_orders_2(X17) )
      & ( v12_waybel_0(esk1_3(X17,X18,X19),X17)
        | ~ r1_subset_1(X18,X19)
        | v1_xboole_0(X19)
        | ~ v2_waybel_0(X19,X17)
        | ~ v13_waybel_0(X19,X17)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X17)))
        | v1_xboole_0(X18)
        | ~ v1_waybel_0(X18,X17)
        | ~ v12_waybel_0(X18,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ v3_orders_2(X17)
        | ~ v4_orders_2(X17)
        | ~ v5_orders_2(X17)
        | ~ v2_waybel_1(X17)
        | ~ v1_lattice3(X17)
        | ~ v2_lattice3(X17)
        | ~ l1_orders_2(X17) )
      & ( m1_subset_1(esk1_3(X17,X18,X19),k1_zfmisc_1(u1_struct_0(X17)))
        | ~ r1_subset_1(X18,X19)
        | v1_xboole_0(X19)
        | ~ v2_waybel_0(X19,X17)
        | ~ v13_waybel_0(X19,X17)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X17)))
        | v1_xboole_0(X18)
        | ~ v1_waybel_0(X18,X17)
        | ~ v12_waybel_0(X18,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ v3_orders_2(X17)
        | ~ v4_orders_2(X17)
        | ~ v5_orders_2(X17)
        | ~ v2_waybel_1(X17)
        | ~ v1_lattice3(X17)
        | ~ v2_lattice3(X17)
        | ~ l1_orders_2(X17) )
      & ( v1_waybel_7(esk1_3(X17,X18,X19),X17)
        | ~ r1_subset_1(X18,X19)
        | v1_xboole_0(X19)
        | ~ v2_waybel_0(X19,X17)
        | ~ v13_waybel_0(X19,X17)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X17)))
        | v1_xboole_0(X18)
        | ~ v1_waybel_0(X18,X17)
        | ~ v12_waybel_0(X18,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ v3_orders_2(X17)
        | ~ v4_orders_2(X17)
        | ~ v5_orders_2(X17)
        | ~ v2_waybel_1(X17)
        | ~ v1_lattice3(X17)
        | ~ v2_lattice3(X17)
        | ~ l1_orders_2(X17) )
      & ( r1_tarski(X18,esk1_3(X17,X18,X19))
        | ~ r1_subset_1(X18,X19)
        | v1_xboole_0(X19)
        | ~ v2_waybel_0(X19,X17)
        | ~ v13_waybel_0(X19,X17)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X17)))
        | v1_xboole_0(X18)
        | ~ v1_waybel_0(X18,X17)
        | ~ v12_waybel_0(X18,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ v3_orders_2(X17)
        | ~ v4_orders_2(X17)
        | ~ v5_orders_2(X17)
        | ~ v2_waybel_1(X17)
        | ~ v1_lattice3(X17)
        | ~ v2_lattice3(X17)
        | ~ l1_orders_2(X17) )
      & ( r1_subset_1(esk1_3(X17,X18,X19),X19)
        | ~ r1_subset_1(X18,X19)
        | v1_xboole_0(X19)
        | ~ v2_waybel_0(X19,X17)
        | ~ v13_waybel_0(X19,X17)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X17)))
        | v1_xboole_0(X18)
        | ~ v1_waybel_0(X18,X17)
        | ~ v12_waybel_0(X18,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ v3_orders_2(X17)
        | ~ v4_orders_2(X17)
        | ~ v5_orders_2(X17)
        | ~ v2_waybel_1(X17)
        | ~ v1_lattice3(X17)
        | ~ v2_lattice3(X17)
        | ~ l1_orders_2(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t27_waybel_7])])])])])])).

fof(c_0_16,plain,(
    ! [X15,X16] :
      ( ( v2_waybel_0(X16,k7_lattice3(X15))
        | ~ v1_waybel_0(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ l1_orders_2(X15) )
      & ( m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(k7_lattice3(X15))))
        | ~ v1_waybel_0(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ l1_orders_2(X15) )
      & ( v1_waybel_0(X16,X15)
        | ~ v2_waybel_0(X16,k7_lattice3(X15))
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(k7_lattice3(X15))))
        | ~ l1_orders_2(X15) )
      & ( m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ v2_waybel_0(X16,k7_lattice3(X15))
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(k7_lattice3(X15))))
        | ~ l1_orders_2(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_yellow_7])])])])).

fof(c_0_17,plain,(
    ! [X5] :
      ( ( v1_orders_2(k7_lattice3(X5))
        | ~ l1_orders_2(X5) )
      & ( l1_orders_2(k7_lattice3(X5))
        | ~ l1_orders_2(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_lattice3])])])).

cnf(c_0_18,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | ~ r1_subset_1(X2,X3)
    | ~ v2_waybel_0(X3,X1)
    | ~ v13_waybel_0(X3,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_waybel_0(X2,X1)
    | ~ v12_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_waybel_1(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X2))))
    | ~ v1_waybel_0(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,plain,
    ( l1_orders_2(k7_lattice3(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,plain,
    ( v2_waybel_0(X1,k7_lattice3(X2))
    | ~ v1_waybel_0(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_22,plain,(
    ! [X21,X22] :
      ( ( v2_waybel_0(X22,X21)
        | ~ v1_waybel_0(X22,k7_lattice3(X21))
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(k7_lattice3(X21))))
        | ~ l1_orders_2(X21) )
      & ( m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ v1_waybel_0(X22,k7_lattice3(X21))
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(k7_lattice3(X21))))
        | ~ l1_orders_2(X21) )
      & ( v1_waybel_0(X22,k7_lattice3(X21))
        | ~ v2_waybel_0(X22,X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ l1_orders_2(X21) )
      & ( m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(k7_lattice3(X21))))
        | ~ v2_waybel_0(X22,X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ l1_orders_2(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t27_yellow_7])])])])).

fof(c_0_23,negated_conjecture,(
    ~ ! [X1] :
        ( ( v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & v2_waybel_1(X1)
          & v1_lattice3(X1)
          & v2_lattice3(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( ( ~ v1_xboole_0(X2)
              & v1_waybel_0(X2,X1)
              & v12_waybel_0(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
           => ! [X3] :
                ( ( ~ v1_xboole_0(X3)
                  & v2_waybel_0(X3,X1)
                  & v13_waybel_0(X3,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
               => ~ ( r1_subset_1(X2,X3)
                    & ! [X4] :
                        ( ( ~ v1_xboole_0(X4)
                          & v2_waybel_0(X4,X1)
                          & v13_waybel_0(X4,X1)
                          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                       => ~ ( v2_waybel_7(X4,X1)
                            & r1_tarski(X3,X4)
                            & r1_subset_1(X2,X4) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t29_waybel_7])).

cnf(c_0_24,plain,
    ( v1_waybel_0(esk1_3(X1,X2,X3),X1)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | ~ r1_subset_1(X2,X3)
    | ~ v2_waybel_0(X3,X1)
    | ~ v13_waybel_0(X3,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_waybel_0(X2,X1)
    | ~ v12_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_waybel_1(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,plain,
    ( m1_subset_1(esk1_3(k7_lattice3(X1),X2,X3),k1_zfmisc_1(u1_struct_0(k7_lattice3(X1))))
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ v12_waybel_0(X2,k7_lattice3(X1))
    | ~ v1_waybel_0(X2,k7_lattice3(X1))
    | ~ v1_waybel_0(X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k7_lattice3(X1))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v13_waybel_0(X3,k7_lattice3(X1))
    | ~ r1_subset_1(X2,X3)
    | ~ v2_waybel_1(k7_lattice3(X1))
    | ~ v1_lattice3(k7_lattice3(X1))
    | ~ v2_lattice3(k7_lattice3(X1))
    | ~ v5_orders_2(k7_lattice3(X1))
    | ~ v4_orders_2(k7_lattice3(X1))
    | ~ v3_orders_2(k7_lattice3(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20]),c_0_21])).

cnf(c_0_26,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X2))))
    | ~ v2_waybel_0(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,plain,
    ( v1_waybel_0(X1,k7_lattice3(X2))
    | ~ v2_waybel_0(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_28,negated_conjecture,(
    ! [X30] :
      ( v3_orders_2(esk2_0)
      & v4_orders_2(esk2_0)
      & v5_orders_2(esk2_0)
      & v2_waybel_1(esk2_0)
      & v1_lattice3(esk2_0)
      & v2_lattice3(esk2_0)
      & l1_orders_2(esk2_0)
      & ~ v1_xboole_0(esk3_0)
      & v1_waybel_0(esk3_0,esk2_0)
      & v12_waybel_0(esk3_0,esk2_0)
      & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
      & ~ v1_xboole_0(esk4_0)
      & v2_waybel_0(esk4_0,esk2_0)
      & v13_waybel_0(esk4_0,esk2_0)
      & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
      & r1_subset_1(esk3_0,esk4_0)
      & ( v1_xboole_0(X30)
        | ~ v2_waybel_0(X30,esk2_0)
        | ~ v13_waybel_0(X30,esk2_0)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(esk2_0)))
        | ~ v2_waybel_7(X30,esk2_0)
        | ~ r1_tarski(esk4_0,X30)
        | ~ r1_subset_1(esk3_0,X30) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_23])])])])])).

cnf(c_0_29,plain,
    ( v1_waybel_0(esk1_3(k7_lattice3(X1),X2,X3),k7_lattice3(X1))
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ v12_waybel_0(X2,k7_lattice3(X1))
    | ~ v1_waybel_0(X2,k7_lattice3(X1))
    | ~ v1_waybel_0(X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k7_lattice3(X1))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v13_waybel_0(X3,k7_lattice3(X1))
    | ~ r1_subset_1(X2,X3)
    | ~ v2_waybel_1(k7_lattice3(X1))
    | ~ v1_lattice3(k7_lattice3(X1))
    | ~ v2_lattice3(k7_lattice3(X1))
    | ~ v5_orders_2(k7_lattice3(X1))
    | ~ v4_orders_2(k7_lattice3(X1))
    | ~ v3_orders_2(k7_lattice3(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_19]),c_0_20]),c_0_21])).

cnf(c_0_30,plain,
    ( v12_waybel_0(esk1_3(X1,X2,X3),X1)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | ~ r1_subset_1(X2,X3)
    | ~ v2_waybel_0(X3,X1)
    | ~ v13_waybel_0(X3,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_waybel_0(X2,X1)
    | ~ v12_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_waybel_1(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_31,plain,
    ( v1_waybel_7(esk1_3(X1,X2,X3),X1)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | ~ r1_subset_1(X2,X3)
    | ~ v2_waybel_0(X3,X1)
    | ~ v13_waybel_0(X3,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_waybel_0(X2,X1)
    | ~ v12_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_waybel_1(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_32,plain,
    ( m1_subset_1(esk1_3(k7_lattice3(X1),X2,X3),k1_zfmisc_1(u1_struct_0(k7_lattice3(X1))))
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | ~ v12_waybel_0(X2,k7_lattice3(X1))
    | ~ v1_waybel_0(X3,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v13_waybel_0(X3,k7_lattice3(X1))
    | ~ v2_waybel_0(X2,X1)
    | ~ r1_subset_1(X2,X3)
    | ~ v2_waybel_1(k7_lattice3(X1))
    | ~ v1_lattice3(k7_lattice3(X1))
    | ~ v2_lattice3(k7_lattice3(X1))
    | ~ v5_orders_2(k7_lattice3(X1))
    | ~ v4_orders_2(k7_lattice3(X1))
    | ~ v3_orders_2(k7_lattice3(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( v1_waybel_0(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_37,plain,(
    ! [X11] :
      ( ( v1_orders_2(k7_lattice3(X11))
        | ~ v3_orders_2(X11)
        | ~ v4_orders_2(X11)
        | ~ v5_orders_2(X11)
        | ~ v1_lattice3(X11)
        | ~ v2_lattice3(X11)
        | ~ v2_waybel_1(X11)
        | ~ l1_orders_2(X11) )
      & ( v2_waybel_1(k7_lattice3(X11))
        | ~ v3_orders_2(X11)
        | ~ v4_orders_2(X11)
        | ~ v5_orders_2(X11)
        | ~ v1_lattice3(X11)
        | ~ v2_lattice3(X11)
        | ~ v2_waybel_1(X11)
        | ~ l1_orders_2(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc8_yellow_7])])])).

cnf(c_0_38,plain,
    ( v1_waybel_0(esk1_3(k7_lattice3(X1),X2,X3),k7_lattice3(X1))
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | ~ v12_waybel_0(X2,k7_lattice3(X1))
    | ~ v1_waybel_0(X3,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v13_waybel_0(X3,k7_lattice3(X1))
    | ~ v2_waybel_0(X2,X1)
    | ~ r1_subset_1(X2,X3)
    | ~ v2_waybel_1(k7_lattice3(X1))
    | ~ v1_lattice3(k7_lattice3(X1))
    | ~ v2_lattice3(k7_lattice3(X1))
    | ~ v5_orders_2(k7_lattice3(X1))
    | ~ v4_orders_2(k7_lattice3(X1))
    | ~ v3_orders_2(k7_lattice3(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_26]),c_0_27])).

cnf(c_0_39,plain,
    ( v12_waybel_0(esk1_3(k7_lattice3(X1),X2,X3),k7_lattice3(X1))
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ v12_waybel_0(X2,k7_lattice3(X1))
    | ~ v1_waybel_0(X2,k7_lattice3(X1))
    | ~ v1_waybel_0(X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k7_lattice3(X1))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v13_waybel_0(X3,k7_lattice3(X1))
    | ~ r1_subset_1(X2,X3)
    | ~ v2_waybel_1(k7_lattice3(X1))
    | ~ v1_lattice3(k7_lattice3(X1))
    | ~ v2_lattice3(k7_lattice3(X1))
    | ~ v5_orders_2(k7_lattice3(X1))
    | ~ v4_orders_2(k7_lattice3(X1))
    | ~ v3_orders_2(k7_lattice3(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_19]),c_0_20]),c_0_21])).

cnf(c_0_40,plain,
    ( v1_waybel_7(esk1_3(k7_lattice3(X1),X2,X3),k7_lattice3(X1))
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ v12_waybel_0(X2,k7_lattice3(X1))
    | ~ v1_waybel_0(X2,k7_lattice3(X1))
    | ~ v1_waybel_0(X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k7_lattice3(X1))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v13_waybel_0(X3,k7_lattice3(X1))
    | ~ r1_subset_1(X2,X3)
    | ~ v2_waybel_1(k7_lattice3(X1))
    | ~ v1_lattice3(k7_lattice3(X1))
    | ~ v2_lattice3(k7_lattice3(X1))
    | ~ v5_orders_2(k7_lattice3(X1))
    | ~ v4_orders_2(k7_lattice3(X1))
    | ~ v3_orders_2(k7_lattice3(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_19]),c_0_20]),c_0_21])).

cnf(c_0_41,plain,
    ( r1_subset_1(esk1_3(X1,X2,X3),X3)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | ~ r1_subset_1(X2,X3)
    | ~ v2_waybel_0(X3,X1)
    | ~ v13_waybel_0(X3,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_waybel_0(X2,X1)
    | ~ v12_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_waybel_1(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,esk1_3(X2,X1,X3))
    | v1_xboole_0(X3)
    | v1_xboole_0(X1)
    | ~ r1_subset_1(X1,X3)
    | ~ v2_waybel_0(X3,X2)
    | ~ v13_waybel_0(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v1_waybel_0(X1,X2)
    | ~ v12_waybel_0(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ v2_waybel_1(X2)
    | ~ v1_lattice3(X2)
    | ~ v2_lattice3(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(esk1_3(k7_lattice3(esk2_0),X1,esk3_0),k1_zfmisc_1(u1_struct_0(k7_lattice3(esk2_0))))
    | v1_xboole_0(X1)
    | ~ v12_waybel_0(X1,k7_lattice3(esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ v13_waybel_0(esk3_0,k7_lattice3(esk2_0))
    | ~ v2_waybel_0(X1,esk2_0)
    | ~ r1_subset_1(X1,esk3_0)
    | ~ v2_waybel_1(k7_lattice3(esk2_0))
    | ~ v1_lattice3(k7_lattice3(esk2_0))
    | ~ v2_lattice3(k7_lattice3(esk2_0))
    | ~ v5_orders_2(k7_lattice3(esk2_0))
    | ~ v4_orders_2(k7_lattice3(esk2_0))
    | ~ v3_orders_2(k7_lattice3(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_44,plain,
    ( v2_waybel_1(k7_lattice3(X1))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ v2_waybel_1(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_45,negated_conjecture,
    ( v2_waybel_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_46,negated_conjecture,
    ( v1_lattice3(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_47,negated_conjecture,
    ( v2_lattice3(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_48,negated_conjecture,
    ( v5_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_49,negated_conjecture,
    ( v4_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_50,negated_conjecture,
    ( v3_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_51,plain,(
    ! [X9] :
      ( ( v1_orders_2(k7_lattice3(X9))
        | ~ v2_lattice3(X9)
        | ~ l1_orders_2(X9) )
      & ( v1_lattice3(k7_lattice3(X9))
        | ~ v2_lattice3(X9)
        | ~ l1_orders_2(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc5_yellow_7])])])).

cnf(c_0_52,negated_conjecture,
    ( v1_waybel_0(esk1_3(k7_lattice3(esk2_0),X1,esk3_0),k7_lattice3(esk2_0))
    | v1_xboole_0(X1)
    | ~ v12_waybel_0(X1,k7_lattice3(esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ v13_waybel_0(esk3_0,k7_lattice3(esk2_0))
    | ~ v2_waybel_0(X1,esk2_0)
    | ~ r1_subset_1(X1,esk3_0)
    | ~ v2_waybel_1(k7_lattice3(esk2_0))
    | ~ v1_lattice3(k7_lattice3(esk2_0))
    | ~ v2_lattice3(k7_lattice3(esk2_0))
    | ~ v5_orders_2(k7_lattice3(esk2_0))
    | ~ v4_orders_2(k7_lattice3(esk2_0))
    | ~ v3_orders_2(k7_lattice3(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_33]),c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_53,plain,
    ( v12_waybel_0(esk1_3(k7_lattice3(X1),X2,X3),k7_lattice3(X1))
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | ~ v12_waybel_0(X2,k7_lattice3(X1))
    | ~ v1_waybel_0(X3,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v13_waybel_0(X3,k7_lattice3(X1))
    | ~ v2_waybel_0(X2,X1)
    | ~ r1_subset_1(X2,X3)
    | ~ v2_waybel_1(k7_lattice3(X1))
    | ~ v1_lattice3(k7_lattice3(X1))
    | ~ v2_lattice3(k7_lattice3(X1))
    | ~ v5_orders_2(k7_lattice3(X1))
    | ~ v4_orders_2(k7_lattice3(X1))
    | ~ v3_orders_2(k7_lattice3(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_26]),c_0_27])).

cnf(c_0_54,plain,
    ( v1_waybel_7(esk1_3(k7_lattice3(X1),X2,X3),k7_lattice3(X1))
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | ~ v12_waybel_0(X2,k7_lattice3(X1))
    | ~ v1_waybel_0(X3,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v13_waybel_0(X3,k7_lattice3(X1))
    | ~ v2_waybel_0(X2,X1)
    | ~ r1_subset_1(X2,X3)
    | ~ v2_waybel_1(k7_lattice3(X1))
    | ~ v1_lattice3(k7_lattice3(X1))
    | ~ v2_lattice3(k7_lattice3(X1))
    | ~ v5_orders_2(k7_lattice3(X1))
    | ~ v4_orders_2(k7_lattice3(X1))
    | ~ v3_orders_2(k7_lattice3(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_26]),c_0_27])).

cnf(c_0_55,plain,
    ( r1_subset_1(esk1_3(k7_lattice3(X1),X2,X3),X3)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ v12_waybel_0(X2,k7_lattice3(X1))
    | ~ v1_waybel_0(X2,k7_lattice3(X1))
    | ~ v1_waybel_0(X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k7_lattice3(X1))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v13_waybel_0(X3,k7_lattice3(X1))
    | ~ r1_subset_1(X2,X3)
    | ~ v2_waybel_1(k7_lattice3(X1))
    | ~ v1_lattice3(k7_lattice3(X1))
    | ~ v2_lattice3(k7_lattice3(X1))
    | ~ v5_orders_2(k7_lattice3(X1))
    | ~ v4_orders_2(k7_lattice3(X1))
    | ~ v3_orders_2(k7_lattice3(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_19]),c_0_20]),c_0_21])).

cnf(c_0_56,plain,
    ( r1_tarski(X1,esk1_3(k7_lattice3(X2),X1,X3))
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | ~ v12_waybel_0(X1,k7_lattice3(X2))
    | ~ v1_waybel_0(X1,k7_lattice3(X2))
    | ~ v1_waybel_0(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v13_waybel_0(X3,k7_lattice3(X2))
    | ~ r1_subset_1(X1,X3)
    | ~ v2_waybel_1(k7_lattice3(X2))
    | ~ v1_lattice3(k7_lattice3(X2))
    | ~ v2_lattice3(k7_lattice3(X2))
    | ~ v5_orders_2(k7_lattice3(X2))
    | ~ v4_orders_2(k7_lattice3(X2))
    | ~ v3_orders_2(k7_lattice3(X2))
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_19]),c_0_20]),c_0_21])).

cnf(c_0_57,negated_conjecture,
    ( m1_subset_1(esk1_3(k7_lattice3(esk2_0),X1,esk3_0),k1_zfmisc_1(u1_struct_0(k7_lattice3(esk2_0))))
    | v1_xboole_0(X1)
    | ~ v12_waybel_0(X1,k7_lattice3(esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ v13_waybel_0(esk3_0,k7_lattice3(esk2_0))
    | ~ v2_waybel_0(X1,esk2_0)
    | ~ r1_subset_1(X1,esk3_0)
    | ~ v1_lattice3(k7_lattice3(esk2_0))
    | ~ v2_lattice3(k7_lattice3(esk2_0))
    | ~ v5_orders_2(k7_lattice3(esk2_0))
    | ~ v4_orders_2(k7_lattice3(esk2_0))
    | ~ v3_orders_2(k7_lattice3(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45]),c_0_46]),c_0_47]),c_0_48]),c_0_49]),c_0_50]),c_0_35])])).

cnf(c_0_58,plain,
    ( v1_lattice3(k7_lattice3(X1))
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

fof(c_0_59,plain,(
    ! [X10] :
      ( ( v1_orders_2(k7_lattice3(X10))
        | ~ v1_lattice3(X10)
        | ~ l1_orders_2(X10) )
      & ( v2_lattice3(k7_lattice3(X10))
        | ~ v1_lattice3(X10)
        | ~ l1_orders_2(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc6_yellow_7])])])).

cnf(c_0_60,negated_conjecture,
    ( v1_waybel_0(esk1_3(k7_lattice3(esk2_0),X1,esk3_0),k7_lattice3(esk2_0))
    | v1_xboole_0(X1)
    | ~ v12_waybel_0(X1,k7_lattice3(esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ v13_waybel_0(esk3_0,k7_lattice3(esk2_0))
    | ~ v2_waybel_0(X1,esk2_0)
    | ~ r1_subset_1(X1,esk3_0)
    | ~ v1_lattice3(k7_lattice3(esk2_0))
    | ~ v2_lattice3(k7_lattice3(esk2_0))
    | ~ v5_orders_2(k7_lattice3(esk2_0))
    | ~ v4_orders_2(k7_lattice3(esk2_0))
    | ~ v3_orders_2(k7_lattice3(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_44]),c_0_45]),c_0_46]),c_0_47]),c_0_48]),c_0_49]),c_0_50]),c_0_35])])).

cnf(c_0_61,negated_conjecture,
    ( v12_waybel_0(esk1_3(k7_lattice3(esk2_0),X1,esk3_0),k7_lattice3(esk2_0))
    | v1_xboole_0(X1)
    | ~ v12_waybel_0(X1,k7_lattice3(esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ v13_waybel_0(esk3_0,k7_lattice3(esk2_0))
    | ~ v2_waybel_0(X1,esk2_0)
    | ~ r1_subset_1(X1,esk3_0)
    | ~ v2_waybel_1(k7_lattice3(esk2_0))
    | ~ v1_lattice3(k7_lattice3(esk2_0))
    | ~ v2_lattice3(k7_lattice3(esk2_0))
    | ~ v5_orders_2(k7_lattice3(esk2_0))
    | ~ v4_orders_2(k7_lattice3(esk2_0))
    | ~ v3_orders_2(k7_lattice3(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_33]),c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_62,negated_conjecture,
    ( v1_waybel_7(esk1_3(k7_lattice3(esk2_0),X1,esk3_0),k7_lattice3(esk2_0))
    | v1_xboole_0(X1)
    | ~ v12_waybel_0(X1,k7_lattice3(esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ v13_waybel_0(esk3_0,k7_lattice3(esk2_0))
    | ~ v2_waybel_0(X1,esk2_0)
    | ~ r1_subset_1(X1,esk3_0)
    | ~ v2_waybel_1(k7_lattice3(esk2_0))
    | ~ v1_lattice3(k7_lattice3(esk2_0))
    | ~ v2_lattice3(k7_lattice3(esk2_0))
    | ~ v5_orders_2(k7_lattice3(esk2_0))
    | ~ v4_orders_2(k7_lattice3(esk2_0))
    | ~ v3_orders_2(k7_lattice3(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_33]),c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_63,plain,
    ( r1_subset_1(esk1_3(k7_lattice3(X1),X2,X3),X3)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | ~ v12_waybel_0(X2,k7_lattice3(X1))
    | ~ v1_waybel_0(X3,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v13_waybel_0(X3,k7_lattice3(X1))
    | ~ v2_waybel_0(X2,X1)
    | ~ r1_subset_1(X2,X3)
    | ~ v2_waybel_1(k7_lattice3(X1))
    | ~ v1_lattice3(k7_lattice3(X1))
    | ~ v2_lattice3(k7_lattice3(X1))
    | ~ v5_orders_2(k7_lattice3(X1))
    | ~ v4_orders_2(k7_lattice3(X1))
    | ~ v3_orders_2(k7_lattice3(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_26]),c_0_27])).

cnf(c_0_64,plain,
    ( r1_tarski(X1,esk1_3(k7_lattice3(X2),X1,X3))
    | v1_xboole_0(X3)
    | v1_xboole_0(X1)
    | ~ v12_waybel_0(X1,k7_lattice3(X2))
    | ~ v1_waybel_0(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v13_waybel_0(X3,k7_lattice3(X2))
    | ~ v2_waybel_0(X1,X2)
    | ~ r1_subset_1(X1,X3)
    | ~ v2_waybel_1(k7_lattice3(X2))
    | ~ v1_lattice3(k7_lattice3(X2))
    | ~ v2_lattice3(k7_lattice3(X2))
    | ~ v5_orders_2(k7_lattice3(X2))
    | ~ v4_orders_2(k7_lattice3(X2))
    | ~ v3_orders_2(k7_lattice3(X2))
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_26]),c_0_27])).

cnf(c_0_65,negated_conjecture,
    ( m1_subset_1(esk1_3(k7_lattice3(esk2_0),X1,esk3_0),k1_zfmisc_1(u1_struct_0(k7_lattice3(esk2_0))))
    | v1_xboole_0(X1)
    | ~ v12_waybel_0(X1,k7_lattice3(esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ v13_waybel_0(esk3_0,k7_lattice3(esk2_0))
    | ~ v2_waybel_0(X1,esk2_0)
    | ~ r1_subset_1(X1,esk3_0)
    | ~ v2_lattice3(k7_lattice3(esk2_0))
    | ~ v5_orders_2(k7_lattice3(esk2_0))
    | ~ v4_orders_2(k7_lattice3(esk2_0))
    | ~ v3_orders_2(k7_lattice3(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_47]),c_0_35])])).

cnf(c_0_66,plain,
    ( v2_lattice3(k7_lattice3(X1))
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

fof(c_0_67,plain,(
    ! [X8] :
      ( ( v1_orders_2(k7_lattice3(X8))
        | ~ v5_orders_2(X8)
        | ~ l1_orders_2(X8) )
      & ( v5_orders_2(k7_lattice3(X8))
        | ~ v5_orders_2(X8)
        | ~ l1_orders_2(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc3_yellow_7])])])).

cnf(c_0_68,negated_conjecture,
    ( v1_waybel_0(esk1_3(k7_lattice3(esk2_0),X1,esk3_0),k7_lattice3(esk2_0))
    | v1_xboole_0(X1)
    | ~ v12_waybel_0(X1,k7_lattice3(esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ v13_waybel_0(esk3_0,k7_lattice3(esk2_0))
    | ~ v2_waybel_0(X1,esk2_0)
    | ~ r1_subset_1(X1,esk3_0)
    | ~ v2_lattice3(k7_lattice3(esk2_0))
    | ~ v5_orders_2(k7_lattice3(esk2_0))
    | ~ v4_orders_2(k7_lattice3(esk2_0))
    | ~ v3_orders_2(k7_lattice3(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_58]),c_0_47]),c_0_35])])).

cnf(c_0_69,negated_conjecture,
    ( v12_waybel_0(esk1_3(k7_lattice3(esk2_0),X1,esk3_0),k7_lattice3(esk2_0))
    | v1_xboole_0(X1)
    | ~ v12_waybel_0(X1,k7_lattice3(esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ v13_waybel_0(esk3_0,k7_lattice3(esk2_0))
    | ~ v2_waybel_0(X1,esk2_0)
    | ~ r1_subset_1(X1,esk3_0)
    | ~ v1_lattice3(k7_lattice3(esk2_0))
    | ~ v2_lattice3(k7_lattice3(esk2_0))
    | ~ v5_orders_2(k7_lattice3(esk2_0))
    | ~ v4_orders_2(k7_lattice3(esk2_0))
    | ~ v3_orders_2(k7_lattice3(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_44]),c_0_45]),c_0_46]),c_0_47]),c_0_48]),c_0_49]),c_0_50]),c_0_35])])).

cnf(c_0_70,negated_conjecture,
    ( v1_waybel_7(esk1_3(k7_lattice3(esk2_0),X1,esk3_0),k7_lattice3(esk2_0))
    | v1_xboole_0(X1)
    | ~ v12_waybel_0(X1,k7_lattice3(esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ v13_waybel_0(esk3_0,k7_lattice3(esk2_0))
    | ~ v2_waybel_0(X1,esk2_0)
    | ~ r1_subset_1(X1,esk3_0)
    | ~ v1_lattice3(k7_lattice3(esk2_0))
    | ~ v2_lattice3(k7_lattice3(esk2_0))
    | ~ v5_orders_2(k7_lattice3(esk2_0))
    | ~ v4_orders_2(k7_lattice3(esk2_0))
    | ~ v3_orders_2(k7_lattice3(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_44]),c_0_45]),c_0_46]),c_0_47]),c_0_48]),c_0_49]),c_0_50]),c_0_35])])).

cnf(c_0_71,negated_conjecture,
    ( r1_subset_1(esk1_3(k7_lattice3(esk2_0),X1,esk3_0),esk3_0)
    | v1_xboole_0(X1)
    | ~ v12_waybel_0(X1,k7_lattice3(esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ v13_waybel_0(esk3_0,k7_lattice3(esk2_0))
    | ~ v2_waybel_0(X1,esk2_0)
    | ~ r1_subset_1(X1,esk3_0)
    | ~ v2_waybel_1(k7_lattice3(esk2_0))
    | ~ v1_lattice3(k7_lattice3(esk2_0))
    | ~ v2_lattice3(k7_lattice3(esk2_0))
    | ~ v5_orders_2(k7_lattice3(esk2_0))
    | ~ v4_orders_2(k7_lattice3(esk2_0))
    | ~ v3_orders_2(k7_lattice3(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_33]),c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_72,negated_conjecture,
    ( r1_tarski(X1,esk1_3(k7_lattice3(esk2_0),X1,esk3_0))
    | v1_xboole_0(X1)
    | ~ v12_waybel_0(X1,k7_lattice3(esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ v13_waybel_0(esk3_0,k7_lattice3(esk2_0))
    | ~ v2_waybel_0(X1,esk2_0)
    | ~ r1_subset_1(X1,esk3_0)
    | ~ v2_waybel_1(k7_lattice3(esk2_0))
    | ~ v1_lattice3(k7_lattice3(esk2_0))
    | ~ v2_lattice3(k7_lattice3(esk2_0))
    | ~ v5_orders_2(k7_lattice3(esk2_0))
    | ~ v4_orders_2(k7_lattice3(esk2_0))
    | ~ v3_orders_2(k7_lattice3(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_33]),c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_73,negated_conjecture,
    ( m1_subset_1(esk1_3(k7_lattice3(esk2_0),X1,esk3_0),k1_zfmisc_1(u1_struct_0(k7_lattice3(esk2_0))))
    | v1_xboole_0(X1)
    | ~ v12_waybel_0(X1,k7_lattice3(esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ v13_waybel_0(esk3_0,k7_lattice3(esk2_0))
    | ~ v2_waybel_0(X1,esk2_0)
    | ~ r1_subset_1(X1,esk3_0)
    | ~ v5_orders_2(k7_lattice3(esk2_0))
    | ~ v4_orders_2(k7_lattice3(esk2_0))
    | ~ v3_orders_2(k7_lattice3(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_46]),c_0_35])])).

cnf(c_0_74,plain,
    ( v5_orders_2(k7_lattice3(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

fof(c_0_75,plain,(
    ! [X7] :
      ( ( v1_orders_2(k7_lattice3(X7))
        | ~ v4_orders_2(X7)
        | ~ l1_orders_2(X7) )
      & ( v4_orders_2(k7_lattice3(X7))
        | ~ v4_orders_2(X7)
        | ~ l1_orders_2(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc2_yellow_7])])])).

cnf(c_0_76,negated_conjecture,
    ( v1_waybel_0(esk1_3(k7_lattice3(esk2_0),X1,esk3_0),k7_lattice3(esk2_0))
    | v1_xboole_0(X1)
    | ~ v12_waybel_0(X1,k7_lattice3(esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ v13_waybel_0(esk3_0,k7_lattice3(esk2_0))
    | ~ v2_waybel_0(X1,esk2_0)
    | ~ r1_subset_1(X1,esk3_0)
    | ~ v5_orders_2(k7_lattice3(esk2_0))
    | ~ v4_orders_2(k7_lattice3(esk2_0))
    | ~ v3_orders_2(k7_lattice3(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_66]),c_0_46]),c_0_35])])).

cnf(c_0_77,negated_conjecture,
    ( v12_waybel_0(esk1_3(k7_lattice3(esk2_0),X1,esk3_0),k7_lattice3(esk2_0))
    | v1_xboole_0(X1)
    | ~ v12_waybel_0(X1,k7_lattice3(esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ v13_waybel_0(esk3_0,k7_lattice3(esk2_0))
    | ~ v2_waybel_0(X1,esk2_0)
    | ~ r1_subset_1(X1,esk3_0)
    | ~ v2_lattice3(k7_lattice3(esk2_0))
    | ~ v5_orders_2(k7_lattice3(esk2_0))
    | ~ v4_orders_2(k7_lattice3(esk2_0))
    | ~ v3_orders_2(k7_lattice3(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_58]),c_0_47]),c_0_35])])).

cnf(c_0_78,negated_conjecture,
    ( v1_waybel_7(esk1_3(k7_lattice3(esk2_0),X1,esk3_0),k7_lattice3(esk2_0))
    | v1_xboole_0(X1)
    | ~ v12_waybel_0(X1,k7_lattice3(esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ v13_waybel_0(esk3_0,k7_lattice3(esk2_0))
    | ~ v2_waybel_0(X1,esk2_0)
    | ~ r1_subset_1(X1,esk3_0)
    | ~ v2_lattice3(k7_lattice3(esk2_0))
    | ~ v5_orders_2(k7_lattice3(esk2_0))
    | ~ v4_orders_2(k7_lattice3(esk2_0))
    | ~ v3_orders_2(k7_lattice3(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_58]),c_0_47]),c_0_35])])).

cnf(c_0_79,negated_conjecture,
    ( r1_subset_1(esk1_3(k7_lattice3(esk2_0),X1,esk3_0),esk3_0)
    | v1_xboole_0(X1)
    | ~ v12_waybel_0(X1,k7_lattice3(esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ v13_waybel_0(esk3_0,k7_lattice3(esk2_0))
    | ~ v2_waybel_0(X1,esk2_0)
    | ~ r1_subset_1(X1,esk3_0)
    | ~ v1_lattice3(k7_lattice3(esk2_0))
    | ~ v2_lattice3(k7_lattice3(esk2_0))
    | ~ v5_orders_2(k7_lattice3(esk2_0))
    | ~ v4_orders_2(k7_lattice3(esk2_0))
    | ~ v3_orders_2(k7_lattice3(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_44]),c_0_45]),c_0_46]),c_0_47]),c_0_48]),c_0_49]),c_0_50]),c_0_35])])).

cnf(c_0_80,negated_conjecture,
    ( r1_tarski(X1,esk1_3(k7_lattice3(esk2_0),X1,esk3_0))
    | v1_xboole_0(X1)
    | ~ v12_waybel_0(X1,k7_lattice3(esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ v13_waybel_0(esk3_0,k7_lattice3(esk2_0))
    | ~ v2_waybel_0(X1,esk2_0)
    | ~ r1_subset_1(X1,esk3_0)
    | ~ v1_lattice3(k7_lattice3(esk2_0))
    | ~ v2_lattice3(k7_lattice3(esk2_0))
    | ~ v5_orders_2(k7_lattice3(esk2_0))
    | ~ v4_orders_2(k7_lattice3(esk2_0))
    | ~ v3_orders_2(k7_lattice3(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_44]),c_0_45]),c_0_46]),c_0_47]),c_0_48]),c_0_49]),c_0_50]),c_0_35])])).

cnf(c_0_81,negated_conjecture,
    ( m1_subset_1(esk1_3(k7_lattice3(esk2_0),X1,esk3_0),k1_zfmisc_1(u1_struct_0(k7_lattice3(esk2_0))))
    | v1_xboole_0(X1)
    | ~ v12_waybel_0(X1,k7_lattice3(esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ v13_waybel_0(esk3_0,k7_lattice3(esk2_0))
    | ~ v2_waybel_0(X1,esk2_0)
    | ~ r1_subset_1(X1,esk3_0)
    | ~ v4_orders_2(k7_lattice3(esk2_0))
    | ~ v3_orders_2(k7_lattice3(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_48]),c_0_35])])).

cnf(c_0_82,plain,
    ( v4_orders_2(k7_lattice3(X1))
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

fof(c_0_83,plain,(
    ! [X6] :
      ( ( v1_orders_2(k7_lattice3(X6))
        | ~ v3_orders_2(X6)
        | ~ l1_orders_2(X6) )
      & ( v3_orders_2(k7_lattice3(X6))
        | ~ v3_orders_2(X6)
        | ~ l1_orders_2(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_yellow_7])])])).

cnf(c_0_84,negated_conjecture,
    ( v1_waybel_0(esk1_3(k7_lattice3(esk2_0),X1,esk3_0),k7_lattice3(esk2_0))
    | v1_xboole_0(X1)
    | ~ v12_waybel_0(X1,k7_lattice3(esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ v13_waybel_0(esk3_0,k7_lattice3(esk2_0))
    | ~ v2_waybel_0(X1,esk2_0)
    | ~ r1_subset_1(X1,esk3_0)
    | ~ v4_orders_2(k7_lattice3(esk2_0))
    | ~ v3_orders_2(k7_lattice3(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_74]),c_0_48]),c_0_35])])).

cnf(c_0_85,negated_conjecture,
    ( v12_waybel_0(esk1_3(k7_lattice3(esk2_0),X1,esk3_0),k7_lattice3(esk2_0))
    | v1_xboole_0(X1)
    | ~ v12_waybel_0(X1,k7_lattice3(esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ v13_waybel_0(esk3_0,k7_lattice3(esk2_0))
    | ~ v2_waybel_0(X1,esk2_0)
    | ~ r1_subset_1(X1,esk3_0)
    | ~ v5_orders_2(k7_lattice3(esk2_0))
    | ~ v4_orders_2(k7_lattice3(esk2_0))
    | ~ v3_orders_2(k7_lattice3(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_66]),c_0_46]),c_0_35])])).

cnf(c_0_86,negated_conjecture,
    ( v1_waybel_7(esk1_3(k7_lattice3(esk2_0),X1,esk3_0),k7_lattice3(esk2_0))
    | v1_xboole_0(X1)
    | ~ v12_waybel_0(X1,k7_lattice3(esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ v13_waybel_0(esk3_0,k7_lattice3(esk2_0))
    | ~ v2_waybel_0(X1,esk2_0)
    | ~ r1_subset_1(X1,esk3_0)
    | ~ v5_orders_2(k7_lattice3(esk2_0))
    | ~ v4_orders_2(k7_lattice3(esk2_0))
    | ~ v3_orders_2(k7_lattice3(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_66]),c_0_46]),c_0_35])])).

cnf(c_0_87,negated_conjecture,
    ( r1_subset_1(esk1_3(k7_lattice3(esk2_0),X1,esk3_0),esk3_0)
    | v1_xboole_0(X1)
    | ~ v12_waybel_0(X1,k7_lattice3(esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ v13_waybel_0(esk3_0,k7_lattice3(esk2_0))
    | ~ v2_waybel_0(X1,esk2_0)
    | ~ r1_subset_1(X1,esk3_0)
    | ~ v2_lattice3(k7_lattice3(esk2_0))
    | ~ v5_orders_2(k7_lattice3(esk2_0))
    | ~ v4_orders_2(k7_lattice3(esk2_0))
    | ~ v3_orders_2(k7_lattice3(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_58]),c_0_47]),c_0_35])])).

cnf(c_0_88,negated_conjecture,
    ( r1_tarski(X1,esk1_3(k7_lattice3(esk2_0),X1,esk3_0))
    | v1_xboole_0(X1)
    | ~ v12_waybel_0(X1,k7_lattice3(esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ v13_waybel_0(esk3_0,k7_lattice3(esk2_0))
    | ~ v2_waybel_0(X1,esk2_0)
    | ~ r1_subset_1(X1,esk3_0)
    | ~ v2_lattice3(k7_lattice3(esk2_0))
    | ~ v5_orders_2(k7_lattice3(esk2_0))
    | ~ v4_orders_2(k7_lattice3(esk2_0))
    | ~ v3_orders_2(k7_lattice3(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_58]),c_0_47]),c_0_35])])).

fof(c_0_89,plain,(
    ! [X1] :
      ( epred1_1(X1)
    <=> ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v2_waybel_0(X2,X1)
            & v13_waybel_0(X2,X1)
            & v2_waybel_7(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
        <=> ( ~ v1_xboole_0(X2)
            & v1_waybel_0(X2,k7_lattice3(X1))
            & v12_waybel_0(X2,k7_lattice3(X1))
            & v1_waybel_7(X2,k7_lattice3(X1))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k7_lattice3(X1)))) ) ) ) ),
    introduced(definition)).

cnf(c_0_90,negated_conjecture,
    ( m1_subset_1(esk1_3(k7_lattice3(esk2_0),X1,esk3_0),k1_zfmisc_1(u1_struct_0(k7_lattice3(esk2_0))))
    | v1_xboole_0(X1)
    | ~ v12_waybel_0(X1,k7_lattice3(esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ v13_waybel_0(esk3_0,k7_lattice3(esk2_0))
    | ~ v2_waybel_0(X1,esk2_0)
    | ~ r1_subset_1(X1,esk3_0)
    | ~ v3_orders_2(k7_lattice3(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_49]),c_0_35])])).

cnf(c_0_91,plain,
    ( v3_orders_2(k7_lattice3(X1))
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

fof(c_0_92,plain,(
    ! [X23,X24] :
      ( ( v13_waybel_0(X24,k7_lattice3(X23))
        | ~ v12_waybel_0(X24,X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))
        | ~ l1_orders_2(X23) )
      & ( m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(k7_lattice3(X23))))
        | ~ v12_waybel_0(X24,X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))
        | ~ l1_orders_2(X23) )
      & ( v12_waybel_0(X24,X23)
        | ~ v13_waybel_0(X24,k7_lattice3(X23))
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(k7_lattice3(X23))))
        | ~ l1_orders_2(X23) )
      & ( m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))
        | ~ v13_waybel_0(X24,k7_lattice3(X23))
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(k7_lattice3(X23))))
        | ~ l1_orders_2(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_yellow_7])])])])).

fof(c_0_93,plain,(
    ! [X12,X13] :
      ( v1_xboole_0(X12)
      | v1_xboole_0(X13)
      | ~ r1_subset_1(X12,X13)
      | r1_subset_1(X13,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[symmetry_r1_subset_1])])])).

cnf(c_0_94,negated_conjecture,
    ( v1_waybel_0(esk1_3(k7_lattice3(esk2_0),X1,esk3_0),k7_lattice3(esk2_0))
    | v1_xboole_0(X1)
    | ~ v12_waybel_0(X1,k7_lattice3(esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ v13_waybel_0(esk3_0,k7_lattice3(esk2_0))
    | ~ v2_waybel_0(X1,esk2_0)
    | ~ r1_subset_1(X1,esk3_0)
    | ~ v3_orders_2(k7_lattice3(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_82]),c_0_49]),c_0_35])])).

cnf(c_0_95,negated_conjecture,
    ( v12_waybel_0(esk1_3(k7_lattice3(esk2_0),X1,esk3_0),k7_lattice3(esk2_0))
    | v1_xboole_0(X1)
    | ~ v12_waybel_0(X1,k7_lattice3(esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ v13_waybel_0(esk3_0,k7_lattice3(esk2_0))
    | ~ v2_waybel_0(X1,esk2_0)
    | ~ r1_subset_1(X1,esk3_0)
    | ~ v4_orders_2(k7_lattice3(esk2_0))
    | ~ v3_orders_2(k7_lattice3(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_74]),c_0_48]),c_0_35])])).

cnf(c_0_96,negated_conjecture,
    ( v1_waybel_7(esk1_3(k7_lattice3(esk2_0),X1,esk3_0),k7_lattice3(esk2_0))
    | v1_xboole_0(X1)
    | ~ v12_waybel_0(X1,k7_lattice3(esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ v13_waybel_0(esk3_0,k7_lattice3(esk2_0))
    | ~ v2_waybel_0(X1,esk2_0)
    | ~ r1_subset_1(X1,esk3_0)
    | ~ v4_orders_2(k7_lattice3(esk2_0))
    | ~ v3_orders_2(k7_lattice3(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_74]),c_0_48]),c_0_35])])).

cnf(c_0_97,negated_conjecture,
    ( r1_subset_1(esk1_3(k7_lattice3(esk2_0),X1,esk3_0),esk3_0)
    | v1_xboole_0(X1)
    | ~ v12_waybel_0(X1,k7_lattice3(esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ v13_waybel_0(esk3_0,k7_lattice3(esk2_0))
    | ~ v2_waybel_0(X1,esk2_0)
    | ~ r1_subset_1(X1,esk3_0)
    | ~ v5_orders_2(k7_lattice3(esk2_0))
    | ~ v4_orders_2(k7_lattice3(esk2_0))
    | ~ v3_orders_2(k7_lattice3(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_66]),c_0_46]),c_0_35])])).

cnf(c_0_98,negated_conjecture,
    ( r1_tarski(X1,esk1_3(k7_lattice3(esk2_0),X1,esk3_0))
    | v1_xboole_0(X1)
    | ~ v12_waybel_0(X1,k7_lattice3(esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ v13_waybel_0(esk3_0,k7_lattice3(esk2_0))
    | ~ v2_waybel_0(X1,esk2_0)
    | ~ r1_subset_1(X1,esk3_0)
    | ~ v5_orders_2(k7_lattice3(esk2_0))
    | ~ v4_orders_2(k7_lattice3(esk2_0))
    | ~ v3_orders_2(k7_lattice3(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_66]),c_0_46]),c_0_35])])).

fof(c_0_99,plain,(
    ! [X1] :
      ( epred1_1(X1)
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v2_waybel_0(X2,X1)
            & v13_waybel_0(X2,X1)
            & v2_waybel_7(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
        <=> ( ~ v1_xboole_0(X2)
            & v1_waybel_0(X2,k7_lattice3(X1))
            & v12_waybel_0(X2,k7_lattice3(X1))
            & v1_waybel_7(X2,k7_lattice3(X1))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k7_lattice3(X1)))) ) ) ) ),
    inference(split_equiv,[status(thm)],[c_0_89])).

cnf(c_0_100,negated_conjecture,
    ( m1_subset_1(esk1_3(k7_lattice3(esk2_0),X1,esk3_0),k1_zfmisc_1(u1_struct_0(k7_lattice3(esk2_0))))
    | v1_xboole_0(X1)
    | ~ v12_waybel_0(X1,k7_lattice3(esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ v13_waybel_0(esk3_0,k7_lattice3(esk2_0))
    | ~ v2_waybel_0(X1,esk2_0)
    | ~ r1_subset_1(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_50]),c_0_35])])).

cnf(c_0_101,plain,
    ( v13_waybel_0(X1,k7_lattice3(X2))
    | ~ v12_waybel_0(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_92])).

cnf(c_0_102,negated_conjecture,
    ( v12_waybel_0(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_103,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | r1_subset_1(X2,X1)
    | ~ r1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_93])).

cnf(c_0_104,negated_conjecture,
    ( r1_subset_1(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_105,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_106,negated_conjecture,
    ( v1_waybel_0(esk1_3(k7_lattice3(esk2_0),X1,esk3_0),k7_lattice3(esk2_0))
    | v1_xboole_0(X1)
    | ~ v12_waybel_0(X1,k7_lattice3(esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ v13_waybel_0(esk3_0,k7_lattice3(esk2_0))
    | ~ v2_waybel_0(X1,esk2_0)
    | ~ r1_subset_1(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_91]),c_0_50]),c_0_35])])).

cnf(c_0_107,negated_conjecture,
    ( v12_waybel_0(esk1_3(k7_lattice3(esk2_0),X1,esk3_0),k7_lattice3(esk2_0))
    | v1_xboole_0(X1)
    | ~ v12_waybel_0(X1,k7_lattice3(esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ v13_waybel_0(esk3_0,k7_lattice3(esk2_0))
    | ~ v2_waybel_0(X1,esk2_0)
    | ~ r1_subset_1(X1,esk3_0)
    | ~ v3_orders_2(k7_lattice3(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_82]),c_0_49]),c_0_35])])).

cnf(c_0_108,negated_conjecture,
    ( v1_waybel_7(esk1_3(k7_lattice3(esk2_0),X1,esk3_0),k7_lattice3(esk2_0))
    | v1_xboole_0(X1)
    | ~ v12_waybel_0(X1,k7_lattice3(esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ v13_waybel_0(esk3_0,k7_lattice3(esk2_0))
    | ~ v2_waybel_0(X1,esk2_0)
    | ~ r1_subset_1(X1,esk3_0)
    | ~ v3_orders_2(k7_lattice3(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_82]),c_0_49]),c_0_35])])).

cnf(c_0_109,negated_conjecture,
    ( r1_subset_1(esk1_3(k7_lattice3(esk2_0),X1,esk3_0),esk3_0)
    | v1_xboole_0(X1)
    | ~ v12_waybel_0(X1,k7_lattice3(esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ v13_waybel_0(esk3_0,k7_lattice3(esk2_0))
    | ~ v2_waybel_0(X1,esk2_0)
    | ~ r1_subset_1(X1,esk3_0)
    | ~ v4_orders_2(k7_lattice3(esk2_0))
    | ~ v3_orders_2(k7_lattice3(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_74]),c_0_48]),c_0_35])])).

cnf(c_0_110,negated_conjecture,
    ( r1_tarski(X1,esk1_3(k7_lattice3(esk2_0),X1,esk3_0))
    | v1_xboole_0(X1)
    | ~ v12_waybel_0(X1,k7_lattice3(esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ v13_waybel_0(esk3_0,k7_lattice3(esk2_0))
    | ~ v2_waybel_0(X1,esk2_0)
    | ~ r1_subset_1(X1,esk3_0)
    | ~ v4_orders_2(k7_lattice3(esk2_0))
    | ~ v3_orders_2(k7_lattice3(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_74]),c_0_48]),c_0_35])])).

fof(c_0_111,plain,(
    ! [X31,X32] :
      ( ( ~ v1_xboole_0(X32)
        | v1_xboole_0(X32)
        | ~ v2_waybel_0(X32,X31)
        | ~ v13_waybel_0(X32,X31)
        | ~ v2_waybel_7(X32,X31)
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))
        | ~ epred1_1(X31) )
      & ( v1_waybel_0(X32,k7_lattice3(X31))
        | v1_xboole_0(X32)
        | ~ v2_waybel_0(X32,X31)
        | ~ v13_waybel_0(X32,X31)
        | ~ v2_waybel_7(X32,X31)
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))
        | ~ epred1_1(X31) )
      & ( v12_waybel_0(X32,k7_lattice3(X31))
        | v1_xboole_0(X32)
        | ~ v2_waybel_0(X32,X31)
        | ~ v13_waybel_0(X32,X31)
        | ~ v2_waybel_7(X32,X31)
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))
        | ~ epred1_1(X31) )
      & ( v1_waybel_7(X32,k7_lattice3(X31))
        | v1_xboole_0(X32)
        | ~ v2_waybel_0(X32,X31)
        | ~ v13_waybel_0(X32,X31)
        | ~ v2_waybel_7(X32,X31)
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))
        | ~ epred1_1(X31) )
      & ( m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(k7_lattice3(X31))))
        | v1_xboole_0(X32)
        | ~ v2_waybel_0(X32,X31)
        | ~ v13_waybel_0(X32,X31)
        | ~ v2_waybel_7(X32,X31)
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))
        | ~ epred1_1(X31) )
      & ( ~ v1_xboole_0(X32)
        | v1_xboole_0(X32)
        | ~ v1_waybel_0(X32,k7_lattice3(X31))
        | ~ v12_waybel_0(X32,k7_lattice3(X31))
        | ~ v1_waybel_7(X32,k7_lattice3(X31))
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(k7_lattice3(X31))))
        | ~ epred1_1(X31) )
      & ( v2_waybel_0(X32,X31)
        | v1_xboole_0(X32)
        | ~ v1_waybel_0(X32,k7_lattice3(X31))
        | ~ v12_waybel_0(X32,k7_lattice3(X31))
        | ~ v1_waybel_7(X32,k7_lattice3(X31))
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(k7_lattice3(X31))))
        | ~ epred1_1(X31) )
      & ( v13_waybel_0(X32,X31)
        | v1_xboole_0(X32)
        | ~ v1_waybel_0(X32,k7_lattice3(X31))
        | ~ v12_waybel_0(X32,k7_lattice3(X31))
        | ~ v1_waybel_7(X32,k7_lattice3(X31))
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(k7_lattice3(X31))))
        | ~ epred1_1(X31) )
      & ( v2_waybel_7(X32,X31)
        | v1_xboole_0(X32)
        | ~ v1_waybel_0(X32,k7_lattice3(X31))
        | ~ v12_waybel_0(X32,k7_lattice3(X31))
        | ~ v1_waybel_7(X32,k7_lattice3(X31))
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(k7_lattice3(X31))))
        | ~ epred1_1(X31) )
      & ( m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))
        | v1_xboole_0(X32)
        | ~ v1_waybel_0(X32,k7_lattice3(X31))
        | ~ v12_waybel_0(X32,k7_lattice3(X31))
        | ~ v1_waybel_7(X32,k7_lattice3(X31))
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(k7_lattice3(X31))))
        | ~ epred1_1(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_99])])])])])).

cnf(c_0_112,negated_conjecture,
    ( m1_subset_1(esk1_3(k7_lattice3(esk2_0),X1,esk3_0),k1_zfmisc_1(u1_struct_0(k7_lattice3(esk2_0))))
    | v1_xboole_0(X1)
    | ~ v12_waybel_0(X1,k7_lattice3(esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ v2_waybel_0(X1,esk2_0)
    | ~ r1_subset_1(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_101]),c_0_102]),c_0_33]),c_0_35])])).

cnf(c_0_113,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_114,negated_conjecture,
    ( v2_waybel_0(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_115,negated_conjecture,
    ( r1_subset_1(esk4_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_104]),c_0_105]),c_0_36])).

cnf(c_0_116,negated_conjecture,
    ( v1_waybel_0(esk1_3(k7_lattice3(esk2_0),X1,esk3_0),k7_lattice3(esk2_0))
    | v1_xboole_0(X1)
    | ~ v12_waybel_0(X1,k7_lattice3(esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ v2_waybel_0(X1,esk2_0)
    | ~ r1_subset_1(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_101]),c_0_102]),c_0_33]),c_0_35])])).

cnf(c_0_117,negated_conjecture,
    ( v12_waybel_0(esk1_3(k7_lattice3(esk2_0),X1,esk3_0),k7_lattice3(esk2_0))
    | v1_xboole_0(X1)
    | ~ v12_waybel_0(X1,k7_lattice3(esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ v13_waybel_0(esk3_0,k7_lattice3(esk2_0))
    | ~ v2_waybel_0(X1,esk2_0)
    | ~ r1_subset_1(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_91]),c_0_50]),c_0_35])])).

cnf(c_0_118,negated_conjecture,
    ( v1_waybel_7(esk1_3(k7_lattice3(esk2_0),X1,esk3_0),k7_lattice3(esk2_0))
    | v1_xboole_0(X1)
    | ~ v12_waybel_0(X1,k7_lattice3(esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ v13_waybel_0(esk3_0,k7_lattice3(esk2_0))
    | ~ v2_waybel_0(X1,esk2_0)
    | ~ r1_subset_1(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_91]),c_0_50]),c_0_35])])).

cnf(c_0_119,negated_conjecture,
    ( r1_subset_1(esk1_3(k7_lattice3(esk2_0),X1,esk3_0),esk3_0)
    | v1_xboole_0(X1)
    | ~ v12_waybel_0(X1,k7_lattice3(esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ v13_waybel_0(esk3_0,k7_lattice3(esk2_0))
    | ~ v2_waybel_0(X1,esk2_0)
    | ~ r1_subset_1(X1,esk3_0)
    | ~ v3_orders_2(k7_lattice3(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_82]),c_0_49]),c_0_35])])).

cnf(c_0_120,negated_conjecture,
    ( r1_tarski(X1,esk1_3(k7_lattice3(esk2_0),X1,esk3_0))
    | v1_xboole_0(X1)
    | ~ v12_waybel_0(X1,k7_lattice3(esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ v13_waybel_0(esk3_0,k7_lattice3(esk2_0))
    | ~ v2_waybel_0(X1,esk2_0)
    | ~ r1_subset_1(X1,esk3_0)
    | ~ v3_orders_2(k7_lattice3(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_82]),c_0_49]),c_0_35])])).

cnf(c_0_121,plain,
    ( v2_waybel_7(X1,X2)
    | v1_xboole_0(X1)
    | ~ v1_waybel_0(X1,k7_lattice3(X2))
    | ~ v12_waybel_0(X1,k7_lattice3(X2))
    | ~ v1_waybel_7(X1,k7_lattice3(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X2))))
    | ~ epred1_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_111])).

cnf(c_0_122,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v1_waybel_0(X1,k7_lattice3(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X2))))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_123,negated_conjecture,
    ( m1_subset_1(esk1_3(k7_lattice3(esk2_0),esk4_0,esk3_0),k1_zfmisc_1(u1_struct_0(k7_lattice3(esk2_0))))
    | ~ v12_waybel_0(esk4_0,k7_lattice3(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_113]),c_0_114]),c_0_115])]),c_0_105])).

cnf(c_0_124,negated_conjecture,
    ( v1_waybel_0(esk1_3(k7_lattice3(esk2_0),esk4_0,esk3_0),k7_lattice3(esk2_0))
    | ~ v12_waybel_0(esk4_0,k7_lattice3(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_113]),c_0_114]),c_0_115])]),c_0_105])).

cnf(c_0_125,plain,
    ( v2_waybel_0(X1,X2)
    | ~ v1_waybel_0(X1,k7_lattice3(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X2))))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_126,negated_conjecture,
    ( v12_waybel_0(esk1_3(k7_lattice3(esk2_0),X1,esk3_0),k7_lattice3(esk2_0))
    | v1_xboole_0(X1)
    | ~ v12_waybel_0(X1,k7_lattice3(esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ v2_waybel_0(X1,esk2_0)
    | ~ r1_subset_1(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_101]),c_0_102]),c_0_33]),c_0_35])])).

cnf(c_0_127,negated_conjecture,
    ( v1_waybel_7(esk1_3(k7_lattice3(esk2_0),X1,esk3_0),k7_lattice3(esk2_0))
    | v1_xboole_0(X1)
    | ~ v12_waybel_0(X1,k7_lattice3(esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ v2_waybel_0(X1,esk2_0)
    | ~ r1_subset_1(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118,c_0_101]),c_0_102]),c_0_33]),c_0_35])])).

fof(c_0_128,axiom,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & v1_lattice3(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1) )
     => epred1_1(X1) ) ),
    inference(apply_def,[status(thm)],[t21_waybel_7,c_0_89])).

cnf(c_0_129,negated_conjecture,
    ( r1_subset_1(esk1_3(k7_lattice3(esk2_0),X1,esk3_0),esk3_0)
    | v1_xboole_0(X1)
    | ~ v12_waybel_0(X1,k7_lattice3(esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ v13_waybel_0(esk3_0,k7_lattice3(esk2_0))
    | ~ v2_waybel_0(X1,esk2_0)
    | ~ r1_subset_1(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_91]),c_0_50]),c_0_35])])).

cnf(c_0_130,negated_conjecture,
    ( r1_tarski(X1,esk1_3(k7_lattice3(esk2_0),X1,esk3_0))
    | v1_xboole_0(X1)
    | ~ v12_waybel_0(X1,k7_lattice3(esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ v13_waybel_0(esk3_0,k7_lattice3(esk2_0))
    | ~ v2_waybel_0(X1,esk2_0)
    | ~ r1_subset_1(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_91]),c_0_50]),c_0_35])])).

cnf(c_0_131,plain,
    ( v2_waybel_7(X1,X2)
    | v1_xboole_0(X1)
    | ~ epred1_1(X2)
    | ~ v1_waybel_7(X1,k7_lattice3(X2))
    | ~ v12_waybel_0(X1,k7_lattice3(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_waybel_0(X1,X2)
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_26]),c_0_27])).

cnf(c_0_132,negated_conjecture,
    ( m1_subset_1(esk1_3(k7_lattice3(esk2_0),esk4_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ v12_waybel_0(esk4_0,k7_lattice3(esk2_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122,c_0_123]),c_0_35])]),c_0_124])).

cnf(c_0_133,negated_conjecture,
    ( v2_waybel_0(esk1_3(k7_lattice3(esk2_0),esk4_0,esk3_0),esk2_0)
    | ~ v12_waybel_0(esk4_0,k7_lattice3(esk2_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125,c_0_123]),c_0_35])]),c_0_124])).

cnf(c_0_134,negated_conjecture,
    ( v12_waybel_0(esk1_3(k7_lattice3(esk2_0),esk4_0,esk3_0),k7_lattice3(esk2_0))
    | ~ v12_waybel_0(esk4_0,k7_lattice3(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126,c_0_113]),c_0_114]),c_0_115])]),c_0_105])).

cnf(c_0_135,negated_conjecture,
    ( v1_waybel_7(esk1_3(k7_lattice3(esk2_0),esk4_0,esk3_0),k7_lattice3(esk2_0))
    | ~ v12_waybel_0(esk4_0,k7_lattice3(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127,c_0_113]),c_0_114]),c_0_115])]),c_0_105])).

fof(c_0_136,plain,(
    ! [X14] :
      ( ~ v3_orders_2(X14)
      | ~ v4_orders_2(X14)
      | ~ v5_orders_2(X14)
      | ~ v1_lattice3(X14)
      | ~ v2_lattice3(X14)
      | ~ l1_orders_2(X14)
      | epred1_1(X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_128])])).

cnf(c_0_137,negated_conjecture,
    ( r1_subset_1(esk1_3(k7_lattice3(esk2_0),X1,esk3_0),esk3_0)
    | v1_xboole_0(X1)
    | ~ v12_waybel_0(X1,k7_lattice3(esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ v2_waybel_0(X1,esk2_0)
    | ~ r1_subset_1(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_129,c_0_101]),c_0_102]),c_0_33]),c_0_35])])).

cnf(c_0_138,negated_conjecture,
    ( r1_tarski(X1,esk1_3(k7_lattice3(esk2_0),X1,esk3_0))
    | v1_xboole_0(X1)
    | ~ v12_waybel_0(X1,k7_lattice3(esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ v2_waybel_0(X1,esk2_0)
    | ~ r1_subset_1(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_130,c_0_101]),c_0_102]),c_0_33]),c_0_35])])).

cnf(c_0_139,plain,
    ( v2_waybel_7(esk1_3(k7_lattice3(esk2_0),esk4_0,esk3_0),esk2_0)
    | v1_xboole_0(esk1_3(k7_lattice3(esk2_0),esk4_0,esk3_0))
    | ~ epred1_1(esk2_0)
    | ~ v12_waybel_0(esk4_0,k7_lattice3(esk2_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131,c_0_132]),c_0_35])]),c_0_133]),c_0_134]),c_0_135])).

cnf(c_0_140,plain,
    ( epred1_1(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_136])).

fof(c_0_141,plain,(
    ! [X25,X26] :
      ( ( v13_waybel_0(X26,X25)
        | ~ v12_waybel_0(X26,k7_lattice3(X25))
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(k7_lattice3(X25))))
        | ~ l1_orders_2(X25) )
      & ( m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ v12_waybel_0(X26,k7_lattice3(X25))
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(k7_lattice3(X25))))
        | ~ l1_orders_2(X25) )
      & ( v12_waybel_0(X26,k7_lattice3(X25))
        | ~ v13_waybel_0(X26,X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ l1_orders_2(X25) )
      & ( m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(k7_lattice3(X25))))
        | ~ v13_waybel_0(X26,X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ l1_orders_2(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_yellow_7])])])])).

cnf(c_0_142,negated_conjecture,
    ( r1_subset_1(esk1_3(k7_lattice3(esk2_0),esk4_0,esk3_0),esk3_0)
    | ~ v12_waybel_0(esk4_0,k7_lattice3(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137,c_0_113]),c_0_114]),c_0_115])]),c_0_105])).

cnf(c_0_143,plain,
    ( v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | ~ v1_xboole_0(esk1_3(X1,X2,X3))
    | ~ r1_subset_1(X2,X3)
    | ~ v2_waybel_0(X3,X1)
    | ~ v13_waybel_0(X3,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_waybel_0(X2,X1)
    | ~ v12_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_waybel_1(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_144,negated_conjecture,
    ( v1_xboole_0(X1)
    | ~ v2_waybel_0(X1,esk2_0)
    | ~ v13_waybel_0(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ v2_waybel_7(X1,esk2_0)
    | ~ r1_tarski(esk4_0,X1)
    | ~ r1_subset_1(esk3_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_145,negated_conjecture,
    ( r1_tarski(esk4_0,esk1_3(k7_lattice3(esk2_0),esk4_0,esk3_0))
    | ~ v12_waybel_0(esk4_0,k7_lattice3(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_113]),c_0_114]),c_0_115])]),c_0_105])).

cnf(c_0_146,plain,
    ( v2_waybel_7(esk1_3(k7_lattice3(esk2_0),esk4_0,esk3_0),esk2_0)
    | v1_xboole_0(esk1_3(k7_lattice3(esk2_0),esk4_0,esk3_0))
    | ~ v12_waybel_0(esk4_0,k7_lattice3(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_139,c_0_140]),c_0_46]),c_0_47]),c_0_48]),c_0_49]),c_0_50]),c_0_35])])).

cnf(c_0_147,plain,
    ( v12_waybel_0(X1,k7_lattice3(X2))
    | ~ v13_waybel_0(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_141])).

cnf(c_0_148,negated_conjecture,
    ( v13_waybel_0(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_149,negated_conjecture,
    ( r1_subset_1(esk3_0,esk1_3(k7_lattice3(esk2_0),esk4_0,esk3_0))
    | v1_xboole_0(esk1_3(k7_lattice3(esk2_0),esk4_0,esk3_0))
    | ~ v12_waybel_0(esk4_0,k7_lattice3(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_142]),c_0_36])).

cnf(c_0_150,plain,
    ( v13_waybel_0(X1,X2)
    | ~ v12_waybel_0(X1,k7_lattice3(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X2))))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_141])).

cnf(c_0_151,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | ~ v12_waybel_0(X1,k7_lattice3(X3))
    | ~ v1_waybel_0(X1,k7_lattice3(X3))
    | ~ v1_waybel_0(X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X3))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v13_waybel_0(X2,k7_lattice3(X3))
    | ~ r1_subset_1(X1,X2)
    | ~ v1_xboole_0(esk1_3(k7_lattice3(X3),X1,X2))
    | ~ v2_waybel_1(k7_lattice3(X3))
    | ~ v1_lattice3(k7_lattice3(X3))
    | ~ v2_lattice3(k7_lattice3(X3))
    | ~ v5_orders_2(k7_lattice3(X3))
    | ~ v4_orders_2(k7_lattice3(X3))
    | ~ v3_orders_2(k7_lattice3(X3))
    | ~ l1_orders_2(X3) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_143,c_0_19]),c_0_20]),c_0_21])).

cnf(c_0_152,negated_conjecture,
    ( v1_xboole_0(esk1_3(k7_lattice3(esk2_0),esk4_0,esk3_0))
    | ~ v12_waybel_0(esk4_0,k7_lattice3(esk2_0))
    | ~ m1_subset_1(esk1_3(k7_lattice3(esk2_0),esk4_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ v2_waybel_7(esk1_3(k7_lattice3(esk2_0),esk4_0,esk3_0),esk2_0)
    | ~ v13_waybel_0(esk1_3(k7_lattice3(esk2_0),esk4_0,esk3_0),esk2_0)
    | ~ v2_waybel_0(esk1_3(k7_lattice3(esk2_0),esk4_0,esk3_0),esk2_0)
    | ~ r1_subset_1(esk3_0,esk1_3(k7_lattice3(esk2_0),esk4_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_144,c_0_145])).

cnf(c_0_153,plain,
    ( v2_waybel_7(esk1_3(k7_lattice3(esk2_0),esk4_0,esk3_0),esk2_0)
    | v1_xboole_0(esk1_3(k7_lattice3(esk2_0),esk4_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_146,c_0_147]),c_0_113]),c_0_148]),c_0_35])])).

cnf(c_0_154,negated_conjecture,
    ( r1_subset_1(esk3_0,esk1_3(k7_lattice3(esk2_0),esk4_0,esk3_0))
    | v1_xboole_0(esk1_3(k7_lattice3(esk2_0),esk4_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_149,c_0_147]),c_0_113]),c_0_148]),c_0_35])])).

cnf(c_0_155,negated_conjecture,
    ( v13_waybel_0(esk1_3(k7_lattice3(esk2_0),esk4_0,esk3_0),esk2_0)
    | ~ v12_waybel_0(esk4_0,k7_lattice3(esk2_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_150,c_0_123]),c_0_35])]),c_0_134])).

cnf(c_0_156,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | ~ v12_waybel_0(X2,k7_lattice3(X3))
    | ~ v1_waybel_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v13_waybel_0(X1,k7_lattice3(X3))
    | ~ v2_waybel_0(X2,X3)
    | ~ r1_subset_1(X2,X1)
    | ~ v1_xboole_0(esk1_3(k7_lattice3(X3),X2,X1))
    | ~ v2_waybel_1(k7_lattice3(X3))
    | ~ v1_lattice3(k7_lattice3(X3))
    | ~ v2_lattice3(k7_lattice3(X3))
    | ~ v5_orders_2(k7_lattice3(X3))
    | ~ v4_orders_2(k7_lattice3(X3))
    | ~ v3_orders_2(k7_lattice3(X3))
    | ~ l1_orders_2(X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_151,c_0_26]),c_0_27])).

cnf(c_0_157,negated_conjecture,
    ( v1_xboole_0(esk1_3(k7_lattice3(esk2_0),esk4_0,esk3_0))
    | ~ v12_waybel_0(esk4_0,k7_lattice3(esk2_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_152,c_0_153]),c_0_154]),c_0_133]),c_0_155]),c_0_132])).

cnf(c_0_158,negated_conjecture,
    ( ~ v12_waybel_0(esk4_0,k7_lattice3(esk2_0))
    | ~ v13_waybel_0(esk3_0,k7_lattice3(esk2_0))
    | ~ v2_waybel_1(k7_lattice3(esk2_0))
    | ~ v1_lattice3(k7_lattice3(esk2_0))
    | ~ v2_lattice3(k7_lattice3(esk2_0))
    | ~ v5_orders_2(k7_lattice3(esk2_0))
    | ~ v4_orders_2(k7_lattice3(esk2_0))
    | ~ v3_orders_2(k7_lattice3(esk2_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_156,c_0_157]),c_0_34]),c_0_33]),c_0_113]),c_0_114]),c_0_115]),c_0_35])]),c_0_36]),c_0_105])).

cnf(c_0_159,negated_conjecture,
    ( ~ v12_waybel_0(esk4_0,k7_lattice3(esk2_0))
    | ~ v13_waybel_0(esk3_0,k7_lattice3(esk2_0))
    | ~ v1_lattice3(k7_lattice3(esk2_0))
    | ~ v2_lattice3(k7_lattice3(esk2_0))
    | ~ v5_orders_2(k7_lattice3(esk2_0))
    | ~ v4_orders_2(k7_lattice3(esk2_0))
    | ~ v3_orders_2(k7_lattice3(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_158,c_0_44]),c_0_45]),c_0_46]),c_0_47]),c_0_48]),c_0_49]),c_0_50]),c_0_35])])).

cnf(c_0_160,negated_conjecture,
    ( ~ v12_waybel_0(esk4_0,k7_lattice3(esk2_0))
    | ~ v13_waybel_0(esk3_0,k7_lattice3(esk2_0))
    | ~ v2_lattice3(k7_lattice3(esk2_0))
    | ~ v5_orders_2(k7_lattice3(esk2_0))
    | ~ v4_orders_2(k7_lattice3(esk2_0))
    | ~ v3_orders_2(k7_lattice3(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_159,c_0_58]),c_0_47]),c_0_35])])).

cnf(c_0_161,negated_conjecture,
    ( ~ v12_waybel_0(esk4_0,k7_lattice3(esk2_0))
    | ~ v13_waybel_0(esk3_0,k7_lattice3(esk2_0))
    | ~ v5_orders_2(k7_lattice3(esk2_0))
    | ~ v4_orders_2(k7_lattice3(esk2_0))
    | ~ v3_orders_2(k7_lattice3(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_160,c_0_66]),c_0_46]),c_0_35])])).

cnf(c_0_162,negated_conjecture,
    ( ~ v12_waybel_0(esk4_0,k7_lattice3(esk2_0))
    | ~ v13_waybel_0(esk3_0,k7_lattice3(esk2_0))
    | ~ v4_orders_2(k7_lattice3(esk2_0))
    | ~ v3_orders_2(k7_lattice3(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_161,c_0_74]),c_0_48]),c_0_35])])).

cnf(c_0_163,negated_conjecture,
    ( ~ v12_waybel_0(esk4_0,k7_lattice3(esk2_0))
    | ~ v13_waybel_0(esk3_0,k7_lattice3(esk2_0))
    | ~ v3_orders_2(k7_lattice3(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_162,c_0_82]),c_0_49]),c_0_35])])).

cnf(c_0_164,negated_conjecture,
    ( ~ v12_waybel_0(esk4_0,k7_lattice3(esk2_0))
    | ~ v13_waybel_0(esk3_0,k7_lattice3(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_163,c_0_91]),c_0_50]),c_0_35])])).

cnf(c_0_165,negated_conjecture,
    ( ~ v13_waybel_0(esk3_0,k7_lattice3(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_164,c_0_147]),c_0_113]),c_0_148]),c_0_35])])).

cnf(c_0_166,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_165,c_0_101]),c_0_102]),c_0_33]),c_0_35])]),
    [proof]).

%------------------------------------------------------------------------------
