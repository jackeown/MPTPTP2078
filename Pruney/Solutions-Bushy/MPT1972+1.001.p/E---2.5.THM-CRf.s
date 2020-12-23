%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1972+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:05 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  312 (178631 expanded)
%              Number of clauses        :  285 (63734 expanded)
%              Number of leaves         :   12 (44898 expanded)
%              Depth                    :   66
%              Number of atoms          : 1948 (2859864 expanded)
%              Number of equality atoms :   52 (17767 expanded)
%              Maximal formula depth    :   33 (   6 average)
%              Maximal clause size      :   95 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t21_waybel_7,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_waybel_7)).

fof(t20_waybel_7,axiom,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & v1_lattice3(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v1_waybel_0(X2,X1)
            & v12_waybel_0(X2,X1)
            & v1_waybel_7(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
        <=> ( ~ v1_xboole_0(X2)
            & v2_waybel_0(X2,k7_lattice3(X1))
            & v13_waybel_0(X2,k7_lattice3(X1))
            & v2_waybel_7(X2,k7_lattice3(X1))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k7_lattice3(X1)))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_waybel_7)).

fof(fc6_yellow_7,axiom,(
    ! [X1] :
      ( ( v1_lattice3(X1)
        & l1_orders_2(X1) )
     => ( v1_orders_2(k7_lattice3(X1))
        & v2_lattice3(k7_lattice3(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_yellow_7)).

fof(fc5_yellow_7,axiom,(
    ! [X1] :
      ( ( v2_lattice3(X1)
        & l1_orders_2(X1) )
     => ( v1_orders_2(k7_lattice3(X1))
        & v1_lattice3(k7_lattice3(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow_7)).

fof(fc3_yellow_7,axiom,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ( v1_orders_2(k7_lattice3(X1))
        & v5_orders_2(k7_lattice3(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_yellow_7)).

fof(fc2_yellow_7,axiom,(
    ! [X1] :
      ( ( v4_orders_2(X1)
        & l1_orders_2(X1) )
     => ( v1_orders_2(k7_lattice3(X1))
        & v4_orders_2(k7_lattice3(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_yellow_7)).

fof(abstractness_v1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v1_orders_2(X1)
       => X1 = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_orders_2)).

fof(dt_k7_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v1_orders_2(k7_lattice3(X1))
        & l1_orders_2(k7_lattice3(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_lattice3)).

fof(t8_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => k7_lattice3(k7_lattice3(X1)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_lattice3)).

fof(fc1_yellow_7,axiom,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & l1_orders_2(X1) )
     => ( v1_orders_2(k7_lattice3(X1))
        & v3_orders_2(k7_lattice3(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_yellow_7)).

fof(t19_waybel_7,axiom,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & v1_lattice3(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( v3_orders_2(X2)
            & v4_orders_2(X2)
            & v5_orders_2(X2)
            & v1_lattice3(X2)
            & v2_lattice3(X2)
            & l1_orders_2(X2) )
         => ( g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
           => ! [X3] :
                ( ( ~ v1_xboole_0(X3)
                  & v2_waybel_0(X3,X1)
                  & v13_waybel_0(X3,X1)
                  & v2_waybel_7(X3,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
               => ( ~ v1_xboole_0(X3)
                  & v2_waybel_0(X3,X2)
                  & v13_waybel_0(X3,X2)
                  & v2_waybel_7(X3,X2)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_waybel_7)).

fof(c_0_11,plain,(
    ! [X1] :
      ( epred1_1(X1)
    <=> ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v1_waybel_0(X2,X1)
            & v12_waybel_0(X2,X1)
            & v1_waybel_7(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
        <=> ( ~ v1_xboole_0(X2)
            & v2_waybel_0(X2,k7_lattice3(X1))
            & v13_waybel_0(X2,k7_lattice3(X1))
            & v2_waybel_7(X2,k7_lattice3(X1))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k7_lattice3(X1)))) ) ) ) ),
    introduced(definition)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1] :
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
    inference(assume_negation,[status(cth)],[t21_waybel_7])).

fof(c_0_13,plain,(
    ! [X1] :
      ( epred1_1(X1)
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v1_waybel_0(X2,X1)
            & v12_waybel_0(X2,X1)
            & v1_waybel_7(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
        <=> ( ~ v1_xboole_0(X2)
            & v2_waybel_0(X2,k7_lattice3(X1))
            & v13_waybel_0(X2,k7_lattice3(X1))
            & v2_waybel_7(X2,k7_lattice3(X1))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k7_lattice3(X1)))) ) ) ) ),
    inference(split_equiv,[status(thm)],[c_0_11])).

fof(c_0_14,negated_conjecture,
    ( v3_orders_2(esk1_0)
    & v4_orders_2(esk1_0)
    & v5_orders_2(esk1_0)
    & v1_lattice3(esk1_0)
    & v2_lattice3(esk1_0)
    & l1_orders_2(esk1_0)
    & ( v1_xboole_0(esk2_0)
      | ~ v2_waybel_0(esk2_0,esk1_0)
      | ~ v13_waybel_0(esk2_0,esk1_0)
      | ~ v2_waybel_7(esk2_0,esk1_0)
      | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
      | v1_xboole_0(esk2_0)
      | ~ v1_waybel_0(esk2_0,k7_lattice3(esk1_0))
      | ~ v12_waybel_0(esk2_0,k7_lattice3(esk1_0))
      | ~ v1_waybel_7(esk2_0,k7_lattice3(esk1_0))
      | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(esk1_0)))) )
    & ( ~ v1_xboole_0(esk2_0)
      | ~ v1_xboole_0(esk2_0) )
    & ( v1_waybel_0(esk2_0,k7_lattice3(esk1_0))
      | ~ v1_xboole_0(esk2_0) )
    & ( v12_waybel_0(esk2_0,k7_lattice3(esk1_0))
      | ~ v1_xboole_0(esk2_0) )
    & ( v1_waybel_7(esk2_0,k7_lattice3(esk1_0))
      | ~ v1_xboole_0(esk2_0) )
    & ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(esk1_0))))
      | ~ v1_xboole_0(esk2_0) )
    & ( ~ v1_xboole_0(esk2_0)
      | v2_waybel_0(esk2_0,esk1_0) )
    & ( v1_waybel_0(esk2_0,k7_lattice3(esk1_0))
      | v2_waybel_0(esk2_0,esk1_0) )
    & ( v12_waybel_0(esk2_0,k7_lattice3(esk1_0))
      | v2_waybel_0(esk2_0,esk1_0) )
    & ( v1_waybel_7(esk2_0,k7_lattice3(esk1_0))
      | v2_waybel_0(esk2_0,esk1_0) )
    & ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(esk1_0))))
      | v2_waybel_0(esk2_0,esk1_0) )
    & ( ~ v1_xboole_0(esk2_0)
      | v13_waybel_0(esk2_0,esk1_0) )
    & ( v1_waybel_0(esk2_0,k7_lattice3(esk1_0))
      | v13_waybel_0(esk2_0,esk1_0) )
    & ( v12_waybel_0(esk2_0,k7_lattice3(esk1_0))
      | v13_waybel_0(esk2_0,esk1_0) )
    & ( v1_waybel_7(esk2_0,k7_lattice3(esk1_0))
      | v13_waybel_0(esk2_0,esk1_0) )
    & ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(esk1_0))))
      | v13_waybel_0(esk2_0,esk1_0) )
    & ( ~ v1_xboole_0(esk2_0)
      | v2_waybel_7(esk2_0,esk1_0) )
    & ( v1_waybel_0(esk2_0,k7_lattice3(esk1_0))
      | v2_waybel_7(esk2_0,esk1_0) )
    & ( v12_waybel_0(esk2_0,k7_lattice3(esk1_0))
      | v2_waybel_7(esk2_0,esk1_0) )
    & ( v1_waybel_7(esk2_0,k7_lattice3(esk1_0))
      | v2_waybel_7(esk2_0,esk1_0) )
    & ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(esk1_0))))
      | v2_waybel_7(esk2_0,esk1_0) )
    & ( ~ v1_xboole_0(esk2_0)
      | m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) )
    & ( v1_waybel_0(esk2_0,k7_lattice3(esk1_0))
      | m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) )
    & ( v12_waybel_0(esk2_0,k7_lattice3(esk1_0))
      | m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) )
    & ( v1_waybel_7(esk2_0,k7_lattice3(esk1_0))
      | m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) )
    & ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(esk1_0))))
      | m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])])).

fof(c_0_15,plain,(
    ! [X18,X19] :
      ( ( ~ v1_xboole_0(X19)
        | v1_xboole_0(X19)
        | ~ v1_waybel_0(X19,X18)
        | ~ v12_waybel_0(X19,X18)
        | ~ v1_waybel_7(X19,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ epred1_1(X18) )
      & ( v2_waybel_0(X19,k7_lattice3(X18))
        | v1_xboole_0(X19)
        | ~ v1_waybel_0(X19,X18)
        | ~ v12_waybel_0(X19,X18)
        | ~ v1_waybel_7(X19,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ epred1_1(X18) )
      & ( v13_waybel_0(X19,k7_lattice3(X18))
        | v1_xboole_0(X19)
        | ~ v1_waybel_0(X19,X18)
        | ~ v12_waybel_0(X19,X18)
        | ~ v1_waybel_7(X19,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ epred1_1(X18) )
      & ( v2_waybel_7(X19,k7_lattice3(X18))
        | v1_xboole_0(X19)
        | ~ v1_waybel_0(X19,X18)
        | ~ v12_waybel_0(X19,X18)
        | ~ v1_waybel_7(X19,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ epred1_1(X18) )
      & ( m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(k7_lattice3(X18))))
        | v1_xboole_0(X19)
        | ~ v1_waybel_0(X19,X18)
        | ~ v12_waybel_0(X19,X18)
        | ~ v1_waybel_7(X19,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ epred1_1(X18) )
      & ( ~ v1_xboole_0(X19)
        | v1_xboole_0(X19)
        | ~ v2_waybel_0(X19,k7_lattice3(X18))
        | ~ v13_waybel_0(X19,k7_lattice3(X18))
        | ~ v2_waybel_7(X19,k7_lattice3(X18))
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(k7_lattice3(X18))))
        | ~ epred1_1(X18) )
      & ( v1_waybel_0(X19,X18)
        | v1_xboole_0(X19)
        | ~ v2_waybel_0(X19,k7_lattice3(X18))
        | ~ v13_waybel_0(X19,k7_lattice3(X18))
        | ~ v2_waybel_7(X19,k7_lattice3(X18))
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(k7_lattice3(X18))))
        | ~ epred1_1(X18) )
      & ( v12_waybel_0(X19,X18)
        | v1_xboole_0(X19)
        | ~ v2_waybel_0(X19,k7_lattice3(X18))
        | ~ v13_waybel_0(X19,k7_lattice3(X18))
        | ~ v2_waybel_7(X19,k7_lattice3(X18))
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(k7_lattice3(X18))))
        | ~ epred1_1(X18) )
      & ( v1_waybel_7(X19,X18)
        | v1_xboole_0(X19)
        | ~ v2_waybel_0(X19,k7_lattice3(X18))
        | ~ v13_waybel_0(X19,k7_lattice3(X18))
        | ~ v2_waybel_7(X19,k7_lattice3(X18))
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(k7_lattice3(X18))))
        | ~ epred1_1(X18) )
      & ( m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | v1_xboole_0(X19)
        | ~ v2_waybel_0(X19,k7_lattice3(X18))
        | ~ v13_waybel_0(X19,k7_lattice3(X18))
        | ~ v2_waybel_7(X19,k7_lattice3(X18))
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(k7_lattice3(X18))))
        | ~ epred1_1(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])])).

cnf(c_0_16,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0)
    | ~ v1_xboole_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_17,axiom,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & v1_lattice3(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1) )
     => epred1_1(X1) ) ),
    inference(apply_def,[status(thm)],[t20_waybel_7,c_0_11])).

fof(c_0_18,plain,(
    ! [X10] :
      ( ( v1_orders_2(k7_lattice3(X10))
        | ~ v1_lattice3(X10)
        | ~ l1_orders_2(X10) )
      & ( v2_lattice3(k7_lattice3(X10))
        | ~ v1_lattice3(X10)
        | ~ l1_orders_2(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc6_yellow_7])])])).

cnf(c_0_19,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X2))))
    | v1_xboole_0(X1)
    | ~ v1_waybel_0(X1,X2)
    | ~ v12_waybel_0(X1,X2)
    | ~ v1_waybel_7(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ epred1_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(esk1_0))))
    | m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(cn,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( v1_waybel_0(esk2_0,k7_lattice3(esk1_0))
    | m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,negated_conjecture,
    ( v12_waybel_0(esk2_0,k7_lattice3(esk1_0))
    | m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,negated_conjecture,
    ( v1_waybel_7(esk2_0,k7_lattice3(esk1_0))
    | m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_25,plain,(
    ! [X14] :
      ( ~ v3_orders_2(X14)
      | ~ v4_orders_2(X14)
      | ~ v5_orders_2(X14)
      | ~ v1_lattice3(X14)
      | ~ v2_lattice3(X14)
      | ~ l1_orders_2(X14)
      | epred1_1(X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])).

cnf(c_0_26,plain,
    ( v2_lattice3(k7_lattice3(X1))
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,negated_conjecture,
    ( v1_lattice3(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_28,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_29,plain,
    ( v2_waybel_0(X1,k7_lattice3(X2))
    | v1_xboole_0(X1)
    | ~ v1_waybel_0(X1,X2)
    | ~ v12_waybel_0(X1,X2)
    | ~ v1_waybel_7(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ epred1_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_30,plain,
    ( v13_waybel_0(X1,k7_lattice3(X2))
    | v1_xboole_0(X1)
    | ~ v1_waybel_0(X1,X2)
    | ~ v12_waybel_0(X1,X2)
    | ~ v1_waybel_7(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ epred1_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_31,plain,
    ( v2_waybel_7(X1,k7_lattice3(X2))
    | v1_xboole_0(X1)
    | ~ v1_waybel_0(X1,X2)
    | ~ v12_waybel_0(X1,X2)
    | ~ v1_waybel_7(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ epred1_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(esk1_0)))))
    | m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ epred1_1(k7_lattice3(esk1_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_22]),c_0_23]),c_0_24])).

cnf(c_0_33,plain,
    ( epred1_1(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,negated_conjecture,
    ( v2_lattice3(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])])).

fof(c_0_35,plain,(
    ! [X9] :
      ( ( v1_orders_2(k7_lattice3(X9))
        | ~ v2_lattice3(X9)
        | ~ l1_orders_2(X9) )
      & ( v1_lattice3(k7_lattice3(X9))
        | ~ v2_lattice3(X9)
        | ~ l1_orders_2(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc5_yellow_7])])])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | v2_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ epred1_1(k7_lattice3(esk1_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_20]),c_0_21]),c_0_22]),c_0_23]),c_0_24])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | v13_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ epred1_1(k7_lattice3(esk1_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_20]),c_0_21]),c_0_22]),c_0_23]),c_0_24])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | v2_waybel_7(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ epred1_1(k7_lattice3(esk1_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_20]),c_0_21]),c_0_22]),c_0_23]),c_0_24])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(esk1_0)))))
    | m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ v1_lattice3(k7_lattice3(esk1_0))
    | ~ v5_orders_2(k7_lattice3(esk1_0))
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])])).

cnf(c_0_40,plain,
    ( v1_lattice3(k7_lattice3(X1))
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( v2_lattice3(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_42,plain,(
    ! [X8] :
      ( ( v1_orders_2(k7_lattice3(X8))
        | ~ v5_orders_2(X8)
        | ~ l1_orders_2(X8) )
      & ( v5_orders_2(k7_lattice3(X8))
        | ~ v5_orders_2(X8)
        | ~ l1_orders_2(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc3_yellow_7])])])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | v2_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v1_lattice3(k7_lattice3(esk1_0))
    | ~ v5_orders_2(k7_lattice3(esk1_0))
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_33]),c_0_34])])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | v13_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v1_lattice3(k7_lattice3(esk1_0))
    | ~ v5_orders_2(k7_lattice3(esk1_0))
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_33]),c_0_34])])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | v2_waybel_7(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v1_lattice3(k7_lattice3(esk1_0))
    | ~ v5_orders_2(k7_lattice3(esk1_0))
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_33]),c_0_34])])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(esk1_0)))))
    | m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ v5_orders_2(k7_lattice3(esk1_0))
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41]),c_0_28])])).

cnf(c_0_47,plain,
    ( v5_orders_2(k7_lattice3(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_48,negated_conjecture,
    ( v5_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_49,plain,(
    ! [X7] :
      ( ( v1_orders_2(k7_lattice3(X7))
        | ~ v4_orders_2(X7)
        | ~ l1_orders_2(X7) )
      & ( v4_orders_2(k7_lattice3(X7))
        | ~ v4_orders_2(X7)
        | ~ l1_orders_2(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc2_yellow_7])])])).

fof(c_0_50,plain,(
    ! [X4] :
      ( ~ l1_orders_2(X4)
      | ~ v1_orders_2(X4)
      | X4 = g1_orders_2(u1_struct_0(X4),u1_orders_2(X4)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_orders_2])])).

fof(c_0_51,plain,(
    ! [X5] :
      ( ( v1_orders_2(k7_lattice3(X5))
        | ~ l1_orders_2(X5) )
      & ( l1_orders_2(k7_lattice3(X5))
        | ~ l1_orders_2(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_lattice3])])])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | v2_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v5_orders_2(k7_lattice3(esk1_0))
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_40]),c_0_41]),c_0_28])])).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | v13_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v5_orders_2(k7_lattice3(esk1_0))
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_40]),c_0_41]),c_0_28])])).

cnf(c_0_54,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | v2_waybel_7(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v5_orders_2(k7_lattice3(esk1_0))
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_40]),c_0_41]),c_0_28])])).

fof(c_0_55,plain,(
    ! [X15] :
      ( ~ l1_orders_2(X15)
      | k7_lattice3(k7_lattice3(X15)) = g1_orders_2(u1_struct_0(X15),u1_orders_2(X15)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_lattice3])])).

cnf(c_0_56,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(esk1_0)))))
    | m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48]),c_0_28])])).

cnf(c_0_57,plain,
    ( v4_orders_2(k7_lattice3(X1))
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_58,negated_conjecture,
    ( v4_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_59,plain,(
    ! [X6] :
      ( ( v1_orders_2(k7_lattice3(X6))
        | ~ v3_orders_2(X6)
        | ~ l1_orders_2(X6) )
      & ( v3_orders_2(k7_lattice3(X6))
        | ~ v3_orders_2(X6)
        | ~ l1_orders_2(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_yellow_7])])])).

cnf(c_0_60,plain,
    ( X1 = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | ~ l1_orders_2(X1)
    | ~ v1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_61,plain,
    ( v1_orders_2(k7_lattice3(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_62,plain,
    ( l1_orders_2(k7_lattice3(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_63,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | v2_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_47]),c_0_48]),c_0_28])])).

cnf(c_0_64,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | v13_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_47]),c_0_48]),c_0_28])])).

cnf(c_0_65,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | v2_waybel_7(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_47]),c_0_48]),c_0_28])])).

cnf(c_0_66,plain,
    ( k7_lattice3(k7_lattice3(X1)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_67,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(esk1_0)))))
    | m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58]),c_0_28])])).

cnf(c_0_68,plain,
    ( v3_orders_2(k7_lattice3(X1))
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_69,negated_conjecture,
    ( v3_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_70,plain,
    ( g1_orders_2(u1_struct_0(k7_lattice3(X1)),u1_orders_2(k7_lattice3(X1))) = k7_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_62])).

cnf(c_0_71,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | v2_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_57]),c_0_58]),c_0_28])])).

cnf(c_0_72,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | v13_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_57]),c_0_58]),c_0_28])])).

cnf(c_0_73,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | v2_waybel_7(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_57]),c_0_58]),c_0_28])])).

cnf(c_0_74,plain,
    ( g1_orders_2(u1_struct_0(k7_lattice3(X1)),u1_orders_2(k7_lattice3(X1))) = k7_lattice3(k7_lattice3(k7_lattice3(X1)))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_66,c_0_62])).

fof(c_0_75,plain,(
    ! [X11,X12,X13] :
      ( ( ~ v1_xboole_0(X13)
        | v1_xboole_0(X13)
        | ~ v2_waybel_0(X13,X11)
        | ~ v13_waybel_0(X13,X11)
        | ~ v2_waybel_7(X13,X11)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X11)))
        | g1_orders_2(u1_struct_0(X11),u1_orders_2(X11)) != g1_orders_2(u1_struct_0(X12),u1_orders_2(X12))
        | ~ v3_orders_2(X12)
        | ~ v4_orders_2(X12)
        | ~ v5_orders_2(X12)
        | ~ v1_lattice3(X12)
        | ~ v2_lattice3(X12)
        | ~ l1_orders_2(X12)
        | ~ v3_orders_2(X11)
        | ~ v4_orders_2(X11)
        | ~ v5_orders_2(X11)
        | ~ v1_lattice3(X11)
        | ~ v2_lattice3(X11)
        | ~ l1_orders_2(X11) )
      & ( v2_waybel_0(X13,X12)
        | v1_xboole_0(X13)
        | ~ v2_waybel_0(X13,X11)
        | ~ v13_waybel_0(X13,X11)
        | ~ v2_waybel_7(X13,X11)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X11)))
        | g1_orders_2(u1_struct_0(X11),u1_orders_2(X11)) != g1_orders_2(u1_struct_0(X12),u1_orders_2(X12))
        | ~ v3_orders_2(X12)
        | ~ v4_orders_2(X12)
        | ~ v5_orders_2(X12)
        | ~ v1_lattice3(X12)
        | ~ v2_lattice3(X12)
        | ~ l1_orders_2(X12)
        | ~ v3_orders_2(X11)
        | ~ v4_orders_2(X11)
        | ~ v5_orders_2(X11)
        | ~ v1_lattice3(X11)
        | ~ v2_lattice3(X11)
        | ~ l1_orders_2(X11) )
      & ( v13_waybel_0(X13,X12)
        | v1_xboole_0(X13)
        | ~ v2_waybel_0(X13,X11)
        | ~ v13_waybel_0(X13,X11)
        | ~ v2_waybel_7(X13,X11)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X11)))
        | g1_orders_2(u1_struct_0(X11),u1_orders_2(X11)) != g1_orders_2(u1_struct_0(X12),u1_orders_2(X12))
        | ~ v3_orders_2(X12)
        | ~ v4_orders_2(X12)
        | ~ v5_orders_2(X12)
        | ~ v1_lattice3(X12)
        | ~ v2_lattice3(X12)
        | ~ l1_orders_2(X12)
        | ~ v3_orders_2(X11)
        | ~ v4_orders_2(X11)
        | ~ v5_orders_2(X11)
        | ~ v1_lattice3(X11)
        | ~ v2_lattice3(X11)
        | ~ l1_orders_2(X11) )
      & ( v2_waybel_7(X13,X12)
        | v1_xboole_0(X13)
        | ~ v2_waybel_0(X13,X11)
        | ~ v13_waybel_0(X13,X11)
        | ~ v2_waybel_7(X13,X11)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X11)))
        | g1_orders_2(u1_struct_0(X11),u1_orders_2(X11)) != g1_orders_2(u1_struct_0(X12),u1_orders_2(X12))
        | ~ v3_orders_2(X12)
        | ~ v4_orders_2(X12)
        | ~ v5_orders_2(X12)
        | ~ v1_lattice3(X12)
        | ~ v2_lattice3(X12)
        | ~ l1_orders_2(X12)
        | ~ v3_orders_2(X11)
        | ~ v4_orders_2(X11)
        | ~ v5_orders_2(X11)
        | ~ v1_lattice3(X11)
        | ~ v2_lattice3(X11)
        | ~ l1_orders_2(X11) )
      & ( m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | v1_xboole_0(X13)
        | ~ v2_waybel_0(X13,X11)
        | ~ v13_waybel_0(X13,X11)
        | ~ v2_waybel_7(X13,X11)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X11)))
        | g1_orders_2(u1_struct_0(X11),u1_orders_2(X11)) != g1_orders_2(u1_struct_0(X12),u1_orders_2(X12))
        | ~ v3_orders_2(X12)
        | ~ v4_orders_2(X12)
        | ~ v5_orders_2(X12)
        | ~ v1_lattice3(X12)
        | ~ v2_lattice3(X12)
        | ~ l1_orders_2(X12)
        | ~ v3_orders_2(X11)
        | ~ v4_orders_2(X11)
        | ~ v5_orders_2(X11)
        | ~ v1_lattice3(X11)
        | ~ v2_lattice3(X11)
        | ~ l1_orders_2(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t19_waybel_7])])])])])).

cnf(c_0_76,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(esk1_0)))))
    | m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_69]),c_0_28])])).

cnf(c_0_77,plain,
    ( g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(X1))),u1_orders_2(k7_lattice3(k7_lattice3(X1)))) = k7_lattice3(k7_lattice3(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_70,c_0_62])).

cnf(c_0_78,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | v2_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_68]),c_0_69]),c_0_28])])).

cnf(c_0_79,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | v13_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_68]),c_0_69]),c_0_28])])).

cnf(c_0_80,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | v2_waybel_7(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_68]),c_0_69]),c_0_28])])).

cnf(c_0_81,negated_conjecture,
    ( g1_orders_2(u1_struct_0(k7_lattice3(esk1_0)),u1_orders_2(k7_lattice3(esk1_0))) = k7_lattice3(k7_lattice3(k7_lattice3(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_74,c_0_28])).

cnf(c_0_82,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | v1_xboole_0(X1)
    | ~ v2_waybel_0(X1,X3)
    | ~ v13_waybel_0(X1,X3)
    | ~ v2_waybel_7(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X3)))
    | g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ v1_lattice3(X2)
    | ~ v2_lattice3(X2)
    | ~ l1_orders_2(X2)
    | ~ v3_orders_2(X3)
    | ~ v4_orders_2(X3)
    | ~ v5_orders_2(X3)
    | ~ v1_lattice3(X3)
    | ~ v2_lattice3(X3)
    | ~ l1_orders_2(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_83,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(esk1_0)))))
    | m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_62]),c_0_28])])).

cnf(c_0_84,negated_conjecture,
    ( g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(esk1_0))),u1_orders_2(k7_lattice3(k7_lattice3(esk1_0)))) = k7_lattice3(k7_lattice3(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_77,c_0_28])).

cnf(c_0_85,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | v2_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_62]),c_0_28])])).

cnf(c_0_86,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | v13_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_62]),c_0_28])])).

cnf(c_0_87,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | v2_waybel_7(esk2_0,k7_lattice3(k7_lattice3(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_62]),c_0_28])])).

cnf(c_0_88,negated_conjecture,
    ( k7_lattice3(k7_lattice3(k7_lattice3(esk1_0))) = k7_lattice3(esk1_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_28]),c_0_81])).

cnf(c_0_89,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(X1)))
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != k7_lattice3(k7_lattice3(esk1_0))
    | ~ v1_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v2_lattice3(X1)
    | ~ v5_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_21]),c_0_84]),c_0_85]),c_0_86]),c_0_87])).

cnf(c_0_90,negated_conjecture,
    ( l1_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(k7_lattice3(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_62,c_0_88])).

cnf(c_0_91,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(X1)))
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != k7_lattice3(k7_lattice3(esk1_0))
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v2_lattice3(X1)
    | ~ v5_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_40]),c_0_34])]),c_0_90])).

cnf(c_0_92,plain,
    ( v2_lattice3(k7_lattice3(k7_lattice3(X1)))
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_40]),c_0_62])).

cnf(c_0_93,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(X1)))
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != k7_lattice3(k7_lattice3(esk1_0))
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ v5_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ l1_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_41]),c_0_28])])).

cnf(c_0_94,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(X1)))
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != k7_lattice3(k7_lattice3(esk1_0))
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ v5_orders_2(k7_lattice3(esk1_0))
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_47]),c_0_90])).

cnf(c_0_95,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(X1)))
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != k7_lattice3(k7_lattice3(esk1_0))
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ l1_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_47]),c_0_48]),c_0_28])])).

cnf(c_0_96,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(X1)))
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != k7_lattice3(k7_lattice3(esk1_0))
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_57]),c_0_90])).

cnf(c_0_97,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(X1)))
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != k7_lattice3(k7_lattice3(esk1_0))
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ l1_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_57]),c_0_58]),c_0_28])])).

cnf(c_0_98,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(X1)))
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != k7_lattice3(k7_lattice3(esk1_0))
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_68]),c_0_90])).

cnf(c_0_99,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(X1)))
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != k7_lattice3(k7_lattice3(esk1_0))
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ l1_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_68]),c_0_69]),c_0_28])])).

cnf(c_0_100,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(X1)))
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != k7_lattice3(k7_lattice3(esk1_0))
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_99,c_0_62])).

cnf(c_0_101,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(X1)))
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != k7_lattice3(k7_lattice3(esk1_0))
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_62]),c_0_28])])).

cnf(c_0_102,negated_conjecture,
    ( g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0)) = k7_lattice3(k7_lattice3(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_28])).

cnf(c_0_103,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_102]),c_0_27]),c_0_41]),c_0_48]),c_0_58]),c_0_69]),c_0_28])])).

cnf(c_0_104,plain,
    ( v2_waybel_0(X1,X2)
    | v1_xboole_0(X1)
    | ~ v2_waybel_0(X1,X3)
    | ~ v13_waybel_0(X1,X3)
    | ~ v2_waybel_7(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X3)))
    | g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ v1_lattice3(X2)
    | ~ v2_lattice3(X2)
    | ~ l1_orders_2(X2)
    | ~ v3_orders_2(X3)
    | ~ v4_orders_2(X3)
    | ~ v5_orders_2(X3)
    | ~ v1_lattice3(X3)
    | ~ v2_lattice3(X3)
    | ~ l1_orders_2(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_105,plain,
    ( v13_waybel_0(X1,X2)
    | v1_xboole_0(X1)
    | ~ v2_waybel_0(X1,X3)
    | ~ v13_waybel_0(X1,X3)
    | ~ v2_waybel_7(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X3)))
    | g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ v1_lattice3(X2)
    | ~ v2_lattice3(X2)
    | ~ l1_orders_2(X2)
    | ~ v3_orders_2(X3)
    | ~ v4_orders_2(X3)
    | ~ v5_orders_2(X3)
    | ~ v1_lattice3(X3)
    | ~ v2_lattice3(X3)
    | ~ l1_orders_2(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_106,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(X1)))
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != k7_lattice3(k7_lattice3(esk1_0))
    | ~ v2_waybel_7(esk2_0,esk1_0)
    | ~ v13_waybel_0(esk2_0,esk1_0)
    | ~ v2_waybel_0(esk2_0,esk1_0)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_103]),c_0_102]),c_0_27]),c_0_41]),c_0_48]),c_0_58]),c_0_69]),c_0_28])]),c_0_21])).

cnf(c_0_107,negated_conjecture,
    ( v2_waybel_0(esk2_0,X1)
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != k7_lattice3(k7_lattice3(esk1_0))
    | ~ v2_waybel_7(esk2_0,esk1_0)
    | ~ v13_waybel_0(esk2_0,esk1_0)
    | ~ v2_waybel_0(esk2_0,esk1_0)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_103]),c_0_102]),c_0_27]),c_0_41]),c_0_48]),c_0_58]),c_0_69]),c_0_28])]),c_0_21])).

cnf(c_0_108,negated_conjecture,
    ( v13_waybel_0(esk2_0,X1)
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != k7_lattice3(k7_lattice3(esk1_0))
    | ~ v2_waybel_7(esk2_0,esk1_0)
    | ~ v13_waybel_0(esk2_0,esk1_0)
    | ~ v2_waybel_0(esk2_0,esk1_0)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_103]),c_0_102]),c_0_27]),c_0_41]),c_0_48]),c_0_58]),c_0_69]),c_0_28])]),c_0_21])).

cnf(c_0_109,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(X1))))
    | g1_orders_2(u1_struct_0(k7_lattice3(X1)),u1_orders_2(k7_lattice3(X1))) != k7_lattice3(k7_lattice3(esk1_0))
    | ~ v2_waybel_7(esk2_0,esk1_0)
    | ~ v13_waybel_0(esk2_0,esk1_0)
    | ~ v2_waybel_0(esk2_0,esk1_0)
    | ~ v2_lattice3(k7_lattice3(X1))
    | ~ v2_lattice3(X1)
    | ~ v5_orders_2(k7_lattice3(X1))
    | ~ v4_orders_2(k7_lattice3(X1))
    | ~ v3_orders_2(k7_lattice3(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_40]),c_0_62])).

cnf(c_0_110,negated_conjecture,
    ( v2_waybel_0(esk2_0,k7_lattice3(X1))
    | g1_orders_2(u1_struct_0(k7_lattice3(X1)),u1_orders_2(k7_lattice3(X1))) != k7_lattice3(k7_lattice3(esk1_0))
    | ~ v2_waybel_7(esk2_0,esk1_0)
    | ~ v13_waybel_0(esk2_0,esk1_0)
    | ~ v2_waybel_0(esk2_0,esk1_0)
    | ~ v2_lattice3(k7_lattice3(X1))
    | ~ v2_lattice3(X1)
    | ~ v5_orders_2(k7_lattice3(X1))
    | ~ v4_orders_2(k7_lattice3(X1))
    | ~ v3_orders_2(k7_lattice3(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_40]),c_0_62])).

cnf(c_0_111,negated_conjecture,
    ( v13_waybel_0(esk2_0,k7_lattice3(X1))
    | g1_orders_2(u1_struct_0(k7_lattice3(X1)),u1_orders_2(k7_lattice3(X1))) != k7_lattice3(k7_lattice3(esk1_0))
    | ~ v2_waybel_7(esk2_0,esk1_0)
    | ~ v13_waybel_0(esk2_0,esk1_0)
    | ~ v2_waybel_0(esk2_0,esk1_0)
    | ~ v2_lattice3(k7_lattice3(X1))
    | ~ v2_lattice3(X1)
    | ~ v5_orders_2(k7_lattice3(X1))
    | ~ v4_orders_2(k7_lattice3(X1))
    | ~ v3_orders_2(k7_lattice3(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_40]),c_0_62])).

cnf(c_0_112,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(X1)))))
    | g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(X1))),u1_orders_2(k7_lattice3(k7_lattice3(X1)))) != k7_lattice3(k7_lattice3(esk1_0))
    | ~ v2_waybel_7(esk2_0,esk1_0)
    | ~ v13_waybel_0(esk2_0,esk1_0)
    | ~ v2_waybel_0(esk2_0,esk1_0)
    | ~ v2_lattice3(k7_lattice3(X1))
    | ~ v2_lattice3(X1)
    | ~ v5_orders_2(k7_lattice3(k7_lattice3(X1)))
    | ~ v4_orders_2(k7_lattice3(k7_lattice3(X1)))
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(X1)))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_92]),c_0_62])).

cnf(c_0_113,negated_conjecture,
    ( v2_waybel_0(esk2_0,k7_lattice3(k7_lattice3(X1)))
    | g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(X1))),u1_orders_2(k7_lattice3(k7_lattice3(X1)))) != k7_lattice3(k7_lattice3(esk1_0))
    | ~ v2_waybel_7(esk2_0,esk1_0)
    | ~ v13_waybel_0(esk2_0,esk1_0)
    | ~ v2_waybel_0(esk2_0,esk1_0)
    | ~ v2_lattice3(k7_lattice3(X1))
    | ~ v2_lattice3(X1)
    | ~ v5_orders_2(k7_lattice3(k7_lattice3(X1)))
    | ~ v4_orders_2(k7_lattice3(k7_lattice3(X1)))
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(X1)))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_92]),c_0_62])).

cnf(c_0_114,negated_conjecture,
    ( v13_waybel_0(esk2_0,k7_lattice3(k7_lattice3(X1)))
    | g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(X1))),u1_orders_2(k7_lattice3(k7_lattice3(X1)))) != k7_lattice3(k7_lattice3(esk1_0))
    | ~ v2_waybel_7(esk2_0,esk1_0)
    | ~ v13_waybel_0(esk2_0,esk1_0)
    | ~ v2_waybel_0(esk2_0,esk1_0)
    | ~ v2_lattice3(k7_lattice3(X1))
    | ~ v2_lattice3(X1)
    | ~ v5_orders_2(k7_lattice3(k7_lattice3(X1)))
    | ~ v4_orders_2(k7_lattice3(k7_lattice3(X1)))
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(X1)))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_92]),c_0_62])).

cnf(c_0_115,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(esk1_0)))))
    | ~ v2_waybel_7(esk2_0,esk1_0)
    | ~ v13_waybel_0(esk2_0,esk1_0)
    | ~ v2_waybel_0(esk2_0,esk1_0)
    | ~ v5_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v4_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_34]),c_0_84]),c_0_41]),c_0_28])])).

cnf(c_0_116,negated_conjecture,
    ( v2_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v2_waybel_7(esk2_0,esk1_0)
    | ~ v13_waybel_0(esk2_0,esk1_0)
    | ~ v2_waybel_0(esk2_0,esk1_0)
    | ~ v5_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v4_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_34]),c_0_84]),c_0_41]),c_0_28])])).

cnf(c_0_117,negated_conjecture,
    ( v13_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v2_waybel_7(esk2_0,esk1_0)
    | ~ v13_waybel_0(esk2_0,esk1_0)
    | ~ v2_waybel_0(esk2_0,esk1_0)
    | ~ v5_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v4_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_34]),c_0_84]),c_0_41]),c_0_28])])).

cnf(c_0_118,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(esk1_0)))))
    | ~ v2_waybel_7(esk2_0,esk1_0)
    | ~ v13_waybel_0(esk2_0,esk1_0)
    | ~ v2_waybel_0(esk2_0,esk1_0)
    | ~ v5_orders_2(k7_lattice3(esk1_0))
    | ~ v4_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_115,c_0_47])).

cnf(c_0_119,negated_conjecture,
    ( v2_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v2_waybel_7(esk2_0,esk1_0)
    | ~ v13_waybel_0(esk2_0,esk1_0)
    | ~ v2_waybel_0(esk2_0,esk1_0)
    | ~ v5_orders_2(k7_lattice3(esk1_0))
    | ~ v4_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_116,c_0_47])).

cnf(c_0_120,negated_conjecture,
    ( v13_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v2_waybel_7(esk2_0,esk1_0)
    | ~ v13_waybel_0(esk2_0,esk1_0)
    | ~ v2_waybel_0(esk2_0,esk1_0)
    | ~ v5_orders_2(k7_lattice3(esk1_0))
    | ~ v4_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_117,c_0_47])).

cnf(c_0_121,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(esk1_0)))))
    | ~ v2_waybel_7(esk2_0,esk1_0)
    | ~ v13_waybel_0(esk2_0,esk1_0)
    | ~ v2_waybel_0(esk2_0,esk1_0)
    | ~ v4_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118,c_0_47]),c_0_48]),c_0_28])])).

cnf(c_0_122,negated_conjecture,
    ( v2_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v2_waybel_7(esk2_0,esk1_0)
    | ~ v13_waybel_0(esk2_0,esk1_0)
    | ~ v2_waybel_0(esk2_0,esk1_0)
    | ~ v4_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_47]),c_0_48]),c_0_28])])).

cnf(c_0_123,negated_conjecture,
    ( v13_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v2_waybel_7(esk2_0,esk1_0)
    | ~ v13_waybel_0(esk2_0,esk1_0)
    | ~ v2_waybel_0(esk2_0,esk1_0)
    | ~ v4_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_47]),c_0_48]),c_0_28])])).

cnf(c_0_124,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(esk1_0)))))
    | ~ v2_waybel_7(esk2_0,esk1_0)
    | ~ v13_waybel_0(esk2_0,esk1_0)
    | ~ v2_waybel_0(esk2_0,esk1_0)
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_121,c_0_57])).

cnf(c_0_125,negated_conjecture,
    ( v2_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v2_waybel_7(esk2_0,esk1_0)
    | ~ v13_waybel_0(esk2_0,esk1_0)
    | ~ v2_waybel_0(esk2_0,esk1_0)
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_122,c_0_57])).

cnf(c_0_126,negated_conjecture,
    ( v13_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v2_waybel_7(esk2_0,esk1_0)
    | ~ v13_waybel_0(esk2_0,esk1_0)
    | ~ v2_waybel_0(esk2_0,esk1_0)
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_123,c_0_57])).

cnf(c_0_127,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(esk1_0)))))
    | ~ v2_waybel_7(esk2_0,esk1_0)
    | ~ v13_waybel_0(esk2_0,esk1_0)
    | ~ v2_waybel_0(esk2_0,esk1_0)
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_57]),c_0_58]),c_0_28])])).

cnf(c_0_128,negated_conjecture,
    ( v2_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v2_waybel_7(esk2_0,esk1_0)
    | ~ v13_waybel_0(esk2_0,esk1_0)
    | ~ v2_waybel_0(esk2_0,esk1_0)
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125,c_0_57]),c_0_58]),c_0_28])])).

cnf(c_0_129,negated_conjecture,
    ( v13_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v2_waybel_7(esk2_0,esk1_0)
    | ~ v13_waybel_0(esk2_0,esk1_0)
    | ~ v2_waybel_0(esk2_0,esk1_0)
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126,c_0_57]),c_0_58]),c_0_28])])).

cnf(c_0_130,plain,
    ( v2_waybel_7(X1,X2)
    | v1_xboole_0(X1)
    | ~ v2_waybel_0(X1,X3)
    | ~ v13_waybel_0(X1,X3)
    | ~ v2_waybel_7(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X3)))
    | g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ v1_lattice3(X2)
    | ~ v2_lattice3(X2)
    | ~ l1_orders_2(X2)
    | ~ v3_orders_2(X3)
    | ~ v4_orders_2(X3)
    | ~ v5_orders_2(X3)
    | ~ v1_lattice3(X3)
    | ~ v2_lattice3(X3)
    | ~ l1_orders_2(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_131,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(esk1_0)))))
    | ~ v2_waybel_7(esk2_0,esk1_0)
    | ~ v13_waybel_0(esk2_0,esk1_0)
    | ~ v2_waybel_0(esk2_0,esk1_0)
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_127,c_0_68])).

cnf(c_0_132,negated_conjecture,
    ( v2_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v2_waybel_7(esk2_0,esk1_0)
    | ~ v13_waybel_0(esk2_0,esk1_0)
    | ~ v2_waybel_0(esk2_0,esk1_0)
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_128,c_0_68])).

cnf(c_0_133,negated_conjecture,
    ( v13_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v2_waybel_7(esk2_0,esk1_0)
    | ~ v13_waybel_0(esk2_0,esk1_0)
    | ~ v2_waybel_0(esk2_0,esk1_0)
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_129,c_0_68])).

cnf(c_0_134,negated_conjecture,
    ( v2_waybel_7(esk2_0,X1)
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != k7_lattice3(k7_lattice3(esk1_0))
    | ~ v2_waybel_7(esk2_0,esk1_0)
    | ~ v13_waybel_0(esk2_0,esk1_0)
    | ~ v2_waybel_0(esk2_0,esk1_0)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_130,c_0_103]),c_0_102]),c_0_27]),c_0_41]),c_0_48]),c_0_58]),c_0_69]),c_0_28])]),c_0_21])).

cnf(c_0_135,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(esk1_0)))))
    | ~ v2_waybel_7(esk2_0,esk1_0)
    | ~ v13_waybel_0(esk2_0,esk1_0)
    | ~ v2_waybel_0(esk2_0,esk1_0)
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131,c_0_68]),c_0_69]),c_0_28])])).

cnf(c_0_136,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(esk1_0))))
    | v2_waybel_7(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_137,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(esk1_0))))
    | v2_waybel_0(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_138,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(esk1_0))))
    | v13_waybel_0(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_139,negated_conjecture,
    ( v2_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v2_waybel_7(esk2_0,esk1_0)
    | ~ v13_waybel_0(esk2_0,esk1_0)
    | ~ v2_waybel_0(esk2_0,esk1_0)
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132,c_0_68]),c_0_69]),c_0_28])])).

cnf(c_0_140,negated_conjecture,
    ( v13_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v2_waybel_7(esk2_0,esk1_0)
    | ~ v13_waybel_0(esk2_0,esk1_0)
    | ~ v2_waybel_0(esk2_0,esk1_0)
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_133,c_0_68]),c_0_69]),c_0_28])])).

cnf(c_0_141,negated_conjecture,
    ( v2_waybel_7(esk2_0,k7_lattice3(X1))
    | g1_orders_2(u1_struct_0(k7_lattice3(X1)),u1_orders_2(k7_lattice3(X1))) != k7_lattice3(k7_lattice3(esk1_0))
    | ~ v2_waybel_7(esk2_0,esk1_0)
    | ~ v13_waybel_0(esk2_0,esk1_0)
    | ~ v2_waybel_0(esk2_0,esk1_0)
    | ~ v2_lattice3(k7_lattice3(X1))
    | ~ v2_lattice3(X1)
    | ~ v5_orders_2(k7_lattice3(X1))
    | ~ v4_orders_2(k7_lattice3(X1))
    | ~ v3_orders_2(k7_lattice3(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_134,c_0_40]),c_0_62])).

cnf(c_0_142,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(esk1_0)))))
    | m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(esk1_0))))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_136]),c_0_137]),c_0_138])).

cnf(c_0_143,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(esk1_0))))
    | v2_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_139,c_0_136]),c_0_137]),c_0_138])).

cnf(c_0_144,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(esk1_0))))
    | v13_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_140,c_0_136]),c_0_137]),c_0_138])).

cnf(c_0_145,negated_conjecture,
    ( v2_waybel_7(esk2_0,k7_lattice3(k7_lattice3(X1)))
    | g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(X1))),u1_orders_2(k7_lattice3(k7_lattice3(X1)))) != k7_lattice3(k7_lattice3(esk1_0))
    | ~ v2_waybel_7(esk2_0,esk1_0)
    | ~ v13_waybel_0(esk2_0,esk1_0)
    | ~ v2_waybel_0(esk2_0,esk1_0)
    | ~ v2_lattice3(k7_lattice3(X1))
    | ~ v2_lattice3(X1)
    | ~ v5_orders_2(k7_lattice3(k7_lattice3(X1)))
    | ~ v4_orders_2(k7_lattice3(k7_lattice3(X1)))
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(X1)))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_141,c_0_92]),c_0_62])).

cnf(c_0_146,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | v1_xboole_0(X1)
    | ~ v2_waybel_0(X1,k7_lattice3(X2))
    | ~ v13_waybel_0(X1,k7_lattice3(X2))
    | ~ v2_waybel_7(X1,k7_lattice3(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X2))))
    | ~ epred1_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_147,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(esk1_0)))))
    | m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(esk1_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_142,c_0_62]),c_0_28])])).

cnf(c_0_148,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(esk1_0))))
    | v2_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_143,c_0_62]),c_0_28])])).

cnf(c_0_149,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(esk1_0))))
    | v13_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_144,c_0_62]),c_0_28])])).

cnf(c_0_150,negated_conjecture,
    ( v2_waybel_7(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v2_waybel_7(esk2_0,esk1_0)
    | ~ v13_waybel_0(esk2_0,esk1_0)
    | ~ v2_waybel_0(esk2_0,esk1_0)
    | ~ v5_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v4_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_145,c_0_34]),c_0_84]),c_0_41]),c_0_28])])).

cnf(c_0_151,plain,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(esk1_0))))
    | ~ epred1_1(k7_lattice3(esk1_0))
    | ~ v2_waybel_7(esk2_0,k7_lattice3(k7_lattice3(esk1_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_146,c_0_147]),c_0_21]),c_0_148]),c_0_149])).

cnf(c_0_152,negated_conjecture,
    ( v2_waybel_7(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v2_waybel_7(esk2_0,esk1_0)
    | ~ v13_waybel_0(esk2_0,esk1_0)
    | ~ v2_waybel_0(esk2_0,esk1_0)
    | ~ v5_orders_2(k7_lattice3(esk1_0))
    | ~ v4_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_150,c_0_47])).

cnf(c_0_153,plain,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(esk1_0))))
    | ~ v2_waybel_7(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v1_lattice3(k7_lattice3(esk1_0))
    | ~ v5_orders_2(k7_lattice3(esk1_0))
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_151,c_0_33]),c_0_34])])).

cnf(c_0_154,negated_conjecture,
    ( v2_waybel_7(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v2_waybel_7(esk2_0,esk1_0)
    | ~ v13_waybel_0(esk2_0,esk1_0)
    | ~ v2_waybel_0(esk2_0,esk1_0)
    | ~ v4_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_152,c_0_47]),c_0_48]),c_0_28])])).

cnf(c_0_155,plain,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(esk1_0))))
    | ~ v2_waybel_7(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v5_orders_2(k7_lattice3(esk1_0))
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_153,c_0_40]),c_0_41]),c_0_28])])).

cnf(c_0_156,negated_conjecture,
    ( v2_waybel_7(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v2_waybel_7(esk2_0,esk1_0)
    | ~ v13_waybel_0(esk2_0,esk1_0)
    | ~ v2_waybel_0(esk2_0,esk1_0)
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_154,c_0_57])).

cnf(c_0_157,plain,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(esk1_0))))
    | ~ v2_waybel_7(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_155,c_0_47]),c_0_48]),c_0_28])])).

cnf(c_0_158,negated_conjecture,
    ( v2_waybel_7(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v2_waybel_7(esk2_0,esk1_0)
    | ~ v13_waybel_0(esk2_0,esk1_0)
    | ~ v2_waybel_0(esk2_0,esk1_0)
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_156,c_0_57]),c_0_58]),c_0_28])])).

cnf(c_0_159,plain,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(esk1_0))))
    | ~ v2_waybel_7(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_157,c_0_57]),c_0_58]),c_0_28])])).

cnf(c_0_160,negated_conjecture,
    ( v2_waybel_7(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v2_waybel_7(esk2_0,esk1_0)
    | ~ v13_waybel_0(esk2_0,esk1_0)
    | ~ v2_waybel_0(esk2_0,esk1_0)
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_158,c_0_68])).

cnf(c_0_161,plain,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(esk1_0))))
    | ~ v2_waybel_7(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_159,c_0_68]),c_0_69]),c_0_28])])).

cnf(c_0_162,negated_conjecture,
    ( v2_waybel_7(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v2_waybel_7(esk2_0,esk1_0)
    | ~ v13_waybel_0(esk2_0,esk1_0)
    | ~ v2_waybel_0(esk2_0,esk1_0)
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_160,c_0_68]),c_0_69]),c_0_28])])).

cnf(c_0_163,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(esk1_0))))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_161,c_0_162]),c_0_137]),c_0_138]),c_0_136])).

cnf(c_0_164,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(esk1_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_163,c_0_62]),c_0_28])])).

cnf(c_0_165,plain,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(esk1_0)))))
    | ~ epred1_1(k7_lattice3(esk1_0))
    | ~ v1_waybel_7(esk2_0,k7_lattice3(esk1_0))
    | ~ v12_waybel_0(esk2_0,k7_lattice3(esk1_0))
    | ~ v1_waybel_0(esk2_0,k7_lattice3(esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_164]),c_0_21])).

cnf(c_0_166,plain,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(esk1_0)))))
    | ~ v1_waybel_7(esk2_0,k7_lattice3(esk1_0))
    | ~ v12_waybel_0(esk2_0,k7_lattice3(esk1_0))
    | ~ v1_waybel_0(esk2_0,k7_lattice3(esk1_0))
    | ~ v1_lattice3(k7_lattice3(esk1_0))
    | ~ v5_orders_2(k7_lattice3(esk1_0))
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_165,c_0_33]),c_0_34])])).

cnf(c_0_167,negated_conjecture,
    ( v1_waybel_7(esk2_0,k7_lattice3(esk1_0))
    | v2_waybel_7(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_168,negated_conjecture,
    ( v1_waybel_0(esk2_0,k7_lattice3(esk1_0))
    | v2_waybel_7(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_169,negated_conjecture,
    ( v12_waybel_0(esk2_0,k7_lattice3(esk1_0))
    | v2_waybel_7(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_170,negated_conjecture,
    ( v1_waybel_7(esk2_0,k7_lattice3(esk1_0))
    | v2_waybel_0(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_171,negated_conjecture,
    ( v1_waybel_0(esk2_0,k7_lattice3(esk1_0))
    | v2_waybel_0(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_172,negated_conjecture,
    ( v12_waybel_0(esk2_0,k7_lattice3(esk1_0))
    | v2_waybel_0(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_173,negated_conjecture,
    ( v1_waybel_7(esk2_0,k7_lattice3(esk1_0))
    | v13_waybel_0(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_174,negated_conjecture,
    ( v1_waybel_0(esk2_0,k7_lattice3(esk1_0))
    | v13_waybel_0(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_175,negated_conjecture,
    ( v12_waybel_0(esk2_0,k7_lattice3(esk1_0))
    | v13_waybel_0(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_176,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(esk1_0)))))
    | v2_waybel_7(esk2_0,esk1_0)
    | ~ v1_lattice3(k7_lattice3(esk1_0))
    | ~ v5_orders_2(k7_lattice3(esk1_0))
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_166,c_0_167]),c_0_168]),c_0_169])).

cnf(c_0_177,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(esk1_0)))))
    | v2_waybel_0(esk2_0,esk1_0)
    | ~ v1_lattice3(k7_lattice3(esk1_0))
    | ~ v5_orders_2(k7_lattice3(esk1_0))
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_166,c_0_170]),c_0_171]),c_0_172])).

cnf(c_0_178,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(esk1_0)))))
    | v13_waybel_0(esk2_0,esk1_0)
    | ~ v1_lattice3(k7_lattice3(esk1_0))
    | ~ v5_orders_2(k7_lattice3(esk1_0))
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_166,c_0_173]),c_0_174]),c_0_175])).

cnf(c_0_179,plain,
    ( v2_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ epred1_1(k7_lattice3(esk1_0))
    | ~ v1_waybel_7(esk2_0,k7_lattice3(esk1_0))
    | ~ v12_waybel_0(esk2_0,k7_lattice3(esk1_0))
    | ~ v1_waybel_0(esk2_0,k7_lattice3(esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_164]),c_0_21])).

cnf(c_0_180,plain,
    ( v13_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ epred1_1(k7_lattice3(esk1_0))
    | ~ v1_waybel_7(esk2_0,k7_lattice3(esk1_0))
    | ~ v12_waybel_0(esk2_0,k7_lattice3(esk1_0))
    | ~ v1_waybel_0(esk2_0,k7_lattice3(esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_164]),c_0_21])).

cnf(c_0_181,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(esk1_0)))))
    | v2_waybel_7(esk2_0,esk1_0)
    | ~ v5_orders_2(k7_lattice3(esk1_0))
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_176,c_0_40]),c_0_41]),c_0_28])])).

cnf(c_0_182,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(esk1_0)))))
    | v2_waybel_0(esk2_0,esk1_0)
    | ~ v5_orders_2(k7_lattice3(esk1_0))
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_177,c_0_40]),c_0_41]),c_0_28])])).

cnf(c_0_183,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(esk1_0)))))
    | v13_waybel_0(esk2_0,esk1_0)
    | ~ v5_orders_2(k7_lattice3(esk1_0))
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_178,c_0_40]),c_0_41]),c_0_28])])).

cnf(c_0_184,plain,
    ( v2_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v1_waybel_7(esk2_0,k7_lattice3(esk1_0))
    | ~ v12_waybel_0(esk2_0,k7_lattice3(esk1_0))
    | ~ v1_waybel_0(esk2_0,k7_lattice3(esk1_0))
    | ~ v1_lattice3(k7_lattice3(esk1_0))
    | ~ v5_orders_2(k7_lattice3(esk1_0))
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_179,c_0_33]),c_0_34])])).

cnf(c_0_185,plain,
    ( v13_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v1_waybel_7(esk2_0,k7_lattice3(esk1_0))
    | ~ v12_waybel_0(esk2_0,k7_lattice3(esk1_0))
    | ~ v1_waybel_0(esk2_0,k7_lattice3(esk1_0))
    | ~ v1_lattice3(k7_lattice3(esk1_0))
    | ~ v5_orders_2(k7_lattice3(esk1_0))
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_180,c_0_33]),c_0_34])])).

cnf(c_0_186,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(esk1_0)))))
    | v2_waybel_7(esk2_0,esk1_0)
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_181,c_0_47]),c_0_48]),c_0_28])])).

cnf(c_0_187,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(esk1_0)))))
    | v2_waybel_0(esk2_0,esk1_0)
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_182,c_0_47]),c_0_48]),c_0_28])])).

cnf(c_0_188,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(esk1_0)))))
    | v13_waybel_0(esk2_0,esk1_0)
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_183,c_0_47]),c_0_48]),c_0_28])])).

cnf(c_0_189,plain,
    ( v2_waybel_7(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ epred1_1(k7_lattice3(esk1_0))
    | ~ v1_waybel_7(esk2_0,k7_lattice3(esk1_0))
    | ~ v12_waybel_0(esk2_0,k7_lattice3(esk1_0))
    | ~ v1_waybel_0(esk2_0,k7_lattice3(esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_164]),c_0_21])).

cnf(c_0_190,negated_conjecture,
    ( v2_waybel_7(esk2_0,esk1_0)
    | v2_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v1_lattice3(k7_lattice3(esk1_0))
    | ~ v5_orders_2(k7_lattice3(esk1_0))
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_184,c_0_167]),c_0_168]),c_0_169])).

cnf(c_0_191,negated_conjecture,
    ( v2_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | v2_waybel_0(esk2_0,esk1_0)
    | ~ v1_lattice3(k7_lattice3(esk1_0))
    | ~ v5_orders_2(k7_lattice3(esk1_0))
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_184,c_0_170]),c_0_171]),c_0_172])).

cnf(c_0_192,negated_conjecture,
    ( v13_waybel_0(esk2_0,esk1_0)
    | v2_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v1_lattice3(k7_lattice3(esk1_0))
    | ~ v5_orders_2(k7_lattice3(esk1_0))
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_184,c_0_173]),c_0_174]),c_0_175])).

cnf(c_0_193,negated_conjecture,
    ( v2_waybel_7(esk2_0,esk1_0)
    | v13_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v1_lattice3(k7_lattice3(esk1_0))
    | ~ v5_orders_2(k7_lattice3(esk1_0))
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_185,c_0_167]),c_0_168]),c_0_169])).

cnf(c_0_194,negated_conjecture,
    ( v13_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | v2_waybel_0(esk2_0,esk1_0)
    | ~ v1_lattice3(k7_lattice3(esk1_0))
    | ~ v5_orders_2(k7_lattice3(esk1_0))
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_185,c_0_170]),c_0_171]),c_0_172])).

cnf(c_0_195,negated_conjecture,
    ( v13_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | v13_waybel_0(esk2_0,esk1_0)
    | ~ v1_lattice3(k7_lattice3(esk1_0))
    | ~ v5_orders_2(k7_lattice3(esk1_0))
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_185,c_0_173]),c_0_174]),c_0_175])).

cnf(c_0_196,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(esk1_0)))))
    | v2_waybel_7(esk2_0,esk1_0)
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_186,c_0_57]),c_0_58]),c_0_28])])).

cnf(c_0_197,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(esk1_0)))))
    | v2_waybel_0(esk2_0,esk1_0)
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_187,c_0_57]),c_0_58]),c_0_28])])).

cnf(c_0_198,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(esk1_0)))))
    | v13_waybel_0(esk2_0,esk1_0)
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_188,c_0_57]),c_0_58]),c_0_28])])).

cnf(c_0_199,plain,
    ( v2_waybel_7(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v1_waybel_7(esk2_0,k7_lattice3(esk1_0))
    | ~ v12_waybel_0(esk2_0,k7_lattice3(esk1_0))
    | ~ v1_waybel_0(esk2_0,k7_lattice3(esk1_0))
    | ~ v1_lattice3(k7_lattice3(esk1_0))
    | ~ v5_orders_2(k7_lattice3(esk1_0))
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_189,c_0_33]),c_0_34])])).

cnf(c_0_200,negated_conjecture,
    ( v2_waybel_7(esk2_0,esk1_0)
    | v2_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v5_orders_2(k7_lattice3(esk1_0))
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_190,c_0_40]),c_0_41]),c_0_28])])).

cnf(c_0_201,negated_conjecture,
    ( v2_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | v2_waybel_0(esk2_0,esk1_0)
    | ~ v5_orders_2(k7_lattice3(esk1_0))
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_191,c_0_40]),c_0_41]),c_0_28])])).

cnf(c_0_202,negated_conjecture,
    ( v13_waybel_0(esk2_0,esk1_0)
    | v2_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v5_orders_2(k7_lattice3(esk1_0))
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_192,c_0_40]),c_0_41]),c_0_28])])).

cnf(c_0_203,negated_conjecture,
    ( v2_waybel_7(esk2_0,esk1_0)
    | v13_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v5_orders_2(k7_lattice3(esk1_0))
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_193,c_0_40]),c_0_41]),c_0_28])])).

cnf(c_0_204,negated_conjecture,
    ( v13_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | v2_waybel_0(esk2_0,esk1_0)
    | ~ v5_orders_2(k7_lattice3(esk1_0))
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_194,c_0_40]),c_0_41]),c_0_28])])).

cnf(c_0_205,negated_conjecture,
    ( v13_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | v13_waybel_0(esk2_0,esk1_0)
    | ~ v5_orders_2(k7_lattice3(esk1_0))
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_195,c_0_40]),c_0_41]),c_0_28])])).

cnf(c_0_206,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(esk1_0)))))
    | v2_waybel_7(esk2_0,esk1_0)
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_196,c_0_68]),c_0_69]),c_0_28])])).

cnf(c_0_207,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(esk1_0)))))
    | v2_waybel_0(esk2_0,esk1_0)
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_197,c_0_68]),c_0_69]),c_0_28])])).

cnf(c_0_208,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(esk1_0)))))
    | v13_waybel_0(esk2_0,esk1_0)
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_198,c_0_68]),c_0_69]),c_0_28])])).

cnf(c_0_209,negated_conjecture,
    ( v2_waybel_7(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | v2_waybel_7(esk2_0,esk1_0)
    | ~ v1_lattice3(k7_lattice3(esk1_0))
    | ~ v5_orders_2(k7_lattice3(esk1_0))
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_199,c_0_167]),c_0_168]),c_0_169])).

cnf(c_0_210,negated_conjecture,
    ( v2_waybel_7(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | v2_waybel_0(esk2_0,esk1_0)
    | ~ v1_lattice3(k7_lattice3(esk1_0))
    | ~ v5_orders_2(k7_lattice3(esk1_0))
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_199,c_0_170]),c_0_171]),c_0_172])).

cnf(c_0_211,negated_conjecture,
    ( v2_waybel_7(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | v13_waybel_0(esk2_0,esk1_0)
    | ~ v1_lattice3(k7_lattice3(esk1_0))
    | ~ v5_orders_2(k7_lattice3(esk1_0))
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_199,c_0_173]),c_0_174]),c_0_175])).

cnf(c_0_212,negated_conjecture,
    ( v2_waybel_7(esk2_0,esk1_0)
    | v2_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_200,c_0_47]),c_0_48]),c_0_28])])).

cnf(c_0_213,negated_conjecture,
    ( v2_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | v2_waybel_0(esk2_0,esk1_0)
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_201,c_0_47]),c_0_48]),c_0_28])])).

cnf(c_0_214,negated_conjecture,
    ( v13_waybel_0(esk2_0,esk1_0)
    | v2_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_202,c_0_47]),c_0_48]),c_0_28])])).

cnf(c_0_215,negated_conjecture,
    ( v2_waybel_7(esk2_0,esk1_0)
    | v13_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_203,c_0_47]),c_0_48]),c_0_28])])).

cnf(c_0_216,negated_conjecture,
    ( v13_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | v2_waybel_0(esk2_0,esk1_0)
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_204,c_0_47]),c_0_48]),c_0_28])])).

cnf(c_0_217,negated_conjecture,
    ( v13_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | v13_waybel_0(esk2_0,esk1_0)
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_205,c_0_47]),c_0_48]),c_0_28])])).

cnf(c_0_218,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(esk1_0)))))
    | v2_waybel_7(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_206,c_0_62]),c_0_28])])).

cnf(c_0_219,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(esk1_0)))))
    | v2_waybel_0(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_207,c_0_62]),c_0_28])])).

cnf(c_0_220,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(esk1_0)))))
    | v13_waybel_0(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_208,c_0_62]),c_0_28])])).

cnf(c_0_221,negated_conjecture,
    ( v2_waybel_7(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | v2_waybel_7(esk2_0,esk1_0)
    | ~ v5_orders_2(k7_lattice3(esk1_0))
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_209,c_0_40]),c_0_41]),c_0_28])])).

cnf(c_0_222,negated_conjecture,
    ( v2_waybel_7(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | v2_waybel_0(esk2_0,esk1_0)
    | ~ v5_orders_2(k7_lattice3(esk1_0))
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_210,c_0_40]),c_0_41]),c_0_28])])).

cnf(c_0_223,negated_conjecture,
    ( v2_waybel_7(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | v13_waybel_0(esk2_0,esk1_0)
    | ~ v5_orders_2(k7_lattice3(esk1_0))
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_211,c_0_40]),c_0_41]),c_0_28])])).

cnf(c_0_224,negated_conjecture,
    ( v1_xboole_0(esk2_0)
    | v1_xboole_0(esk2_0)
    | ~ v2_waybel_0(esk2_0,esk1_0)
    | ~ v13_waybel_0(esk2_0,esk1_0)
    | ~ v2_waybel_7(esk2_0,esk1_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ v1_waybel_0(esk2_0,k7_lattice3(esk1_0))
    | ~ v12_waybel_0(esk2_0,k7_lattice3(esk1_0))
    | ~ v1_waybel_7(esk2_0,k7_lattice3(esk1_0))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(esk1_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_225,negated_conjecture,
    ( v2_waybel_7(esk2_0,esk1_0)
    | v2_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_212,c_0_57]),c_0_58]),c_0_28])])).

cnf(c_0_226,negated_conjecture,
    ( v2_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | v2_waybel_0(esk2_0,esk1_0)
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_213,c_0_57]),c_0_58]),c_0_28])])).

cnf(c_0_227,negated_conjecture,
    ( v13_waybel_0(esk2_0,esk1_0)
    | v2_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_214,c_0_57]),c_0_58]),c_0_28])])).

cnf(c_0_228,negated_conjecture,
    ( v2_waybel_7(esk2_0,esk1_0)
    | v13_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_215,c_0_57]),c_0_58]),c_0_28])])).

cnf(c_0_229,negated_conjecture,
    ( v13_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | v2_waybel_0(esk2_0,esk1_0)
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_216,c_0_57]),c_0_58]),c_0_28])])).

cnf(c_0_230,negated_conjecture,
    ( v13_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | v13_waybel_0(esk2_0,esk1_0)
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_217,c_0_57]),c_0_58]),c_0_28])])).

cnf(c_0_231,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(esk1_0)))))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_218]),c_0_219]),c_0_220])).

cnf(c_0_232,negated_conjecture,
    ( v2_waybel_7(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | v2_waybel_7(esk2_0,esk1_0)
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_221,c_0_47]),c_0_48]),c_0_28])])).

cnf(c_0_233,negated_conjecture,
    ( v2_waybel_7(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | v2_waybel_0(esk2_0,esk1_0)
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_222,c_0_47]),c_0_48]),c_0_28])])).

cnf(c_0_234,negated_conjecture,
    ( v2_waybel_7(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | v13_waybel_0(esk2_0,esk1_0)
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_223,c_0_47]),c_0_48]),c_0_28])])).

cnf(c_0_235,negated_conjecture,
    ( v1_xboole_0(esk2_0)
    | ~ v2_waybel_0(esk2_0,esk1_0)
    | ~ v13_waybel_0(esk2_0,esk1_0)
    | ~ v2_waybel_7(esk2_0,esk1_0)
    | ~ v1_waybel_0(esk2_0,k7_lattice3(esk1_0))
    | ~ v12_waybel_0(esk2_0,k7_lattice3(esk1_0))
    | ~ v1_waybel_7(esk2_0,k7_lattice3(esk1_0))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(esk1_0)))) ),
    inference(cn,[status(thm)],[c_0_224])).

cnf(c_0_236,negated_conjecture,
    ( v2_waybel_7(esk2_0,esk1_0)
    | v2_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_225,c_0_68]),c_0_69]),c_0_28])])).

cnf(c_0_237,negated_conjecture,
    ( v2_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | v2_waybel_0(esk2_0,esk1_0)
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_226,c_0_68]),c_0_69]),c_0_28])])).

cnf(c_0_238,negated_conjecture,
    ( v13_waybel_0(esk2_0,esk1_0)
    | v2_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_227,c_0_68]),c_0_69]),c_0_28])])).

cnf(c_0_239,negated_conjecture,
    ( v2_waybel_7(esk2_0,esk1_0)
    | v13_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_228,c_0_68]),c_0_69]),c_0_28])])).

cnf(c_0_240,negated_conjecture,
    ( v13_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | v2_waybel_0(esk2_0,esk1_0)
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_229,c_0_68]),c_0_69]),c_0_28])])).

cnf(c_0_241,negated_conjecture,
    ( v13_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | v13_waybel_0(esk2_0,esk1_0)
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_230,c_0_68]),c_0_69]),c_0_28])])).

cnf(c_0_242,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(esk1_0))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_231,c_0_62]),c_0_28])])).

cnf(c_0_243,negated_conjecture,
    ( v2_waybel_7(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | v2_waybel_7(esk2_0,esk1_0)
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_232,c_0_57]),c_0_58]),c_0_28])])).

cnf(c_0_244,negated_conjecture,
    ( v2_waybel_7(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | v2_waybel_0(esk2_0,esk1_0)
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_233,c_0_57]),c_0_58]),c_0_28])])).

cnf(c_0_245,negated_conjecture,
    ( v2_waybel_7(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | v13_waybel_0(esk2_0,esk1_0)
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_234,c_0_57]),c_0_58]),c_0_28])])).

cnf(c_0_246,negated_conjecture,
    ( ~ v1_waybel_7(esk2_0,k7_lattice3(esk1_0))
    | ~ v12_waybel_0(esk2_0,k7_lattice3(esk1_0))
    | ~ v1_waybel_0(esk2_0,k7_lattice3(esk1_0))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(esk1_0))))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ v2_waybel_7(esk2_0,esk1_0)
    | ~ v13_waybel_0(esk2_0,esk1_0)
    | ~ v2_waybel_0(esk2_0,esk1_0) ),
    inference(sr,[status(thm)],[c_0_235,c_0_21])).

cnf(c_0_247,plain,
    ( v1_waybel_7(X1,X2)
    | v1_xboole_0(X1)
    | ~ v2_waybel_0(X1,k7_lattice3(X2))
    | ~ v13_waybel_0(X1,k7_lattice3(X2))
    | ~ v2_waybel_7(X1,k7_lattice3(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X2))))
    | ~ epred1_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_248,negated_conjecture,
    ( v2_waybel_7(esk2_0,esk1_0)
    | v2_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_236,c_0_62]),c_0_28])])).

cnf(c_0_249,negated_conjecture,
    ( v2_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | v2_waybel_0(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_237,c_0_62]),c_0_28])])).

cnf(c_0_250,negated_conjecture,
    ( v13_waybel_0(esk2_0,esk1_0)
    | v2_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_238,c_0_62]),c_0_28])])).

cnf(c_0_251,negated_conjecture,
    ( v2_waybel_7(esk2_0,esk1_0)
    | v13_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_239,c_0_62]),c_0_28])])).

cnf(c_0_252,negated_conjecture,
    ( v13_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | v2_waybel_0(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_240,c_0_62]),c_0_28])])).

cnf(c_0_253,negated_conjecture,
    ( v13_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | v13_waybel_0(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_241,c_0_62]),c_0_28])])).

cnf(c_0_254,negated_conjecture,
    ( v2_waybel_7(esk2_0,X1)
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != k7_lattice3(k7_lattice3(esk1_0))
    | ~ v2_waybel_7(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v13_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v2_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v1_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v2_lattice3(X1)
    | ~ v5_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ l1_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_130,c_0_242]),c_0_84]),c_0_21])).

cnf(c_0_255,negated_conjecture,
    ( v2_waybel_7(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | v2_waybel_7(esk2_0,esk1_0)
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_243,c_0_68]),c_0_69]),c_0_28])])).

cnf(c_0_256,negated_conjecture,
    ( v2_waybel_0(esk2_0,X1)
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != k7_lattice3(k7_lattice3(esk1_0))
    | ~ v2_waybel_7(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v13_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v2_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v1_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v2_lattice3(X1)
    | ~ v5_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ l1_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_242]),c_0_84]),c_0_21])).

cnf(c_0_257,negated_conjecture,
    ( v2_waybel_7(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | v2_waybel_0(esk2_0,esk1_0)
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_244,c_0_68]),c_0_69]),c_0_28])])).

cnf(c_0_258,negated_conjecture,
    ( v13_waybel_0(esk2_0,X1)
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != k7_lattice3(k7_lattice3(esk1_0))
    | ~ v2_waybel_7(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v13_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v2_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v1_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v2_lattice3(X1)
    | ~ v5_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ l1_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_242]),c_0_84]),c_0_21])).

cnf(c_0_259,negated_conjecture,
    ( v2_waybel_7(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | v13_waybel_0(esk2_0,esk1_0)
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_245,c_0_68]),c_0_69]),c_0_28])])).

cnf(c_0_260,negated_conjecture,
    ( ~ v1_waybel_7(esk2_0,k7_lattice3(esk1_0))
    | ~ v12_waybel_0(esk2_0,k7_lattice3(esk1_0))
    | ~ v1_waybel_0(esk2_0,k7_lattice3(esk1_0))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(esk1_0))))
    | ~ v2_waybel_7(esk2_0,esk1_0)
    | ~ v13_waybel_0(esk2_0,esk1_0)
    | ~ v2_waybel_0(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_246,c_0_103])])).

cnf(c_0_261,plain,
    ( v1_waybel_7(esk2_0,k7_lattice3(esk1_0))
    | ~ epred1_1(k7_lattice3(esk1_0))
    | ~ v2_waybel_7(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v13_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v2_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_247,c_0_242]),c_0_21])).

cnf(c_0_262,negated_conjecture,
    ( v2_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_139,c_0_248]),c_0_249]),c_0_250])).

cnf(c_0_263,negated_conjecture,
    ( v13_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_140,c_0_251]),c_0_252]),c_0_253])).

cnf(c_0_264,plain,
    ( v12_waybel_0(X1,X2)
    | v1_xboole_0(X1)
    | ~ v2_waybel_0(X1,k7_lattice3(X2))
    | ~ v13_waybel_0(X1,k7_lattice3(X2))
    | ~ v2_waybel_7(X1,k7_lattice3(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X2))))
    | ~ epred1_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_265,negated_conjecture,
    ( v2_waybel_7(esk2_0,X1)
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != k7_lattice3(k7_lattice3(esk1_0))
    | ~ v2_waybel_7(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v13_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v2_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v2_lattice3(X1)
    | ~ v5_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_254,c_0_40]),c_0_34])]),c_0_90])).

cnf(c_0_266,negated_conjecture,
    ( v2_waybel_7(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | v2_waybel_7(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_255,c_0_62]),c_0_28])])).

cnf(c_0_267,negated_conjecture,
    ( v2_waybel_0(esk2_0,X1)
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != k7_lattice3(k7_lattice3(esk1_0))
    | ~ v2_waybel_7(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v13_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v2_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v2_lattice3(X1)
    | ~ v5_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_256,c_0_40]),c_0_34])]),c_0_90])).

cnf(c_0_268,negated_conjecture,
    ( v2_waybel_7(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | v2_waybel_0(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_257,c_0_62]),c_0_28])])).

cnf(c_0_269,negated_conjecture,
    ( v13_waybel_0(esk2_0,X1)
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != k7_lattice3(k7_lattice3(esk1_0))
    | ~ v2_waybel_7(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v13_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v2_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v2_lattice3(X1)
    | ~ v5_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_258,c_0_40]),c_0_34])]),c_0_90])).

cnf(c_0_270,negated_conjecture,
    ( v2_waybel_7(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | v13_waybel_0(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_259,c_0_62]),c_0_28])])).

cnf(c_0_271,negated_conjecture,
    ( ~ v1_waybel_7(esk2_0,k7_lattice3(esk1_0))
    | ~ v12_waybel_0(esk2_0,k7_lattice3(esk1_0))
    | ~ v1_waybel_0(esk2_0,k7_lattice3(esk1_0))
    | ~ v2_waybel_7(esk2_0,esk1_0)
    | ~ v13_waybel_0(esk2_0,esk1_0)
    | ~ v2_waybel_0(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_260,c_0_164])])).

cnf(c_0_272,plain,
    ( v1_waybel_7(esk2_0,k7_lattice3(esk1_0))
    | ~ v2_waybel_7(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v1_lattice3(k7_lattice3(esk1_0))
    | ~ v5_orders_2(k7_lattice3(esk1_0))
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_261,c_0_33]),c_0_34])]),c_0_262]),c_0_263])).

cnf(c_0_273,plain,
    ( v12_waybel_0(esk2_0,k7_lattice3(esk1_0))
    | ~ epred1_1(k7_lattice3(esk1_0))
    | ~ v2_waybel_7(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v13_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v2_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_264,c_0_242]),c_0_21])).

cnf(c_0_274,plain,
    ( v1_waybel_0(X1,X2)
    | v1_xboole_0(X1)
    | ~ v2_waybel_0(X1,k7_lattice3(X2))
    | ~ v13_waybel_0(X1,k7_lattice3(X2))
    | ~ v2_waybel_7(X1,k7_lattice3(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X2))))
    | ~ epred1_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_275,negated_conjecture,
    ( v2_waybel_7(esk2_0,esk1_0)
    | ~ v2_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v5_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v4_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ l1_orders_2(k7_lattice3(k7_lattice3(esk1_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_265,c_0_27]),c_0_102]),c_0_41]),c_0_48]),c_0_58]),c_0_69]),c_0_28])]),c_0_248]),c_0_251]),c_0_266])).

cnf(c_0_276,negated_conjecture,
    ( v2_waybel_0(esk2_0,esk1_0)
    | ~ v2_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v5_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v4_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ l1_orders_2(k7_lattice3(k7_lattice3(esk1_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_267,c_0_27]),c_0_102]),c_0_41]),c_0_48]),c_0_58]),c_0_69]),c_0_28])]),c_0_249]),c_0_252]),c_0_268])).

cnf(c_0_277,negated_conjecture,
    ( v13_waybel_0(esk2_0,esk1_0)
    | ~ v2_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v5_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v4_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ l1_orders_2(k7_lattice3(k7_lattice3(esk1_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_269,c_0_27]),c_0_102]),c_0_41]),c_0_48]),c_0_58]),c_0_69]),c_0_28])]),c_0_250]),c_0_253]),c_0_270])).

cnf(c_0_278,negated_conjecture,
    ( ~ v12_waybel_0(esk2_0,k7_lattice3(esk1_0))
    | ~ v1_waybel_0(esk2_0,k7_lattice3(esk1_0))
    | ~ v2_waybel_7(esk2_0,esk1_0)
    | ~ v13_waybel_0(esk2_0,esk1_0)
    | ~ v2_waybel_0(esk2_0,esk1_0)
    | ~ v1_lattice3(k7_lattice3(esk1_0))
    | ~ v5_orders_2(k7_lattice3(esk1_0))
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_271,c_0_272]),c_0_162])).

cnf(c_0_279,plain,
    ( v12_waybel_0(esk2_0,k7_lattice3(esk1_0))
    | ~ v2_waybel_7(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v1_lattice3(k7_lattice3(esk1_0))
    | ~ v5_orders_2(k7_lattice3(esk1_0))
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_273,c_0_33]),c_0_34])]),c_0_262]),c_0_263])).

cnf(c_0_280,plain,
    ( v1_waybel_0(esk2_0,k7_lattice3(esk1_0))
    | ~ epred1_1(k7_lattice3(esk1_0))
    | ~ v2_waybel_7(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v13_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v2_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_274,c_0_242]),c_0_21])).

cnf(c_0_281,negated_conjecture,
    ( v2_waybel_7(esk2_0,esk1_0)
    | ~ v5_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v4_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ l1_orders_2(k7_lattice3(k7_lattice3(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_275,c_0_92]),c_0_41]),c_0_28])])).

cnf(c_0_282,negated_conjecture,
    ( v2_waybel_0(esk2_0,esk1_0)
    | ~ v5_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v4_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ l1_orders_2(k7_lattice3(k7_lattice3(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_276,c_0_92]),c_0_41]),c_0_28])])).

cnf(c_0_283,negated_conjecture,
    ( v13_waybel_0(esk2_0,esk1_0)
    | ~ v5_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v4_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ l1_orders_2(k7_lattice3(k7_lattice3(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_277,c_0_92]),c_0_41]),c_0_28])])).

cnf(c_0_284,plain,
    ( ~ v1_waybel_0(esk2_0,k7_lattice3(esk1_0))
    | ~ v2_waybel_7(esk2_0,esk1_0)
    | ~ v13_waybel_0(esk2_0,esk1_0)
    | ~ v2_waybel_0(esk2_0,esk1_0)
    | ~ v1_lattice3(k7_lattice3(esk1_0))
    | ~ v5_orders_2(k7_lattice3(esk1_0))
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_278,c_0_279]),c_0_162])).

cnf(c_0_285,plain,
    ( v1_waybel_0(esk2_0,k7_lattice3(esk1_0))
    | ~ v2_waybel_7(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v1_lattice3(k7_lattice3(esk1_0))
    | ~ v5_orders_2(k7_lattice3(esk1_0))
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_280,c_0_33]),c_0_34])]),c_0_262]),c_0_263])).

cnf(c_0_286,negated_conjecture,
    ( v2_waybel_7(esk2_0,esk1_0)
    | ~ v5_orders_2(k7_lattice3(esk1_0))
    | ~ v4_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ l1_orders_2(k7_lattice3(k7_lattice3(esk1_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_281,c_0_47]),c_0_90])).

cnf(c_0_287,negated_conjecture,
    ( v2_waybel_0(esk2_0,esk1_0)
    | ~ v5_orders_2(k7_lattice3(esk1_0))
    | ~ v4_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ l1_orders_2(k7_lattice3(k7_lattice3(esk1_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_282,c_0_47]),c_0_90])).

cnf(c_0_288,negated_conjecture,
    ( v13_waybel_0(esk2_0,esk1_0)
    | ~ v5_orders_2(k7_lattice3(esk1_0))
    | ~ v4_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ l1_orders_2(k7_lattice3(k7_lattice3(esk1_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_283,c_0_47]),c_0_90])).

cnf(c_0_289,plain,
    ( ~ v2_waybel_7(esk2_0,esk1_0)
    | ~ v13_waybel_0(esk2_0,esk1_0)
    | ~ v2_waybel_0(esk2_0,esk1_0)
    | ~ v1_lattice3(k7_lattice3(esk1_0))
    | ~ v5_orders_2(k7_lattice3(esk1_0))
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_284,c_0_285]),c_0_162])).

cnf(c_0_290,negated_conjecture,
    ( v2_waybel_7(esk2_0,esk1_0)
    | ~ v4_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ l1_orders_2(k7_lattice3(k7_lattice3(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_286,c_0_47]),c_0_48]),c_0_28])])).

cnf(c_0_291,negated_conjecture,
    ( v2_waybel_0(esk2_0,esk1_0)
    | ~ v4_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ l1_orders_2(k7_lattice3(k7_lattice3(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_287,c_0_47]),c_0_48]),c_0_28])])).

cnf(c_0_292,negated_conjecture,
    ( v13_waybel_0(esk2_0,esk1_0)
    | ~ v4_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ l1_orders_2(k7_lattice3(k7_lattice3(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_288,c_0_47]),c_0_48]),c_0_28])])).

cnf(c_0_293,plain,
    ( ~ v2_waybel_7(esk2_0,esk1_0)
    | ~ v13_waybel_0(esk2_0,esk1_0)
    | ~ v2_waybel_0(esk2_0,esk1_0)
    | ~ v5_orders_2(k7_lattice3(esk1_0))
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_289,c_0_40]),c_0_41]),c_0_28])])).

cnf(c_0_294,negated_conjecture,
    ( v2_waybel_7(esk2_0,esk1_0)
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ l1_orders_2(k7_lattice3(k7_lattice3(esk1_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_290,c_0_57]),c_0_90])).

cnf(c_0_295,negated_conjecture,
    ( v2_waybel_0(esk2_0,esk1_0)
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ l1_orders_2(k7_lattice3(k7_lattice3(esk1_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_291,c_0_57]),c_0_90])).

cnf(c_0_296,negated_conjecture,
    ( v13_waybel_0(esk2_0,esk1_0)
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ l1_orders_2(k7_lattice3(k7_lattice3(esk1_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_292,c_0_57]),c_0_90])).

cnf(c_0_297,plain,
    ( ~ v2_waybel_7(esk2_0,esk1_0)
    | ~ v13_waybel_0(esk2_0,esk1_0)
    | ~ v2_waybel_0(esk2_0,esk1_0)
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_293,c_0_47]),c_0_48]),c_0_28])])).

cnf(c_0_298,negated_conjecture,
    ( v2_waybel_7(esk2_0,esk1_0)
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ l1_orders_2(k7_lattice3(k7_lattice3(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_294,c_0_57]),c_0_58]),c_0_28])])).

cnf(c_0_299,negated_conjecture,
    ( v2_waybel_0(esk2_0,esk1_0)
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ l1_orders_2(k7_lattice3(k7_lattice3(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_295,c_0_57]),c_0_58]),c_0_28])])).

cnf(c_0_300,negated_conjecture,
    ( v13_waybel_0(esk2_0,esk1_0)
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ l1_orders_2(k7_lattice3(k7_lattice3(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_296,c_0_57]),c_0_58]),c_0_28])])).

cnf(c_0_301,plain,
    ( ~ v2_waybel_7(esk2_0,esk1_0)
    | ~ v13_waybel_0(esk2_0,esk1_0)
    | ~ v2_waybel_0(esk2_0,esk1_0)
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_297,c_0_57]),c_0_58]),c_0_28])])).

cnf(c_0_302,negated_conjecture,
    ( v2_waybel_7(esk2_0,esk1_0)
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(k7_lattice3(esk1_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_298,c_0_68]),c_0_90])).

cnf(c_0_303,negated_conjecture,
    ( v2_waybel_0(esk2_0,esk1_0)
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(k7_lattice3(esk1_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_299,c_0_68]),c_0_90])).

cnf(c_0_304,negated_conjecture,
    ( v13_waybel_0(esk2_0,esk1_0)
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(k7_lattice3(esk1_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_300,c_0_68]),c_0_90])).

cnf(c_0_305,plain,
    ( ~ v2_waybel_7(esk2_0,esk1_0)
    | ~ v13_waybel_0(esk2_0,esk1_0)
    | ~ v2_waybel_0(esk2_0,esk1_0)
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_301,c_0_68]),c_0_69]),c_0_28])])).

cnf(c_0_306,negated_conjecture,
    ( v2_waybel_7(esk2_0,esk1_0)
    | ~ l1_orders_2(k7_lattice3(k7_lattice3(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_302,c_0_68]),c_0_69]),c_0_28])])).

cnf(c_0_307,negated_conjecture,
    ( v2_waybel_0(esk2_0,esk1_0)
    | ~ l1_orders_2(k7_lattice3(k7_lattice3(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_303,c_0_68]),c_0_69]),c_0_28])])).

cnf(c_0_308,negated_conjecture,
    ( v13_waybel_0(esk2_0,esk1_0)
    | ~ l1_orders_2(k7_lattice3(k7_lattice3(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_304,c_0_68]),c_0_69]),c_0_28])])).

cnf(c_0_309,plain,
    ( ~ l1_orders_2(k7_lattice3(k7_lattice3(esk1_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_305,c_0_306]),c_0_90]),c_0_307]),c_0_308])).

cnf(c_0_310,plain,
    ( ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_309,c_0_62])).

cnf(c_0_311,plain,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_310,c_0_62]),c_0_28])]),
    [proof]).

%------------------------------------------------------------------------------
