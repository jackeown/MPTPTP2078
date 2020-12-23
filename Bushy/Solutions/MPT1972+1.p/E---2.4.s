%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : waybel_7__t21_waybel_7.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:04 EDT 2019

% Result     : Theorem 268.74s
% Output     : CNFRefutation 268.74s
% Verified   : 
% Statistics : Number of formulae       :  197 (2658427 expanded)
%              Number of clauses        :  164 (1035192 expanded)
%              Number of leaves         :   15 (656257 expanded)
%              Depth                    :   51
%              Number of atoms          : 1379 (35545633 expanded)
%              Number of equality atoms :   70 (661467 expanded)
%              Maximal formula depth    :   33 (   7 average)
%              Maximal clause size      :   95 (   6 average)
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
    file('/export/starexec/sandbox/benchmark/waybel_7__t21_waybel_7.p',t21_waybel_7)).

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
    file('/export/starexec/sandbox/benchmark/waybel_7__t21_waybel_7.p',t20_waybel_7)).

fof(fc6_yellow_7,axiom,(
    ! [X1] :
      ( ( v1_lattice3(X1)
        & l1_orders_2(X1) )
     => ( v1_orders_2(k7_lattice3(X1))
        & v2_lattice3(k7_lattice3(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t21_waybel_7.p',fc6_yellow_7)).

fof(fc5_yellow_7,axiom,(
    ! [X1] :
      ( ( v2_lattice3(X1)
        & l1_orders_2(X1) )
     => ( v1_orders_2(k7_lattice3(X1))
        & v1_lattice3(k7_lattice3(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t21_waybel_7.p',fc5_yellow_7)).

fof(t8_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => k7_lattice3(k7_lattice3(X1)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t21_waybel_7.p',t8_lattice3)).

fof(abstractness_v1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v1_orders_2(X1)
       => X1 = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t21_waybel_7.p',abstractness_v1_orders_2)).

fof(dt_k7_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v1_orders_2(k7_lattice3(X1))
        & l1_orders_2(k7_lattice3(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t21_waybel_7.p',dt_k7_lattice3)).

fof(fc3_yellow_7,axiom,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ( v1_orders_2(k7_lattice3(X1))
        & v5_orders_2(k7_lattice3(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t21_waybel_7.p',fc3_yellow_7)).

fof(dt_g1_orders_2,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
     => ( v1_orders_2(g1_orders_2(X1,X2))
        & l1_orders_2(g1_orders_2(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t21_waybel_7.p',dt_g1_orders_2)).

fof(dt_u1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t21_waybel_7.p',dt_u1_orders_2)).

fof(fc2_yellow_7,axiom,(
    ! [X1] :
      ( ( v4_orders_2(X1)
        & l1_orders_2(X1) )
     => ( v1_orders_2(k7_lattice3(X1))
        & v4_orders_2(k7_lattice3(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t21_waybel_7.p',fc2_yellow_7)).

fof(fc1_yellow_7,axiom,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & l1_orders_2(X1) )
     => ( v1_orders_2(k7_lattice3(X1))
        & v3_orders_2(k7_lattice3(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t21_waybel_7.p',fc1_yellow_7)).

fof(free_g1_orders_2,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
     => ! [X3,X4] :
          ( g1_orders_2(X1,X2) = g1_orders_2(X3,X4)
         => ( X1 = X3
            & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t21_waybel_7.p',free_g1_orders_2)).

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
    file('/export/starexec/sandbox/benchmark/waybel_7__t21_waybel_7.p',t19_waybel_7)).

fof(c_0_14,plain,(
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

fof(c_0_15,negated_conjecture,(
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

fof(c_0_16,plain,(
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
    inference(split_equiv,[status(thm)],[c_0_14])).

fof(c_0_17,negated_conjecture,
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
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])])).

fof(c_0_18,plain,(
    ! [X55,X56] :
      ( ( ~ v1_xboole_0(X56)
        | v1_xboole_0(X56)
        | ~ v1_waybel_0(X56,X55)
        | ~ v12_waybel_0(X56,X55)
        | ~ v1_waybel_7(X56,X55)
        | ~ m1_subset_1(X56,k1_zfmisc_1(u1_struct_0(X55)))
        | ~ epred1_1(X55) )
      & ( v2_waybel_0(X56,k7_lattice3(X55))
        | v1_xboole_0(X56)
        | ~ v1_waybel_0(X56,X55)
        | ~ v12_waybel_0(X56,X55)
        | ~ v1_waybel_7(X56,X55)
        | ~ m1_subset_1(X56,k1_zfmisc_1(u1_struct_0(X55)))
        | ~ epred1_1(X55) )
      & ( v13_waybel_0(X56,k7_lattice3(X55))
        | v1_xboole_0(X56)
        | ~ v1_waybel_0(X56,X55)
        | ~ v12_waybel_0(X56,X55)
        | ~ v1_waybel_7(X56,X55)
        | ~ m1_subset_1(X56,k1_zfmisc_1(u1_struct_0(X55)))
        | ~ epred1_1(X55) )
      & ( v2_waybel_7(X56,k7_lattice3(X55))
        | v1_xboole_0(X56)
        | ~ v1_waybel_0(X56,X55)
        | ~ v12_waybel_0(X56,X55)
        | ~ v1_waybel_7(X56,X55)
        | ~ m1_subset_1(X56,k1_zfmisc_1(u1_struct_0(X55)))
        | ~ epred1_1(X55) )
      & ( m1_subset_1(X56,k1_zfmisc_1(u1_struct_0(k7_lattice3(X55))))
        | v1_xboole_0(X56)
        | ~ v1_waybel_0(X56,X55)
        | ~ v12_waybel_0(X56,X55)
        | ~ v1_waybel_7(X56,X55)
        | ~ m1_subset_1(X56,k1_zfmisc_1(u1_struct_0(X55)))
        | ~ epred1_1(X55) )
      & ( ~ v1_xboole_0(X56)
        | v1_xboole_0(X56)
        | ~ v2_waybel_0(X56,k7_lattice3(X55))
        | ~ v13_waybel_0(X56,k7_lattice3(X55))
        | ~ v2_waybel_7(X56,k7_lattice3(X55))
        | ~ m1_subset_1(X56,k1_zfmisc_1(u1_struct_0(k7_lattice3(X55))))
        | ~ epred1_1(X55) )
      & ( v1_waybel_0(X56,X55)
        | v1_xboole_0(X56)
        | ~ v2_waybel_0(X56,k7_lattice3(X55))
        | ~ v13_waybel_0(X56,k7_lattice3(X55))
        | ~ v2_waybel_7(X56,k7_lattice3(X55))
        | ~ m1_subset_1(X56,k1_zfmisc_1(u1_struct_0(k7_lattice3(X55))))
        | ~ epred1_1(X55) )
      & ( v12_waybel_0(X56,X55)
        | v1_xboole_0(X56)
        | ~ v2_waybel_0(X56,k7_lattice3(X55))
        | ~ v13_waybel_0(X56,k7_lattice3(X55))
        | ~ v2_waybel_7(X56,k7_lattice3(X55))
        | ~ m1_subset_1(X56,k1_zfmisc_1(u1_struct_0(k7_lattice3(X55))))
        | ~ epred1_1(X55) )
      & ( v1_waybel_7(X56,X55)
        | v1_xboole_0(X56)
        | ~ v2_waybel_0(X56,k7_lattice3(X55))
        | ~ v13_waybel_0(X56,k7_lattice3(X55))
        | ~ v2_waybel_7(X56,k7_lattice3(X55))
        | ~ m1_subset_1(X56,k1_zfmisc_1(u1_struct_0(k7_lattice3(X55))))
        | ~ epred1_1(X55) )
      & ( m1_subset_1(X56,k1_zfmisc_1(u1_struct_0(X55)))
        | v1_xboole_0(X56)
        | ~ v2_waybel_0(X56,k7_lattice3(X55))
        | ~ v13_waybel_0(X56,k7_lattice3(X55))
        | ~ v2_waybel_7(X56,k7_lattice3(X55))
        | ~ m1_subset_1(X56,k1_zfmisc_1(u1_struct_0(k7_lattice3(X55))))
        | ~ epred1_1(X55) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])])).

cnf(c_0_19,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0)
    | ~ v1_xboole_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_20,axiom,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & v1_lattice3(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1) )
     => epred1_1(X1) ) ),
    inference(apply_def,[status(thm)],[t20_waybel_7,c_0_14])).

fof(c_0_21,plain,(
    ! [X50] :
      ( ( v1_orders_2(k7_lattice3(X50))
        | ~ v1_lattice3(X50)
        | ~ l1_orders_2(X50) )
      & ( v2_lattice3(k7_lattice3(X50))
        | ~ v1_lattice3(X50)
        | ~ l1_orders_2(X50) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc6_yellow_7])])])).

cnf(c_0_22,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X2))))
    | v1_xboole_0(X1)
    | ~ v1_waybel_0(X1,X2)
    | ~ v12_waybel_0(X1,X2)
    | ~ v1_waybel_7(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ epred1_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(esk1_0))))
    | m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(cn,[status(thm)],[c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( v1_waybel_0(esk2_0,k7_lattice3(esk1_0))
    | m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,negated_conjecture,
    ( v12_waybel_0(esk2_0,k7_lattice3(esk1_0))
    | m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,negated_conjecture,
    ( v1_waybel_7(esk2_0,k7_lattice3(esk1_0))
    | m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_28,plain,(
    ! [X28] :
      ( ~ v3_orders_2(X28)
      | ~ v4_orders_2(X28)
      | ~ v5_orders_2(X28)
      | ~ v1_lattice3(X28)
      | ~ v2_lattice3(X28)
      | ~ l1_orders_2(X28)
      | epred1_1(X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])).

cnf(c_0_29,plain,
    ( v2_lattice3(k7_lattice3(X1))
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,negated_conjecture,
    ( v1_lattice3(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_31,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(esk1_0)))))
    | m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ epred1_1(k7_lattice3(esk1_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_25]),c_0_26]),c_0_27])).

cnf(c_0_33,plain,
    ( epred1_1(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( v2_lattice3(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])])).

fof(c_0_35,plain,(
    ! [X49] :
      ( ( v1_orders_2(k7_lattice3(X49))
        | ~ v2_lattice3(X49)
        | ~ l1_orders_2(X49) )
      & ( v1_lattice3(k7_lattice3(X49))
        | ~ v2_lattice3(X49)
        | ~ l1_orders_2(X49) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc5_yellow_7])])])).

fof(c_0_36,plain,(
    ! [X44] :
      ( ~ l1_orders_2(X44)
      | k7_lattice3(k7_lattice3(X44)) = g1_orders_2(u1_struct_0(X44),u1_orders_2(X44)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_lattice3])])).

fof(c_0_37,plain,(
    ! [X7] :
      ( ~ l1_orders_2(X7)
      | ~ v1_orders_2(X7)
      | X7 = g1_orders_2(u1_struct_0(X7),u1_orders_2(X7)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_orders_2])])).

fof(c_0_38,plain,(
    ! [X12] :
      ( ( v1_orders_2(k7_lattice3(X12))
        | ~ l1_orders_2(X12) )
      & ( l1_orders_2(k7_lattice3(X12))
        | ~ l1_orders_2(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_lattice3])])])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(esk1_0)))))
    | m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ l1_orders_2(k7_lattice3(esk1_0))
    | ~ v1_lattice3(k7_lattice3(esk1_0))
    | ~ v5_orders_2(k7_lattice3(esk1_0))
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])])).

cnf(c_0_40,plain,
    ( v1_lattice3(k7_lattice3(X1))
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( v2_lattice3(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_42,plain,(
    ! [X48] :
      ( ( v1_orders_2(k7_lattice3(X48))
        | ~ v5_orders_2(X48)
        | ~ l1_orders_2(X48) )
      & ( v5_orders_2(k7_lattice3(X48))
        | ~ v5_orders_2(X48)
        | ~ l1_orders_2(X48) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc3_yellow_7])])])).

fof(c_0_43,plain,(
    ! [X10,X11] :
      ( ( v1_orders_2(g1_orders_2(X10,X11))
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X10,X10))) )
      & ( l1_orders_2(g1_orders_2(X10,X11))
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X10,X10))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_g1_orders_2])])])).

cnf(c_0_44,plain,
    ( k7_lattice3(k7_lattice3(X1)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_45,plain,(
    ! [X14] :
      ( ~ l1_orders_2(X14)
      | m1_subset_1(u1_orders_2(X14),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X14)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).

cnf(c_0_46,plain,
    ( X1 = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | ~ l1_orders_2(X1)
    | ~ v1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_47,plain,
    ( v1_orders_2(k7_lattice3(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_48,plain,
    ( l1_orders_2(k7_lattice3(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(esk1_0)))))
    | m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ l1_orders_2(k7_lattice3(esk1_0))
    | ~ v5_orders_2(k7_lattice3(esk1_0))
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_31]),c_0_41])])).

cnf(c_0_50,plain,
    ( v5_orders_2(k7_lattice3(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_51,negated_conjecture,
    ( v5_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_52,plain,(
    ! [X47] :
      ( ( v1_orders_2(k7_lattice3(X47))
        | ~ v4_orders_2(X47)
        | ~ l1_orders_2(X47) )
      & ( v4_orders_2(k7_lattice3(X47))
        | ~ v4_orders_2(X47)
        | ~ l1_orders_2(X47) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc2_yellow_7])])])).

cnf(c_0_53,plain,
    ( l1_orders_2(g1_orders_2(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_54,negated_conjecture,
    ( g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0)) = k7_lattice3(k7_lattice3(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_31])).

cnf(c_0_55,plain,
    ( m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_56,plain,
    ( g1_orders_2(u1_struct_0(k7_lattice3(X1)),u1_orders_2(k7_lattice3(X1))) = k7_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48])).

cnf(c_0_57,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(esk1_0)))))
    | m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ l1_orders_2(k7_lattice3(esk1_0))
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_31]),c_0_51])])).

cnf(c_0_58,plain,
    ( v4_orders_2(k7_lattice3(X1))
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_59,negated_conjecture,
    ( v4_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_60,plain,(
    ! [X46] :
      ( ( v1_orders_2(k7_lattice3(X46))
        | ~ v3_orders_2(X46)
        | ~ l1_orders_2(X46) )
      & ( v3_orders_2(k7_lattice3(X46))
        | ~ v3_orders_2(X46)
        | ~ l1_orders_2(X46) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_yellow_7])])])).

fof(c_0_61,plain,(
    ! [X19,X20,X21,X22] :
      ( ( X19 = X21
        | g1_orders_2(X19,X20) != g1_orders_2(X21,X22)
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X19,X19))) )
      & ( X20 = X22
        | g1_orders_2(X19,X20) != g1_orders_2(X21,X22)
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X19,X19))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_orders_2])])])])).

cnf(c_0_62,negated_conjecture,
    ( l1_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ m1_subset_1(u1_orders_2(esk1_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)))) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_63,negated_conjecture,
    ( m1_subset_1(u1_orders_2(esk1_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)))) ),
    inference(spm,[status(thm)],[c_0_55,c_0_31])).

cnf(c_0_64,plain,
    ( g1_orders_2(u1_struct_0(k7_lattice3(X1)),u1_orders_2(k7_lattice3(X1))) = k7_lattice3(k7_lattice3(k7_lattice3(X1)))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_48])).

cnf(c_0_65,negated_conjecture,
    ( g1_orders_2(u1_struct_0(k7_lattice3(esk1_0)),u1_orders_2(k7_lattice3(esk1_0))) = k7_lattice3(esk1_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_31])).

cnf(c_0_66,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(esk1_0)))))
    | m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ l1_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_31]),c_0_59])])).

cnf(c_0_67,plain,
    ( v3_orders_2(k7_lattice3(X1))
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_68,negated_conjecture,
    ( v3_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_69,plain,
    ( X1 = X2
    | g1_orders_2(X1,X3) != g1_orders_2(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_70,negated_conjecture,
    ( l1_orders_2(k7_lattice3(k7_lattice3(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_63])])).

cnf(c_0_71,negated_conjecture,
    ( k7_lattice3(k7_lattice3(k7_lattice3(esk1_0))) = k7_lattice3(esk1_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_31]),c_0_65])).

cnf(c_0_72,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(esk1_0)))))
    | m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_31]),c_0_68])])).

cnf(c_0_73,negated_conjecture,
    ( u1_struct_0(esk1_0) = X1
    | g1_orders_2(X1,X2) != k7_lattice3(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_54]),c_0_63])])).

cnf(c_0_74,negated_conjecture,
    ( g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(esk1_0))),u1_orders_2(k7_lattice3(k7_lattice3(esk1_0)))) = k7_lattice3(k7_lattice3(esk1_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_70]),c_0_71])).

fof(c_0_75,plain,(
    ! [X23,X24,X25] :
      ( ( ~ v1_xboole_0(X25)
        | v1_xboole_0(X25)
        | ~ v2_waybel_0(X25,X23)
        | ~ v13_waybel_0(X25,X23)
        | ~ v2_waybel_7(X25,X23)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))
        | g1_orders_2(u1_struct_0(X23),u1_orders_2(X23)) != g1_orders_2(u1_struct_0(X24),u1_orders_2(X24))
        | ~ v3_orders_2(X24)
        | ~ v4_orders_2(X24)
        | ~ v5_orders_2(X24)
        | ~ v1_lattice3(X24)
        | ~ v2_lattice3(X24)
        | ~ l1_orders_2(X24)
        | ~ v3_orders_2(X23)
        | ~ v4_orders_2(X23)
        | ~ v5_orders_2(X23)
        | ~ v1_lattice3(X23)
        | ~ v2_lattice3(X23)
        | ~ l1_orders_2(X23) )
      & ( v2_waybel_0(X25,X24)
        | v1_xboole_0(X25)
        | ~ v2_waybel_0(X25,X23)
        | ~ v13_waybel_0(X25,X23)
        | ~ v2_waybel_7(X25,X23)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))
        | g1_orders_2(u1_struct_0(X23),u1_orders_2(X23)) != g1_orders_2(u1_struct_0(X24),u1_orders_2(X24))
        | ~ v3_orders_2(X24)
        | ~ v4_orders_2(X24)
        | ~ v5_orders_2(X24)
        | ~ v1_lattice3(X24)
        | ~ v2_lattice3(X24)
        | ~ l1_orders_2(X24)
        | ~ v3_orders_2(X23)
        | ~ v4_orders_2(X23)
        | ~ v5_orders_2(X23)
        | ~ v1_lattice3(X23)
        | ~ v2_lattice3(X23)
        | ~ l1_orders_2(X23) )
      & ( v13_waybel_0(X25,X24)
        | v1_xboole_0(X25)
        | ~ v2_waybel_0(X25,X23)
        | ~ v13_waybel_0(X25,X23)
        | ~ v2_waybel_7(X25,X23)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))
        | g1_orders_2(u1_struct_0(X23),u1_orders_2(X23)) != g1_orders_2(u1_struct_0(X24),u1_orders_2(X24))
        | ~ v3_orders_2(X24)
        | ~ v4_orders_2(X24)
        | ~ v5_orders_2(X24)
        | ~ v1_lattice3(X24)
        | ~ v2_lattice3(X24)
        | ~ l1_orders_2(X24)
        | ~ v3_orders_2(X23)
        | ~ v4_orders_2(X23)
        | ~ v5_orders_2(X23)
        | ~ v1_lattice3(X23)
        | ~ v2_lattice3(X23)
        | ~ l1_orders_2(X23) )
      & ( v2_waybel_7(X25,X24)
        | v1_xboole_0(X25)
        | ~ v2_waybel_0(X25,X23)
        | ~ v13_waybel_0(X25,X23)
        | ~ v2_waybel_7(X25,X23)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))
        | g1_orders_2(u1_struct_0(X23),u1_orders_2(X23)) != g1_orders_2(u1_struct_0(X24),u1_orders_2(X24))
        | ~ v3_orders_2(X24)
        | ~ v4_orders_2(X24)
        | ~ v5_orders_2(X24)
        | ~ v1_lattice3(X24)
        | ~ v2_lattice3(X24)
        | ~ l1_orders_2(X24)
        | ~ v3_orders_2(X23)
        | ~ v4_orders_2(X23)
        | ~ v5_orders_2(X23)
        | ~ v1_lattice3(X23)
        | ~ v2_lattice3(X23)
        | ~ l1_orders_2(X23) )
      & ( m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
        | v1_xboole_0(X25)
        | ~ v2_waybel_0(X25,X23)
        | ~ v13_waybel_0(X25,X23)
        | ~ v2_waybel_7(X25,X23)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))
        | g1_orders_2(u1_struct_0(X23),u1_orders_2(X23)) != g1_orders_2(u1_struct_0(X24),u1_orders_2(X24))
        | ~ v3_orders_2(X24)
        | ~ v4_orders_2(X24)
        | ~ v5_orders_2(X24)
        | ~ v1_lattice3(X24)
        | ~ v2_lattice3(X24)
        | ~ l1_orders_2(X24)
        | ~ v3_orders_2(X23)
        | ~ v4_orders_2(X23)
        | ~ v5_orders_2(X23)
        | ~ v1_lattice3(X23)
        | ~ v2_lattice3(X23)
        | ~ l1_orders_2(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t19_waybel_7])])])])])).

cnf(c_0_76,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(esk1_0)))))
    | m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_48]),c_0_31])])).

cnf(c_0_77,negated_conjecture,
    ( u1_struct_0(k7_lattice3(k7_lattice3(esk1_0))) = u1_struct_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_78,plain,
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

cnf(c_0_79,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_77])])).

cnf(c_0_80,plain,
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

cnf(c_0_81,plain,
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

cnf(c_0_83,plain,
    ( v1_orders_2(g1_orders_2(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_84,negated_conjecture,
    ( v2_waybel_7(esk2_0,X1)
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != k7_lattice3(k7_lattice3(esk1_0))
    | ~ v2_waybel_7(esk2_0,esk1_0)
    | ~ v13_waybel_0(esk2_0,esk1_0)
    | ~ v2_waybel_0(esk2_0,esk1_0)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v1_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_54]),c_0_31]),c_0_41]),c_0_30]),c_0_51]),c_0_59]),c_0_68])]),c_0_24])).

cnf(c_0_85,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(esk1_0))))
    | v2_waybel_7(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_86,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(esk1_0))))
    | v2_waybel_0(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_87,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(esk1_0))))
    | v13_waybel_0(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_88,negated_conjecture,
    ( v2_waybel_0(esk2_0,X1)
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != k7_lattice3(k7_lattice3(esk1_0))
    | ~ v2_waybel_7(esk2_0,esk1_0)
    | ~ v13_waybel_0(esk2_0,esk1_0)
    | ~ v2_waybel_0(esk2_0,esk1_0)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v1_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_79]),c_0_54]),c_0_31]),c_0_41]),c_0_30]),c_0_51]),c_0_59]),c_0_68])]),c_0_24])).

cnf(c_0_89,negated_conjecture,
    ( v13_waybel_0(esk2_0,X1)
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != k7_lattice3(k7_lattice3(esk1_0))
    | ~ v2_waybel_7(esk2_0,esk1_0)
    | ~ v13_waybel_0(esk2_0,esk1_0)
    | ~ v2_waybel_0(esk2_0,esk1_0)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v1_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_79]),c_0_54]),c_0_31]),c_0_41]),c_0_30]),c_0_51]),c_0_59]),c_0_68])]),c_0_24])).

cnf(c_0_90,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(X1)))
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != k7_lattice3(k7_lattice3(esk1_0))
    | ~ v2_waybel_7(esk2_0,esk1_0)
    | ~ v13_waybel_0(esk2_0,esk1_0)
    | ~ v2_waybel_0(esk2_0,esk1_0)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v1_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_79]),c_0_54]),c_0_31]),c_0_41]),c_0_30]),c_0_51]),c_0_59]),c_0_68])]),c_0_24])).

cnf(c_0_91,plain,
    ( X1 = X2
    | g1_orders_2(X3,X1) != g1_orders_2(X4,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_92,negated_conjecture,
    ( v1_orders_2(k7_lattice3(k7_lattice3(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_54]),c_0_63])])).

cnf(c_0_93,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | v1_xboole_0(X1)
    | ~ v2_waybel_0(X1,k7_lattice3(X2))
    | ~ v13_waybel_0(X1,k7_lattice3(X2))
    | ~ v2_waybel_7(X1,k7_lattice3(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X2))))
    | ~ epred1_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_94,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(esk1_0))))
    | v2_waybel_7(esk2_0,X1)
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != k7_lattice3(k7_lattice3(esk1_0))
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v1_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_86]),c_0_87])).

cnf(c_0_95,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(esk1_0))))
    | v2_waybel_0(esk2_0,X1)
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != k7_lattice3(k7_lattice3(esk1_0))
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v1_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_85]),c_0_86]),c_0_87])).

cnf(c_0_96,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(esk1_0))))
    | v13_waybel_0(esk2_0,X1)
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != k7_lattice3(k7_lattice3(esk1_0))
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v1_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_85]),c_0_86]),c_0_87])).

cnf(c_0_97,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(esk1_0))))
    | m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(X1)))
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != k7_lattice3(k7_lattice3(esk1_0))
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v1_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_85]),c_0_86]),c_0_87])).

cnf(c_0_98,negated_conjecture,
    ( u1_orders_2(esk1_0) = X1
    | g1_orders_2(X2,X1) != k7_lattice3(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_54]),c_0_63])])).

cnf(c_0_99,negated_conjecture,
    ( g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(k7_lattice3(k7_lattice3(esk1_0)))) = k7_lattice3(k7_lattice3(esk1_0)) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_92]),c_0_70])]),c_0_77])).

cnf(c_0_100,plain,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(esk1_0))))
    | m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(X1)))
    | g1_orders_2(u1_struct_0(k7_lattice3(X1)),u1_orders_2(k7_lattice3(X1))) != k7_lattice3(k7_lattice3(esk1_0))
    | ~ epred1_1(X1)
    | ~ l1_orders_2(k7_lattice3(X1))
    | ~ v2_lattice3(k7_lattice3(X1))
    | ~ v1_lattice3(k7_lattice3(X1))
    | ~ v5_orders_2(k7_lattice3(X1))
    | ~ v4_orders_2(k7_lattice3(X1))
    | ~ v3_orders_2(k7_lattice3(X1)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_24]),c_0_95]),c_0_96]),c_0_97])).

cnf(c_0_101,negated_conjecture,
    ( u1_orders_2(k7_lattice3(k7_lattice3(esk1_0))) = u1_orders_2(esk1_0) ),
    inference(spm,[status(thm)],[c_0_98,c_0_99])).

cnf(c_0_102,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(esk1_0))))
    | ~ epred1_1(k7_lattice3(esk1_0))
    | ~ v2_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v1_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v5_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v4_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_70]),c_0_77]),c_0_101]),c_0_54])])).

cnf(c_0_103,negated_conjecture,
    ( l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_71]),c_0_70])])).

cnf(c_0_104,negated_conjecture,
    ( v3_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_71]),c_0_70])])).

cnf(c_0_105,negated_conjecture,
    ( v4_orders_2(k7_lattice3(esk1_0))
    | ~ v4_orders_2(k7_lattice3(k7_lattice3(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_71]),c_0_70])])).

cnf(c_0_106,negated_conjecture,
    ( v5_orders_2(k7_lattice3(esk1_0))
    | ~ v5_orders_2(k7_lattice3(k7_lattice3(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_71]),c_0_70])])).

cnf(c_0_107,negated_conjecture,
    ( v1_lattice3(k7_lattice3(esk1_0))
    | ~ v2_lattice3(k7_lattice3(k7_lattice3(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_71]),c_0_70])])).

cnf(c_0_108,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(esk1_0))))
    | ~ v2_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v1_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v5_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v4_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_33]),c_0_103]),c_0_34])]),c_0_104]),c_0_105]),c_0_106]),c_0_107])).

cnf(c_0_109,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(esk1_0))))
    | ~ v2_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v5_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v4_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_40]),c_0_103]),c_0_34])])).

cnf(c_0_110,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(esk1_0))))
    | ~ v2_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v5_orders_2(k7_lattice3(esk1_0))
    | ~ v4_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_50]),c_0_103])])).

cnf(c_0_111,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(esk1_0))))
    | ~ v2_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v4_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_50]),c_0_31]),c_0_51])])).

cnf(c_0_112,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(esk1_0))))
    | ~ v2_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_58]),c_0_103])])).

cnf(c_0_113,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(esk1_0))))
    | ~ v2_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_58]),c_0_31]),c_0_59])])).

cnf(c_0_114,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(esk1_0))))
    | ~ v2_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_67]),c_0_103])])).

cnf(c_0_115,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(esk1_0))))
    | ~ v2_lattice3(k7_lattice3(k7_lattice3(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_67]),c_0_31]),c_0_68])])).

cnf(c_0_116,plain,
    ( v2_lattice3(k7_lattice3(k7_lattice3(X1)))
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_40]),c_0_48])).

cnf(c_0_117,plain,
    ( v2_waybel_0(X1,k7_lattice3(X2))
    | v1_xboole_0(X1)
    | ~ v1_waybel_0(X1,X2)
    | ~ v12_waybel_0(X1,X2)
    | ~ v1_waybel_7(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ epred1_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_118,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(esk1_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_116]),c_0_31]),c_0_41])])).

cnf(c_0_119,plain,
    ( v13_waybel_0(X1,k7_lattice3(X2))
    | v1_xboole_0(X1)
    | ~ v1_waybel_0(X1,X2)
    | ~ v12_waybel_0(X1,X2)
    | ~ v1_waybel_7(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ epred1_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_120,plain,
    ( v2_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ epred1_1(k7_lattice3(esk1_0))
    | ~ v1_waybel_7(esk2_0,k7_lattice3(esk1_0))
    | ~ v12_waybel_0(esk2_0,k7_lattice3(esk1_0))
    | ~ v1_waybel_0(esk2_0,k7_lattice3(esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_118]),c_0_24])).

cnf(c_0_121,plain,
    ( v13_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ epred1_1(k7_lattice3(esk1_0))
    | ~ v1_waybel_7(esk2_0,k7_lattice3(esk1_0))
    | ~ v12_waybel_0(esk2_0,k7_lattice3(esk1_0))
    | ~ v1_waybel_0(esk2_0,k7_lattice3(esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_118]),c_0_24])).

cnf(c_0_122,plain,
    ( v2_waybel_7(X1,k7_lattice3(X2))
    | v1_xboole_0(X1)
    | ~ v1_waybel_0(X1,X2)
    | ~ v12_waybel_0(X1,X2)
    | ~ v1_waybel_7(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ epred1_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_123,plain,
    ( v2_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v1_waybel_7(esk2_0,k7_lattice3(esk1_0))
    | ~ v12_waybel_0(esk2_0,k7_lattice3(esk1_0))
    | ~ v1_waybel_0(esk2_0,k7_lattice3(esk1_0))
    | ~ v1_lattice3(k7_lattice3(esk1_0))
    | ~ v5_orders_2(k7_lattice3(esk1_0))
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_33]),c_0_103]),c_0_34])])).

cnf(c_0_124,negated_conjecture,
    ( v1_waybel_7(esk2_0,k7_lattice3(esk1_0))
    | v2_waybel_7(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_125,negated_conjecture,
    ( v1_waybel_0(esk2_0,k7_lattice3(esk1_0))
    | v2_waybel_7(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_126,negated_conjecture,
    ( v12_waybel_0(esk2_0,k7_lattice3(esk1_0))
    | v2_waybel_7(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_127,negated_conjecture,
    ( v1_waybel_7(esk2_0,k7_lattice3(esk1_0))
    | v2_waybel_0(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_128,negated_conjecture,
    ( v1_waybel_0(esk2_0,k7_lattice3(esk1_0))
    | v2_waybel_0(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_129,negated_conjecture,
    ( v12_waybel_0(esk2_0,k7_lattice3(esk1_0))
    | v2_waybel_0(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_130,negated_conjecture,
    ( v1_waybel_7(esk2_0,k7_lattice3(esk1_0))
    | v13_waybel_0(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_131,negated_conjecture,
    ( v1_waybel_0(esk2_0,k7_lattice3(esk1_0))
    | v13_waybel_0(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_132,negated_conjecture,
    ( v12_waybel_0(esk2_0,k7_lattice3(esk1_0))
    | v13_waybel_0(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_133,plain,
    ( v13_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v1_waybel_7(esk2_0,k7_lattice3(esk1_0))
    | ~ v12_waybel_0(esk2_0,k7_lattice3(esk1_0))
    | ~ v1_waybel_0(esk2_0,k7_lattice3(esk1_0))
    | ~ v1_lattice3(k7_lattice3(esk1_0))
    | ~ v5_orders_2(k7_lattice3(esk1_0))
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_33]),c_0_103]),c_0_34])])).

cnf(c_0_134,plain,
    ( v2_waybel_7(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ epred1_1(k7_lattice3(esk1_0))
    | ~ v1_waybel_7(esk2_0,k7_lattice3(esk1_0))
    | ~ v12_waybel_0(esk2_0,k7_lattice3(esk1_0))
    | ~ v1_waybel_0(esk2_0,k7_lattice3(esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_122,c_0_118]),c_0_24])).

cnf(c_0_135,negated_conjecture,
    ( v2_waybel_7(esk2_0,esk1_0)
    | v2_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v1_lattice3(k7_lattice3(esk1_0))
    | ~ v5_orders_2(k7_lattice3(esk1_0))
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(k7_lattice3(esk1_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_124]),c_0_125]),c_0_126])).

cnf(c_0_136,negated_conjecture,
    ( v2_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | v2_waybel_0(esk2_0,esk1_0)
    | ~ v1_lattice3(k7_lattice3(esk1_0))
    | ~ v5_orders_2(k7_lattice3(esk1_0))
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(k7_lattice3(esk1_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_127]),c_0_128]),c_0_129])).

cnf(c_0_137,negated_conjecture,
    ( v13_waybel_0(esk2_0,esk1_0)
    | v2_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v1_lattice3(k7_lattice3(esk1_0))
    | ~ v5_orders_2(k7_lattice3(esk1_0))
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(k7_lattice3(esk1_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_130]),c_0_131]),c_0_132])).

cnf(c_0_138,negated_conjecture,
    ( v2_waybel_7(esk2_0,esk1_0)
    | v13_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v1_lattice3(k7_lattice3(esk1_0))
    | ~ v5_orders_2(k7_lattice3(esk1_0))
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(k7_lattice3(esk1_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_133,c_0_124]),c_0_125]),c_0_126])).

cnf(c_0_139,negated_conjecture,
    ( v13_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | v2_waybel_0(esk2_0,esk1_0)
    | ~ v1_lattice3(k7_lattice3(esk1_0))
    | ~ v5_orders_2(k7_lattice3(esk1_0))
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(k7_lattice3(esk1_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_133,c_0_127]),c_0_128]),c_0_129])).

cnf(c_0_140,negated_conjecture,
    ( v13_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | v13_waybel_0(esk2_0,esk1_0)
    | ~ v1_lattice3(k7_lattice3(esk1_0))
    | ~ v5_orders_2(k7_lattice3(esk1_0))
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(k7_lattice3(esk1_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_133,c_0_130]),c_0_131]),c_0_132])).

cnf(c_0_141,plain,
    ( v2_waybel_7(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v1_waybel_7(esk2_0,k7_lattice3(esk1_0))
    | ~ v12_waybel_0(esk2_0,k7_lattice3(esk1_0))
    | ~ v1_waybel_0(esk2_0,k7_lattice3(esk1_0))
    | ~ v1_lattice3(k7_lattice3(esk1_0))
    | ~ v5_orders_2(k7_lattice3(esk1_0))
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134,c_0_33]),c_0_103]),c_0_34])])).

cnf(c_0_142,negated_conjecture,
    ( v2_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | v2_waybel_0(esk2_0,X1)
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != k7_lattice3(k7_lattice3(esk1_0))
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v1_lattice3(k7_lattice3(esk1_0))
    | ~ v1_lattice3(X1)
    | ~ v5_orders_2(k7_lattice3(esk1_0))
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_135]),c_0_136]),c_0_137])).

cnf(c_0_143,negated_conjecture,
    ( v13_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | v13_waybel_0(esk2_0,X1)
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != k7_lattice3(k7_lattice3(esk1_0))
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v1_lattice3(k7_lattice3(esk1_0))
    | ~ v1_lattice3(X1)
    | ~ v5_orders_2(k7_lattice3(esk1_0))
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_138]),c_0_139]),c_0_140])).

cnf(c_0_144,negated_conjecture,
    ( v2_waybel_7(X1,X2)
    | v1_xboole_0(X1)
    | g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) != k7_lattice3(k7_lattice3(esk1_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ v2_waybel_7(X1,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v13_waybel_0(X1,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v2_waybel_0(X1,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ l1_orders_2(X2)
    | ~ v2_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v2_lattice3(X2)
    | ~ v1_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v1_lattice3(X2)
    | ~ v5_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v5_orders_2(X2)
    | ~ v4_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v4_orders_2(X2)
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_77]),c_0_70])]),c_0_101]),c_0_54])).

cnf(c_0_145,negated_conjecture,
    ( v2_waybel_7(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | v2_waybel_0(esk2_0,esk1_0)
    | ~ v1_lattice3(k7_lattice3(esk1_0))
    | ~ v5_orders_2(k7_lattice3(esk1_0))
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(k7_lattice3(esk1_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_141,c_0_127]),c_0_128]),c_0_129])).

cnf(c_0_146,negated_conjecture,
    ( v2_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v2_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v1_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v5_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v4_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(ef,[status(thm)],[c_0_142]),c_0_77]),c_0_101]),c_0_54]),c_0_70])]),c_0_104]),c_0_105]),c_0_106]),c_0_107])).

cnf(c_0_147,negated_conjecture,
    ( v13_waybel_0(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v2_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v1_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v5_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v4_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(ef,[status(thm)],[c_0_143]),c_0_77]),c_0_101]),c_0_54]),c_0_70])]),c_0_104]),c_0_105]),c_0_106]),c_0_107])).

cnf(c_0_148,negated_conjecture,
    ( v2_waybel_7(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | v13_waybel_0(esk2_0,esk1_0)
    | ~ v1_lattice3(k7_lattice3(esk1_0))
    | ~ v5_orders_2(k7_lattice3(esk1_0))
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(k7_lattice3(esk1_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_141,c_0_130]),c_0_131]),c_0_132])).

cnf(c_0_149,negated_conjecture,
    ( v2_waybel_7(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | v2_waybel_7(esk2_0,esk1_0)
    | ~ v1_lattice3(k7_lattice3(esk1_0))
    | ~ v5_orders_2(k7_lattice3(esk1_0))
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(k7_lattice3(esk1_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_141,c_0_124]),c_0_125]),c_0_126])).

cnf(c_0_150,negated_conjecture,
    ( v2_waybel_0(X1,X2)
    | v1_xboole_0(X1)
    | g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) != k7_lattice3(k7_lattice3(esk1_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ v2_waybel_7(X1,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v13_waybel_0(X1,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v2_waybel_0(X1,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ l1_orders_2(X2)
    | ~ v2_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v2_lattice3(X2)
    | ~ v1_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v1_lattice3(X2)
    | ~ v5_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v5_orders_2(X2)
    | ~ v4_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v4_orders_2(X2)
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_77]),c_0_70])]),c_0_101]),c_0_54])).

cnf(c_0_151,negated_conjecture,
    ( v2_waybel_7(esk2_0,X1)
    | v2_waybel_0(esk2_0,esk1_0)
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != k7_lattice3(k7_lattice3(esk1_0))
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v2_lattice3(X1)
    | ~ v1_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v1_lattice3(X1)
    | ~ v5_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_144,c_0_145]),c_0_79])]),c_0_24]),c_0_104]),c_0_105]),c_0_106]),c_0_107]),c_0_146]),c_0_147])).

cnf(c_0_152,negated_conjecture,
    ( v13_waybel_0(X1,X2)
    | v1_xboole_0(X1)
    | g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) != k7_lattice3(k7_lattice3(esk1_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ v2_waybel_7(X1,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v13_waybel_0(X1,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v2_waybel_0(X1,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ l1_orders_2(X2)
    | ~ v2_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v2_lattice3(X2)
    | ~ v1_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v1_lattice3(X2)
    | ~ v5_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v5_orders_2(X2)
    | ~ v4_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v4_orders_2(X2)
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_77]),c_0_70])]),c_0_101]),c_0_54])).

cnf(c_0_153,negated_conjecture,
    ( v2_waybel_7(esk2_0,X1)
    | v13_waybel_0(esk2_0,esk1_0)
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != k7_lattice3(k7_lattice3(esk1_0))
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v2_lattice3(X1)
    | ~ v1_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v1_lattice3(X1)
    | ~ v5_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_144,c_0_148]),c_0_79])]),c_0_24]),c_0_104]),c_0_105]),c_0_106]),c_0_107]),c_0_146]),c_0_147])).

cnf(c_0_154,negated_conjecture,
    ( v2_waybel_7(esk2_0,esk1_0)
    | v2_waybel_7(esk2_0,X1)
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != k7_lattice3(k7_lattice3(esk1_0))
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v2_lattice3(X1)
    | ~ v1_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v1_lattice3(X1)
    | ~ v5_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_144,c_0_149]),c_0_79])]),c_0_24]),c_0_104]),c_0_105]),c_0_106]),c_0_107]),c_0_146]),c_0_147])).

cnf(c_0_155,negated_conjecture,
    ( v2_waybel_0(esk2_0,esk1_0)
    | v2_waybel_0(esk2_0,X1)
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != k7_lattice3(k7_lattice3(esk1_0))
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v2_lattice3(X1)
    | ~ v1_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v1_lattice3(X1)
    | ~ v5_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_150,c_0_151]),c_0_79]),c_0_77]),c_0_101]),c_0_54]),c_0_70])]),c_0_24]),c_0_146]),c_0_147])).

cnf(c_0_156,negated_conjecture,
    ( v13_waybel_0(esk2_0,esk1_0)
    | v13_waybel_0(esk2_0,X1)
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != k7_lattice3(k7_lattice3(esk1_0))
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v2_lattice3(X1)
    | ~ v1_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v1_lattice3(X1)
    | ~ v5_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_152,c_0_153]),c_0_79]),c_0_77]),c_0_101]),c_0_54]),c_0_70])]),c_0_24]),c_0_146]),c_0_147])).

cnf(c_0_157,negated_conjecture,
    ( v2_waybel_7(esk2_0,esk1_0)
    | ~ v2_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v1_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v5_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v4_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(ef,[status(thm)],[c_0_154]),c_0_54]),c_0_31]),c_0_41]),c_0_30]),c_0_51]),c_0_59]),c_0_68])])).

cnf(c_0_158,negated_conjecture,
    ( v2_waybel_0(esk2_0,esk1_0)
    | ~ v2_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v1_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v5_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v4_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(ef,[status(thm)],[c_0_155]),c_0_54]),c_0_31]),c_0_41]),c_0_30]),c_0_51]),c_0_59]),c_0_68])])).

cnf(c_0_159,negated_conjecture,
    ( v13_waybel_0(esk2_0,esk1_0)
    | ~ v2_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v1_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v5_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v4_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(ef,[status(thm)],[c_0_156]),c_0_54]),c_0_31]),c_0_41]),c_0_30]),c_0_51]),c_0_59]),c_0_68])])).

cnf(c_0_160,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(X1)))
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != k7_lattice3(k7_lattice3(esk1_0))
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v2_lattice3(X1)
    | ~ v1_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v1_lattice3(X1)
    | ~ v5_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_157]),c_0_158]),c_0_159])).

cnf(c_0_161,plain,
    ( v1_waybel_7(X1,X2)
    | v1_xboole_0(X1)
    | ~ v2_waybel_0(X1,k7_lattice3(X2))
    | ~ v13_waybel_0(X1,k7_lattice3(X2))
    | ~ v2_waybel_7(X1,k7_lattice3(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X2))))
    | ~ epred1_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_162,negated_conjecture,
    ( v2_waybel_7(esk2_0,X1)
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != k7_lattice3(k7_lattice3(esk1_0))
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v2_lattice3(X1)
    | ~ v1_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v1_lattice3(X1)
    | ~ v5_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_157]),c_0_158]),c_0_159])).

cnf(c_0_163,negated_conjecture,
    ( v2_waybel_0(esk2_0,X1)
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != k7_lattice3(k7_lattice3(esk1_0))
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v2_lattice3(X1)
    | ~ v1_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v1_lattice3(X1)
    | ~ v5_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_157]),c_0_158]),c_0_159])).

cnf(c_0_164,negated_conjecture,
    ( v13_waybel_0(esk2_0,X1)
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != k7_lattice3(k7_lattice3(esk1_0))
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v2_lattice3(X1)
    | ~ v1_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v1_lattice3(X1)
    | ~ v5_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_157]),c_0_158]),c_0_159])).

cnf(c_0_165,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(X1)))
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != k7_lattice3(k7_lattice3(esk1_0))
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v2_lattice3(X1)
    | ~ v1_lattice3(X1)
    | ~ v5_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_160,c_0_40]),c_0_103]),c_0_34])])).

cnf(c_0_166,plain,
    ( v1_waybel_7(esk2_0,X1)
    | g1_orders_2(u1_struct_0(k7_lattice3(X1)),u1_orders_2(k7_lattice3(X1))) != k7_lattice3(k7_lattice3(esk1_0))
    | ~ epred1_1(X1)
    | ~ l1_orders_2(k7_lattice3(X1))
    | ~ v2_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v2_lattice3(k7_lattice3(X1))
    | ~ v1_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v1_lattice3(k7_lattice3(X1))
    | ~ v5_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v5_orders_2(k7_lattice3(X1))
    | ~ v4_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v4_orders_2(k7_lattice3(X1))
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(k7_lattice3(X1)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_161,c_0_162]),c_0_24]),c_0_163]),c_0_164]),c_0_165])).

cnf(c_0_167,plain,
    ( v12_waybel_0(X1,X2)
    | v1_xboole_0(X1)
    | ~ v2_waybel_0(X1,k7_lattice3(X2))
    | ~ v13_waybel_0(X1,k7_lattice3(X2))
    | ~ v2_waybel_7(X1,k7_lattice3(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X2))))
    | ~ epred1_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_168,plain,
    ( v1_waybel_7(esk2_0,X1)
    | g1_orders_2(u1_struct_0(k7_lattice3(X1)),u1_orders_2(k7_lattice3(X1))) != k7_lattice3(k7_lattice3(esk1_0))
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v2_lattice3(X1)
    | ~ v1_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v1_lattice3(X1)
    | ~ v5_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_166,c_0_33]),c_0_67]),c_0_58]),c_0_50]),c_0_40]),c_0_29]),c_0_48])).

cnf(c_0_169,plain,
    ( v12_waybel_0(esk2_0,X1)
    | g1_orders_2(u1_struct_0(k7_lattice3(X1)),u1_orders_2(k7_lattice3(X1))) != k7_lattice3(k7_lattice3(esk1_0))
    | ~ epred1_1(X1)
    | ~ l1_orders_2(k7_lattice3(X1))
    | ~ v2_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v2_lattice3(k7_lattice3(X1))
    | ~ v1_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v1_lattice3(k7_lattice3(X1))
    | ~ v5_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v5_orders_2(k7_lattice3(X1))
    | ~ v4_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v4_orders_2(k7_lattice3(X1))
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(k7_lattice3(X1)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_167,c_0_162]),c_0_24]),c_0_163]),c_0_164]),c_0_165])).

cnf(c_0_170,plain,
    ( v1_waybel_0(X1,X2)
    | v1_xboole_0(X1)
    | ~ v2_waybel_0(X1,k7_lattice3(X2))
    | ~ v13_waybel_0(X1,k7_lattice3(X2))
    | ~ v2_waybel_7(X1,k7_lattice3(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X2))))
    | ~ epred1_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_171,negated_conjecture,
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
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_172,plain,
    ( v2_waybel_7(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v12_waybel_0(esk2_0,k7_lattice3(esk1_0))
    | ~ v1_waybel_0(esk2_0,k7_lattice3(esk1_0))
    | ~ v2_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v1_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v5_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v4_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_141,c_0_168]),c_0_77]),c_0_101]),c_0_54]),c_0_103]),c_0_34])]),c_0_104]),c_0_105]),c_0_106]),c_0_107])).

cnf(c_0_173,plain,
    ( v12_waybel_0(esk2_0,X1)
    | g1_orders_2(u1_struct_0(k7_lattice3(X1)),u1_orders_2(k7_lattice3(X1))) != k7_lattice3(k7_lattice3(esk1_0))
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v2_lattice3(X1)
    | ~ v1_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v1_lattice3(X1)
    | ~ v5_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_169,c_0_33]),c_0_67]),c_0_58]),c_0_50]),c_0_40]),c_0_29]),c_0_48])).

cnf(c_0_174,plain,
    ( v1_waybel_0(esk2_0,X1)
    | g1_orders_2(u1_struct_0(k7_lattice3(X1)),u1_orders_2(k7_lattice3(X1))) != k7_lattice3(k7_lattice3(esk1_0))
    | ~ epred1_1(X1)
    | ~ l1_orders_2(k7_lattice3(X1))
    | ~ v2_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v2_lattice3(k7_lattice3(X1))
    | ~ v1_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v1_lattice3(k7_lattice3(X1))
    | ~ v5_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v5_orders_2(k7_lattice3(X1))
    | ~ v4_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v4_orders_2(k7_lattice3(X1))
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(k7_lattice3(X1)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_170,c_0_162]),c_0_24]),c_0_163]),c_0_164]),c_0_165])).

cnf(c_0_175,negated_conjecture,
    ( v1_xboole_0(esk2_0)
    | ~ v2_waybel_0(esk2_0,esk1_0)
    | ~ v13_waybel_0(esk2_0,esk1_0)
    | ~ v2_waybel_7(esk2_0,esk1_0)
    | ~ v1_waybel_0(esk2_0,k7_lattice3(esk1_0))
    | ~ v12_waybel_0(esk2_0,k7_lattice3(esk1_0))
    | ~ v1_waybel_7(esk2_0,k7_lattice3(esk1_0))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(esk1_0)))) ),
    inference(cn,[status(thm)],[c_0_171])).

cnf(c_0_176,plain,
    ( v2_waybel_7(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v1_waybel_0(esk2_0,k7_lattice3(esk1_0))
    | ~ v2_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v1_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v5_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v4_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_172,c_0_173]),c_0_77]),c_0_101]),c_0_54]),c_0_103]),c_0_34])]),c_0_104]),c_0_105]),c_0_106]),c_0_107])).

cnf(c_0_177,plain,
    ( v1_waybel_0(esk2_0,X1)
    | g1_orders_2(u1_struct_0(k7_lattice3(X1)),u1_orders_2(k7_lattice3(X1))) != k7_lattice3(k7_lattice3(esk1_0))
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v2_lattice3(X1)
    | ~ v1_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v1_lattice3(X1)
    | ~ v5_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_174,c_0_33]),c_0_67]),c_0_58]),c_0_50]),c_0_40]),c_0_29]),c_0_48])).

cnf(c_0_178,negated_conjecture,
    ( ~ v1_waybel_7(esk2_0,k7_lattice3(esk1_0))
    | ~ v12_waybel_0(esk2_0,k7_lattice3(esk1_0))
    | ~ v1_waybel_0(esk2_0,k7_lattice3(esk1_0))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(esk1_0))))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ v2_waybel_7(esk2_0,esk1_0)
    | ~ v13_waybel_0(esk2_0,esk1_0)
    | ~ v2_waybel_0(esk2_0,esk1_0) ),
    inference(sr,[status(thm)],[c_0_175,c_0_24])).

cnf(c_0_179,plain,
    ( v2_waybel_7(esk2_0,k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v2_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v1_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v5_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v4_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_176,c_0_177]),c_0_77]),c_0_101]),c_0_54]),c_0_103]),c_0_34])]),c_0_104]),c_0_105]),c_0_106]),c_0_107])).

cnf(c_0_180,negated_conjecture,
    ( ~ v1_waybel_7(esk2_0,k7_lattice3(esk1_0))
    | ~ v12_waybel_0(esk2_0,k7_lattice3(esk1_0))
    | ~ v1_waybel_0(esk2_0,k7_lattice3(esk1_0))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(esk1_0))))
    | ~ v2_waybel_7(esk2_0,esk1_0)
    | ~ v13_waybel_0(esk2_0,esk1_0)
    | ~ v2_waybel_0(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_178,c_0_79])])).

cnf(c_0_181,plain,
    ( v1_waybel_7(esk2_0,k7_lattice3(esk1_0))
    | ~ epred1_1(k7_lattice3(esk1_0))
    | ~ v2_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v1_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v5_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v4_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_161,c_0_179]),c_0_77]),c_0_79])]),c_0_24]),c_0_146]),c_0_147])).

cnf(c_0_182,plain,
    ( v1_waybel_0(esk2_0,k7_lattice3(esk1_0))
    | ~ epred1_1(k7_lattice3(esk1_0))
    | ~ v2_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v1_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v5_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v4_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_170,c_0_179]),c_0_77]),c_0_79])]),c_0_24]),c_0_146]),c_0_147])).

cnf(c_0_183,plain,
    ( v12_waybel_0(esk2_0,k7_lattice3(esk1_0))
    | ~ epred1_1(k7_lattice3(esk1_0))
    | ~ v2_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v1_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v5_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v4_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_167,c_0_179]),c_0_77]),c_0_79])]),c_0_24]),c_0_146]),c_0_147])).

cnf(c_0_184,negated_conjecture,
    ( ~ v1_waybel_7(esk2_0,k7_lattice3(esk1_0))
    | ~ v12_waybel_0(esk2_0,k7_lattice3(esk1_0))
    | ~ v1_waybel_0(esk2_0,k7_lattice3(esk1_0))
    | ~ v2_waybel_7(esk2_0,esk1_0)
    | ~ v13_waybel_0(esk2_0,esk1_0)
    | ~ v2_waybel_0(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_180,c_0_118])])).

cnf(c_0_185,plain,
    ( v1_waybel_7(esk2_0,k7_lattice3(esk1_0))
    | ~ v2_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v1_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v5_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v4_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_181,c_0_33]),c_0_103]),c_0_34])]),c_0_104]),c_0_105]),c_0_106]),c_0_107])).

cnf(c_0_186,plain,
    ( v1_waybel_0(esk2_0,k7_lattice3(esk1_0))
    | ~ v2_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v1_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v5_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v4_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_182,c_0_33]),c_0_103]),c_0_34])]),c_0_104]),c_0_105]),c_0_106]),c_0_107])).

cnf(c_0_187,plain,
    ( v12_waybel_0(esk2_0,k7_lattice3(esk1_0))
    | ~ v2_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v1_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v5_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v4_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_183,c_0_33]),c_0_103]),c_0_34])]),c_0_104]),c_0_105]),c_0_106]),c_0_107])).

cnf(c_0_188,negated_conjecture,
    ( ~ v2_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v1_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v5_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v4_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_184,c_0_185]),c_0_158]),c_0_159]),c_0_157]),c_0_186]),c_0_187])).

cnf(c_0_189,negated_conjecture,
    ( ~ v2_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v5_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v4_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_188,c_0_40]),c_0_103]),c_0_34])])).

cnf(c_0_190,negated_conjecture,
    ( ~ v2_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v5_orders_2(k7_lattice3(esk1_0))
    | ~ v4_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_189,c_0_50]),c_0_103])])).

cnf(c_0_191,negated_conjecture,
    ( ~ v2_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v4_orders_2(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_190,c_0_50]),c_0_31]),c_0_51])])).

cnf(c_0_192,negated_conjecture,
    ( ~ v2_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v4_orders_2(k7_lattice3(esk1_0))
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_191,c_0_58]),c_0_103])])).

cnf(c_0_193,negated_conjecture,
    ( ~ v2_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_192,c_0_58]),c_0_31]),c_0_59])])).

cnf(c_0_194,negated_conjecture,
    ( ~ v2_lattice3(k7_lattice3(k7_lattice3(esk1_0)))
    | ~ v3_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_193,c_0_67]),c_0_103])])).

cnf(c_0_195,negated_conjecture,
    ( ~ v2_lattice3(k7_lattice3(k7_lattice3(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_194,c_0_67]),c_0_31]),c_0_68])])).

cnf(c_0_196,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_195,c_0_116]),c_0_31]),c_0_41])]),
    [proof]).
%------------------------------------------------------------------------------
