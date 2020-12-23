%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1976+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:06 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  104 (4856 expanded)
%              Number of clauses        :   75 (2097 expanded)
%              Number of leaves         :   14 (1338 expanded)
%              Depth                    :   17
%              Number of atoms          :  427 (12893 expanded)
%              Number of equality atoms :   33 (3136 expanded)
%              Maximal formula depth    :   20 (   4 average)
%              Maximal clause size      :   54 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t25_waybel_7,conjecture,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X2)
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) )
     => ( v2_waybel_7(X2,k3_yellow_1(X1))
      <=> ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(X1))
           => ( r2_hidden(X3,X2)
              | r2_hidden(k6_subset_1(X1,X3),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_waybel_7)).

fof(t4_yellow_1,axiom,(
    ! [X1] : k3_yellow_1(X1) = k2_yellow_1(k9_setfam_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_1)).

fof(redefinition_k9_setfam_1,axiom,(
    ! [X1] : k9_setfam_1(X1) = k1_zfmisc_1(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

fof(d1_yellow_1,axiom,(
    ! [X1] : k2_yellow_1(X1) = g1_orders_2(X1,k1_yellow_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_yellow_1)).

fof(fc7_yellow_1,axiom,(
    ! [X1] :
      ( ~ v2_struct_0(k3_yellow_1(X1))
      & v1_orders_2(k3_yellow_1(X1))
      & v3_orders_2(k3_yellow_1(X1))
      & v4_orders_2(k3_yellow_1(X1))
      & v5_orders_2(k3_yellow_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_yellow_1)).

fof(fc1_waybel_7,axiom,(
    ! [X1] :
      ( v1_orders_2(k3_yellow_1(X1))
      & v11_waybel_1(k3_yellow_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_waybel_7)).

fof(dt_k2_yellow_1,axiom,(
    ! [X1] :
      ( v1_orders_2(k2_yellow_1(X1))
      & l1_orders_2(k2_yellow_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(t24_waybel_7,axiom,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & v11_waybel_1(X1)
        & v1_lattice3(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v2_waybel_0(X2,X1)
            & v13_waybel_0(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => ( v2_waybel_7(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ( r2_hidden(X3,X2)
                  | r2_hidden(k7_waybel_1(X1,X3),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_waybel_7)).

fof(free_g1_orders_2,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
     => ! [X3,X4] :
          ( g1_orders_2(X1,X2) = g1_orders_2(X3,X4)
         => ( X1 = X3
            & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_orders_2)).

fof(abstractness_v1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v1_orders_2(X1)
       => X1 = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_orders_2)).

fof(cc8_waybel_1,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( ( ~ v2_struct_0(X1)
          & v11_waybel_1(X1) )
       => ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & v1_lattice3(X1)
          & v2_lattice3(X1)
          & v3_yellow_0(X1)
          & v2_waybel_1(X1)
          & v10_waybel_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc8_waybel_1)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(dt_k1_yellow_1,axiom,(
    ! [X1] :
      ( v1_relat_2(k1_yellow_1(X1))
      & v4_relat_2(k1_yellow_1(X1))
      & v8_relat_2(k1_yellow_1(X1))
      & v1_partfun1(k1_yellow_1(X1),X1)
      & m1_subset_1(k1_yellow_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_yellow_1)).

fof(t9_waybel_7,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
     => k7_waybel_1(k3_yellow_1(X1),X2) = k6_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_waybel_7)).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( ~ v1_xboole_0(X2)
          & v2_waybel_0(X2,k3_yellow_1(X1))
          & v13_waybel_0(X2,k3_yellow_1(X1))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) )
       => ( v2_waybel_7(X2,k3_yellow_1(X1))
        <=> ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(X1))
             => ( r2_hidden(X3,X2)
                | r2_hidden(k6_subset_1(X1,X3),X2) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t25_waybel_7])).

fof(c_0_15,plain,(
    ! [X21] : k3_yellow_1(X21) = k2_yellow_1(k9_setfam_1(X21)) ),
    inference(variable_rename,[status(thm)],[t4_yellow_1])).

fof(c_0_16,plain,(
    ! [X16] : k9_setfam_1(X16) = k1_zfmisc_1(X16) ),
    inference(variable_rename,[status(thm)],[redefinition_k9_setfam_1])).

fof(c_0_17,negated_conjecture,(
    ! [X29] :
      ( ~ v1_xboole_0(esk3_0)
      & v2_waybel_0(esk3_0,k3_yellow_1(esk2_0))
      & v13_waybel_0(esk3_0,k3_yellow_1(esk2_0))
      & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(esk2_0))))
      & ( m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))
        | ~ v2_waybel_7(esk3_0,k3_yellow_1(esk2_0)) )
      & ( ~ r2_hidden(esk4_0,esk3_0)
        | ~ v2_waybel_7(esk3_0,k3_yellow_1(esk2_0)) )
      & ( ~ r2_hidden(k6_subset_1(esk2_0,esk4_0),esk3_0)
        | ~ v2_waybel_7(esk3_0,k3_yellow_1(esk2_0)) )
      & ( v2_waybel_7(esk3_0,k3_yellow_1(esk2_0))
        | ~ m1_subset_1(X29,k1_zfmisc_1(esk2_0))
        | r2_hidden(X29,esk3_0)
        | r2_hidden(k6_subset_1(esk2_0,X29),esk3_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])])])).

cnf(c_0_18,plain,
    ( k3_yellow_1(X1) = k2_yellow_1(k9_setfam_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,plain,
    ( k9_setfam_1(X1) = k1_zfmisc_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_20,plain,(
    ! [X7] : k2_yellow_1(X7) = g1_orders_2(X7,k1_yellow_1(X7)) ),
    inference(variable_rename,[status(thm)],[d1_yellow_1])).

fof(c_0_21,plain,(
    ! [X11] :
      ( ~ v2_struct_0(k3_yellow_1(X11))
      & v1_orders_2(k3_yellow_1(X11))
      & v3_orders_2(k3_yellow_1(X11))
      & v4_orders_2(k3_yellow_1(X11))
      & v5_orders_2(k3_yellow_1(X11)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc7_yellow_1])])).

fof(c_0_22,plain,(
    ! [X10] :
      ( v1_orders_2(k3_yellow_1(X10))
      & v11_waybel_1(k3_yellow_1(X10)) ) ),
    inference(variable_rename,[status(thm)],[fc1_waybel_7])).

fof(c_0_23,plain,(
    ! [X9] :
      ( v1_orders_2(k2_yellow_1(X9))
      & l1_orders_2(k2_yellow_1(X9)) ) ),
    inference(variable_rename,[status(thm)],[dt_k2_yellow_1])).

fof(c_0_24,plain,(
    ! [X17,X18,X19] :
      ( ( ~ v2_waybel_7(X18,X17)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | r2_hidden(X19,X18)
        | r2_hidden(k7_waybel_1(X17,X19),X18)
        | v1_xboole_0(X18)
        | ~ v2_waybel_0(X18,X17)
        | ~ v13_waybel_0(X18,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ v3_orders_2(X17)
        | ~ v4_orders_2(X17)
        | ~ v5_orders_2(X17)
        | ~ v11_waybel_1(X17)
        | ~ v1_lattice3(X17)
        | ~ v2_lattice3(X17)
        | ~ l1_orders_2(X17) )
      & ( m1_subset_1(esk1_2(X17,X18),u1_struct_0(X17))
        | v2_waybel_7(X18,X17)
        | v1_xboole_0(X18)
        | ~ v2_waybel_0(X18,X17)
        | ~ v13_waybel_0(X18,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ v3_orders_2(X17)
        | ~ v4_orders_2(X17)
        | ~ v5_orders_2(X17)
        | ~ v11_waybel_1(X17)
        | ~ v1_lattice3(X17)
        | ~ v2_lattice3(X17)
        | ~ l1_orders_2(X17) )
      & ( ~ r2_hidden(esk1_2(X17,X18),X18)
        | v2_waybel_7(X18,X17)
        | v1_xboole_0(X18)
        | ~ v2_waybel_0(X18,X17)
        | ~ v13_waybel_0(X18,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ v3_orders_2(X17)
        | ~ v4_orders_2(X17)
        | ~ v5_orders_2(X17)
        | ~ v11_waybel_1(X17)
        | ~ v1_lattice3(X17)
        | ~ v2_lattice3(X17)
        | ~ l1_orders_2(X17) )
      & ( ~ r2_hidden(k7_waybel_1(X17,esk1_2(X17,X18)),X18)
        | v2_waybel_7(X18,X17)
        | v1_xboole_0(X18)
        | ~ v2_waybel_0(X18,X17)
        | ~ v13_waybel_0(X18,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ v3_orders_2(X17)
        | ~ v4_orders_2(X17)
        | ~ v5_orders_2(X17)
        | ~ v11_waybel_1(X17)
        | ~ v1_lattice3(X17)
        | ~ v2_lattice3(X17)
        | ~ l1_orders_2(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_waybel_7])])])])])])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( k3_yellow_1(X1) = k2_yellow_1(k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_27,plain,
    ( k2_yellow_1(X1) = g1_orders_2(X1,k1_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( v13_waybel_0(esk3_0,k3_yellow_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_29,negated_conjecture,
    ( v2_waybel_0(esk3_0,k3_yellow_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_30,plain,
    ( v5_orders_2(k3_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( v4_orders_2(k3_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,plain,
    ( v3_orders_2(k3_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_33,plain,
    ( v11_waybel_1(k3_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_34,plain,
    ( l1_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_35,plain,(
    ! [X12,X13,X14,X15] :
      ( ( X12 = X14
        | g1_orders_2(X12,X13) != g1_orders_2(X14,X15)
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X12,X12))) )
      & ( X13 = X15
        | g1_orders_2(X12,X13) != g1_orders_2(X14,X15)
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X12,X12))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_orders_2])])])])).

fof(c_0_36,plain,(
    ! [X5] :
      ( ~ l1_orders_2(X5)
      | ~ v1_orders_2(X5)
      | X5 = g1_orders_2(u1_struct_0(X5),u1_orders_2(X5)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_orders_2])])).

cnf(c_0_37,plain,
    ( m1_subset_1(esk1_2(X1,X2),u1_struct_0(X1))
    | v2_waybel_7(X2,X1)
    | v1_xboole_0(X2)
    | ~ v2_waybel_0(X2,X1)
    | ~ v13_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v11_waybel_1(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(g1_orders_2(k1_zfmisc_1(esk2_0),k1_yellow_1(k1_zfmisc_1(esk2_0)))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_26]),c_0_27])).

cnf(c_0_39,negated_conjecture,
    ( v13_waybel_0(esk3_0,g1_orders_2(k1_zfmisc_1(esk2_0),k1_yellow_1(k1_zfmisc_1(esk2_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_26]),c_0_27])).

cnf(c_0_40,negated_conjecture,
    ( v2_waybel_0(esk3_0,g1_orders_2(k1_zfmisc_1(esk2_0),k1_yellow_1(k1_zfmisc_1(esk2_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_26]),c_0_27])).

cnf(c_0_41,plain,
    ( v5_orders_2(g1_orders_2(k1_zfmisc_1(X1),k1_yellow_1(k1_zfmisc_1(X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_26]),c_0_27])).

cnf(c_0_42,plain,
    ( v4_orders_2(g1_orders_2(k1_zfmisc_1(X1),k1_yellow_1(k1_zfmisc_1(X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_26]),c_0_27])).

cnf(c_0_43,plain,
    ( v3_orders_2(g1_orders_2(k1_zfmisc_1(X1),k1_yellow_1(k1_zfmisc_1(X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_26]),c_0_27])).

cnf(c_0_44,plain,
    ( v11_waybel_1(g1_orders_2(k1_zfmisc_1(X1),k1_yellow_1(k1_zfmisc_1(X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_26]),c_0_27])).

cnf(c_0_45,plain,
    ( l1_orders_2(g1_orders_2(X1,k1_yellow_1(X1))) ),
    inference(rw,[status(thm)],[c_0_34,c_0_27])).

cnf(c_0_46,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_47,plain,(
    ! [X6] :
      ( ( ~ v2_struct_0(X6)
        | v2_struct_0(X6)
        | ~ v11_waybel_1(X6)
        | ~ l1_orders_2(X6) )
      & ( v3_orders_2(X6)
        | v2_struct_0(X6)
        | ~ v11_waybel_1(X6)
        | ~ l1_orders_2(X6) )
      & ( v4_orders_2(X6)
        | v2_struct_0(X6)
        | ~ v11_waybel_1(X6)
        | ~ l1_orders_2(X6) )
      & ( v5_orders_2(X6)
        | v2_struct_0(X6)
        | ~ v11_waybel_1(X6)
        | ~ l1_orders_2(X6) )
      & ( v1_lattice3(X6)
        | v2_struct_0(X6)
        | ~ v11_waybel_1(X6)
        | ~ l1_orders_2(X6) )
      & ( v2_lattice3(X6)
        | v2_struct_0(X6)
        | ~ v11_waybel_1(X6)
        | ~ l1_orders_2(X6) )
      & ( v3_yellow_0(X6)
        | v2_struct_0(X6)
        | ~ v11_waybel_1(X6)
        | ~ l1_orders_2(X6) )
      & ( v2_waybel_1(X6)
        | v2_struct_0(X6)
        | ~ v11_waybel_1(X6)
        | ~ l1_orders_2(X6) )
      & ( v10_waybel_1(X6)
        | v2_struct_0(X6)
        | ~ v11_waybel_1(X6)
        | ~ l1_orders_2(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc8_waybel_1])])])])).

cnf(c_0_48,plain,
    ( ~ v2_struct_0(k3_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_49,plain,
    ( X1 = X2
    | g1_orders_2(X1,X3) != g1_orders_2(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_50,plain,
    ( X1 = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | ~ l1_orders_2(X1)
    | ~ v1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_51,plain,(
    ! [X22,X23] :
      ( ~ r2_hidden(X22,X23)
      | ~ v1_xboole_0(X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_52,negated_conjecture,
    ( v2_waybel_7(esk3_0,g1_orders_2(k1_zfmisc_1(esk2_0),k1_yellow_1(k1_zfmisc_1(esk2_0))))
    | m1_subset_1(esk1_2(g1_orders_2(k1_zfmisc_1(esk2_0),k1_yellow_1(k1_zfmisc_1(esk2_0))),esk3_0),u1_struct_0(g1_orders_2(k1_zfmisc_1(esk2_0),k1_yellow_1(k1_zfmisc_1(esk2_0)))))
    | ~ v2_lattice3(g1_orders_2(k1_zfmisc_1(esk2_0),k1_yellow_1(k1_zfmisc_1(esk2_0))))
    | ~ v1_lattice3(g1_orders_2(k1_zfmisc_1(esk2_0),k1_yellow_1(k1_zfmisc_1(esk2_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39]),c_0_40]),c_0_41]),c_0_42]),c_0_43]),c_0_44]),c_0_45])]),c_0_46])).

cnf(c_0_53,plain,
    ( v2_lattice3(X1)
    | v2_struct_0(X1)
    | ~ v11_waybel_1(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_54,plain,
    ( ~ v2_struct_0(g1_orders_2(k1_zfmisc_1(X1),k1_yellow_1(k1_zfmisc_1(X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_26]),c_0_27])).

cnf(c_0_55,plain,
    ( X1 = u1_struct_0(X2)
    | g1_orders_2(X1,X3) != X2
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_56,plain,
    ( v1_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_57,plain,(
    ! [X8] :
      ( v1_relat_2(k1_yellow_1(X8))
      & v4_relat_2(k1_yellow_1(X8))
      & v8_relat_2(k1_yellow_1(X8))
      & v1_partfun1(k1_yellow_1(X8),X8)
      & m1_subset_1(k1_yellow_1(X8),k1_zfmisc_1(k2_zfmisc_1(X8,X8))) ) ),
    inference(variable_rename,[status(thm)],[dt_k1_yellow_1])).

cnf(c_0_58,plain,
    ( v2_waybel_7(X2,X1)
    | v1_xboole_0(X2)
    | ~ r2_hidden(k7_waybel_1(X1,esk1_2(X1,X2)),X2)
    | ~ v2_waybel_0(X2,X1)
    | ~ v13_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v11_waybel_1(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_59,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_60,negated_conjecture,
    ( v2_waybel_7(esk3_0,g1_orders_2(k1_zfmisc_1(esk2_0),k1_yellow_1(k1_zfmisc_1(esk2_0))))
    | m1_subset_1(esk1_2(g1_orders_2(k1_zfmisc_1(esk2_0),k1_yellow_1(k1_zfmisc_1(esk2_0))),esk3_0),u1_struct_0(g1_orders_2(k1_zfmisc_1(esk2_0),k1_yellow_1(k1_zfmisc_1(esk2_0)))))
    | ~ v1_lattice3(g1_orders_2(k1_zfmisc_1(esk2_0),k1_yellow_1(k1_zfmisc_1(esk2_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_44]),c_0_45])]),c_0_54])).

cnf(c_0_61,plain,
    ( v1_lattice3(X1)
    | v2_struct_0(X1)
    | ~ v11_waybel_1(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_62,plain,
    ( u1_struct_0(g1_orders_2(X1,X2)) = X1
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_orders_2(g1_orders_2(X1,X2))
    | ~ l1_orders_2(g1_orders_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_55])).

cnf(c_0_63,plain,
    ( v1_orders_2(g1_orders_2(X1,k1_yellow_1(X1))) ),
    inference(rw,[status(thm)],[c_0_56,c_0_27])).

cnf(c_0_64,plain,
    ( m1_subset_1(k1_yellow_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

fof(c_0_65,plain,(
    ! [X24,X25] :
      ( ~ m1_subset_1(X25,u1_struct_0(k3_yellow_1(X24)))
      | k7_waybel_1(k3_yellow_1(X24),X25) = k6_subset_1(X24,X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_waybel_7])])).

cnf(c_0_66,plain,
    ( v2_waybel_7(X1,X2)
    | ~ r2_hidden(k7_waybel_1(X2,esk1_2(X2,X1)),X1)
    | ~ v13_waybel_0(X1,X2)
    | ~ v2_waybel_0(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_lattice3(X2)
    | ~ v1_lattice3(X2)
    | ~ v5_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v3_orders_2(X2)
    | ~ v11_waybel_1(X2)
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_67,negated_conjecture,
    ( v2_waybel_7(esk3_0,k3_yellow_1(esk2_0))
    | r2_hidden(X1,esk3_0)
    | r2_hidden(k6_subset_1(esk2_0,X1),esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_68,negated_conjecture,
    ( v2_waybel_7(esk3_0,g1_orders_2(k1_zfmisc_1(esk2_0),k1_yellow_1(k1_zfmisc_1(esk2_0))))
    | m1_subset_1(esk1_2(g1_orders_2(k1_zfmisc_1(esk2_0),k1_yellow_1(k1_zfmisc_1(esk2_0))),esk3_0),u1_struct_0(g1_orders_2(k1_zfmisc_1(esk2_0),k1_yellow_1(k1_zfmisc_1(esk2_0))))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_44]),c_0_45])]),c_0_54])).

cnf(c_0_69,plain,
    ( u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64]),c_0_45])])).

cnf(c_0_70,plain,
    ( k7_waybel_1(k3_yellow_1(X2),X1) = k6_subset_1(X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_71,negated_conjecture,
    ( v2_waybel_7(esk3_0,g1_orders_2(k1_zfmisc_1(esk2_0),k1_yellow_1(k1_zfmisc_1(esk2_0))))
    | ~ r2_hidden(k7_waybel_1(g1_orders_2(k1_zfmisc_1(esk2_0),k1_yellow_1(k1_zfmisc_1(esk2_0))),esk1_2(g1_orders_2(k1_zfmisc_1(esk2_0),k1_yellow_1(k1_zfmisc_1(esk2_0))),esk3_0)),esk3_0)
    | ~ v2_lattice3(g1_orders_2(k1_zfmisc_1(esk2_0),k1_yellow_1(k1_zfmisc_1(esk2_0))))
    | ~ v1_lattice3(g1_orders_2(k1_zfmisc_1(esk2_0),k1_yellow_1(k1_zfmisc_1(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_38]),c_0_39]),c_0_40]),c_0_41]),c_0_42]),c_0_43]),c_0_44]),c_0_45])])).

cnf(c_0_72,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | r2_hidden(k6_subset_1(esk2_0,X1),esk3_0)
    | v2_waybel_7(esk3_0,g1_orders_2(k1_zfmisc_1(esk2_0),k1_yellow_1(k1_zfmisc_1(esk2_0))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk2_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_26]),c_0_27])).

cnf(c_0_73,negated_conjecture,
    ( v2_waybel_7(esk3_0,g1_orders_2(k1_zfmisc_1(esk2_0),k1_yellow_1(k1_zfmisc_1(esk2_0))))
    | m1_subset_1(esk1_2(g1_orders_2(k1_zfmisc_1(esk2_0),k1_yellow_1(k1_zfmisc_1(esk2_0))),esk3_0),k1_zfmisc_1(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_74,plain,
    ( k7_waybel_1(g1_orders_2(k1_zfmisc_1(X2),k1_yellow_1(k1_zfmisc_1(X2))),X1) = k6_subset_1(X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(k1_zfmisc_1(X2),k1_yellow_1(k1_zfmisc_1(X2))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_26]),c_0_26]),c_0_27]),c_0_27])).

cnf(c_0_75,negated_conjecture,
    ( v2_waybel_7(esk3_0,g1_orders_2(k1_zfmisc_1(esk2_0),k1_yellow_1(k1_zfmisc_1(esk2_0))))
    | ~ r2_hidden(k7_waybel_1(g1_orders_2(k1_zfmisc_1(esk2_0),k1_yellow_1(k1_zfmisc_1(esk2_0))),esk1_2(g1_orders_2(k1_zfmisc_1(esk2_0),k1_yellow_1(k1_zfmisc_1(esk2_0))),esk3_0)),esk3_0)
    | ~ v1_lattice3(g1_orders_2(k1_zfmisc_1(esk2_0),k1_yellow_1(k1_zfmisc_1(esk2_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_53]),c_0_44]),c_0_45])]),c_0_54])).

cnf(c_0_76,plain,
    ( v2_waybel_7(X2,X1)
    | v1_xboole_0(X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2)
    | ~ v2_waybel_0(X2,X1)
    | ~ v13_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v11_waybel_1(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_77,negated_conjecture,
    ( r2_hidden(k6_subset_1(esk2_0,esk1_2(g1_orders_2(k1_zfmisc_1(esk2_0),k1_yellow_1(k1_zfmisc_1(esk2_0))),esk3_0)),esk3_0)
    | r2_hidden(esk1_2(g1_orders_2(k1_zfmisc_1(esk2_0),k1_yellow_1(k1_zfmisc_1(esk2_0))),esk3_0),esk3_0)
    | v2_waybel_7(esk3_0,g1_orders_2(k1_zfmisc_1(esk2_0),k1_yellow_1(k1_zfmisc_1(esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_78,negated_conjecture,
    ( k6_subset_1(esk2_0,esk1_2(g1_orders_2(k1_zfmisc_1(esk2_0),k1_yellow_1(k1_zfmisc_1(esk2_0))),esk3_0)) = k7_waybel_1(g1_orders_2(k1_zfmisc_1(esk2_0),k1_yellow_1(k1_zfmisc_1(esk2_0))),esk1_2(g1_orders_2(k1_zfmisc_1(esk2_0),k1_yellow_1(k1_zfmisc_1(esk2_0))),esk3_0))
    | v2_waybel_7(esk3_0,g1_orders_2(k1_zfmisc_1(esk2_0),k1_yellow_1(k1_zfmisc_1(esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_74,c_0_68])).

cnf(c_0_79,negated_conjecture,
    ( v2_waybel_7(esk3_0,g1_orders_2(k1_zfmisc_1(esk2_0),k1_yellow_1(k1_zfmisc_1(esk2_0))))
    | ~ r2_hidden(k7_waybel_1(g1_orders_2(k1_zfmisc_1(esk2_0),k1_yellow_1(k1_zfmisc_1(esk2_0))),esk1_2(g1_orders_2(k1_zfmisc_1(esk2_0),k1_yellow_1(k1_zfmisc_1(esk2_0))),esk3_0)),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_61]),c_0_44]),c_0_45])]),c_0_54])).

cnf(c_0_80,plain,
    ( v2_waybel_7(X1,X2)
    | ~ r2_hidden(esk1_2(X2,X1),X1)
    | ~ v13_waybel_0(X1,X2)
    | ~ v2_waybel_0(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_lattice3(X2)
    | ~ v1_lattice3(X2)
    | ~ v5_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v3_orders_2(X2)
    | ~ v11_waybel_1(X2)
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[c_0_76,c_0_59])).

cnf(c_0_81,negated_conjecture,
    ( r2_hidden(esk1_2(g1_orders_2(k1_zfmisc_1(esk2_0),k1_yellow_1(k1_zfmisc_1(esk2_0))),esk3_0),esk3_0)
    | v2_waybel_7(esk3_0,g1_orders_2(k1_zfmisc_1(esk2_0),k1_yellow_1(k1_zfmisc_1(esk2_0)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_79])).

cnf(c_0_82,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0))) ),
    inference(rw,[status(thm)],[c_0_38,c_0_69])).

cnf(c_0_83,negated_conjecture,
    ( v2_waybel_7(esk3_0,g1_orders_2(k1_zfmisc_1(esk2_0),k1_yellow_1(k1_zfmisc_1(esk2_0))))
    | ~ v2_lattice3(g1_orders_2(k1_zfmisc_1(esk2_0),k1_yellow_1(k1_zfmisc_1(esk2_0))))
    | ~ v1_lattice3(g1_orders_2(k1_zfmisc_1(esk2_0),k1_yellow_1(k1_zfmisc_1(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_39]),c_0_40]),c_0_69]),c_0_82]),c_0_41]),c_0_42]),c_0_43]),c_0_44]),c_0_45])])).

cnf(c_0_84,plain,
    ( r2_hidden(X3,X1)
    | r2_hidden(k7_waybel_1(X2,X3),X1)
    | v1_xboole_0(X1)
    | ~ v2_waybel_7(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v2_waybel_0(X1,X2)
    | ~ v13_waybel_0(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ v11_waybel_1(X2)
    | ~ v1_lattice3(X2)
    | ~ v2_lattice3(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_85,negated_conjecture,
    ( v2_waybel_7(esk3_0,g1_orders_2(k1_zfmisc_1(esk2_0),k1_yellow_1(k1_zfmisc_1(esk2_0))))
    | ~ v1_lattice3(g1_orders_2(k1_zfmisc_1(esk2_0),k1_yellow_1(k1_zfmisc_1(esk2_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_53]),c_0_44]),c_0_45])]),c_0_54])).

cnf(c_0_86,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))
    | ~ v2_waybel_7(esk3_0,k3_yellow_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_87,plain,
    ( r2_hidden(k7_waybel_1(g1_orders_2(X1,k1_yellow_1(X1)),X2),X3)
    | r2_hidden(X2,X3)
    | v1_xboole_0(X3)
    | ~ v2_waybel_7(X3,g1_orders_2(X1,k1_yellow_1(X1)))
    | ~ v13_waybel_0(X3,g1_orders_2(X1,k1_yellow_1(X1)))
    | ~ v2_waybel_0(X3,g1_orders_2(X1,k1_yellow_1(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,X1)
    | ~ v2_lattice3(g1_orders_2(X1,k1_yellow_1(X1)))
    | ~ v1_lattice3(g1_orders_2(X1,k1_yellow_1(X1)))
    | ~ v5_orders_2(g1_orders_2(X1,k1_yellow_1(X1)))
    | ~ v4_orders_2(g1_orders_2(X1,k1_yellow_1(X1)))
    | ~ v3_orders_2(g1_orders_2(X1,k1_yellow_1(X1)))
    | ~ v11_waybel_1(g1_orders_2(X1,k1_yellow_1(X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_69]),c_0_45])])).

cnf(c_0_88,negated_conjecture,
    ( v2_waybel_7(esk3_0,g1_orders_2(k1_zfmisc_1(esk2_0),k1_yellow_1(k1_zfmisc_1(esk2_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_61]),c_0_44]),c_0_45])]),c_0_54])).

cnf(c_0_89,negated_conjecture,
    ( ~ r2_hidden(k6_subset_1(esk2_0,esk4_0),esk3_0)
    | ~ v2_waybel_7(esk3_0,k3_yellow_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_90,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))
    | ~ v2_waybel_7(esk3_0,g1_orders_2(k1_zfmisc_1(esk2_0),k1_yellow_1(k1_zfmisc_1(esk2_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_86,c_0_26]),c_0_27])).

cnf(c_0_91,negated_conjecture,
    ( r2_hidden(k7_waybel_1(g1_orders_2(k1_zfmisc_1(esk2_0),k1_yellow_1(k1_zfmisc_1(esk2_0))),X1),esk3_0)
    | r2_hidden(X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk2_0))
    | ~ v2_lattice3(g1_orders_2(k1_zfmisc_1(esk2_0),k1_yellow_1(k1_zfmisc_1(esk2_0))))
    | ~ v1_lattice3(g1_orders_2(k1_zfmisc_1(esk2_0),k1_yellow_1(k1_zfmisc_1(esk2_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_82]),c_0_88]),c_0_39]),c_0_40]),c_0_41]),c_0_42]),c_0_43]),c_0_44])]),c_0_46])).

cnf(c_0_92,negated_conjecture,
    ( ~ r2_hidden(k6_subset_1(esk2_0,esk4_0),esk3_0)
    | ~ v2_waybel_7(esk3_0,g1_orders_2(k1_zfmisc_1(esk2_0),k1_yellow_1(k1_zfmisc_1(esk2_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_89,c_0_26]),c_0_27])).

cnf(c_0_93,plain,
    ( k6_subset_1(X1,X2) = k7_waybel_1(g1_orders_2(k1_zfmisc_1(X1),k1_yellow_1(k1_zfmisc_1(X1))),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_74,c_0_69])).

cnf(c_0_94,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_90,c_0_88])])).

cnf(c_0_95,negated_conjecture,
    ( ~ r2_hidden(esk4_0,esk3_0)
    | ~ v2_waybel_7(esk3_0,k3_yellow_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_96,negated_conjecture,
    ( r2_hidden(k7_waybel_1(g1_orders_2(k1_zfmisc_1(esk2_0),k1_yellow_1(k1_zfmisc_1(esk2_0))),X1),esk3_0)
    | r2_hidden(X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk2_0))
    | ~ v1_lattice3(g1_orders_2(k1_zfmisc_1(esk2_0),k1_yellow_1(k1_zfmisc_1(esk2_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_53]),c_0_44]),c_0_45])]),c_0_54])).

cnf(c_0_97,negated_conjecture,
    ( ~ r2_hidden(k6_subset_1(esk2_0,esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_92,c_0_88])])).

cnf(c_0_98,negated_conjecture,
    ( k6_subset_1(esk2_0,esk4_0) = k7_waybel_1(g1_orders_2(k1_zfmisc_1(esk2_0),k1_yellow_1(k1_zfmisc_1(esk2_0))),esk4_0) ),
    inference(spm,[status(thm)],[c_0_93,c_0_94])).

cnf(c_0_99,negated_conjecture,
    ( ~ r2_hidden(esk4_0,esk3_0)
    | ~ v2_waybel_7(esk3_0,g1_orders_2(k1_zfmisc_1(esk2_0),k1_yellow_1(k1_zfmisc_1(esk2_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_95,c_0_26]),c_0_27])).

cnf(c_0_100,negated_conjecture,
    ( r2_hidden(k7_waybel_1(g1_orders_2(k1_zfmisc_1(esk2_0),k1_yellow_1(k1_zfmisc_1(esk2_0))),X1),esk3_0)
    | r2_hidden(X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_61]),c_0_44]),c_0_45])]),c_0_54])).

cnf(c_0_101,negated_conjecture,
    ( ~ r2_hidden(k7_waybel_1(g1_orders_2(k1_zfmisc_1(esk2_0),k1_yellow_1(k1_zfmisc_1(esk2_0))),esk4_0),esk3_0) ),
    inference(rw,[status(thm)],[c_0_97,c_0_98])).

cnf(c_0_102,negated_conjecture,
    ( ~ r2_hidden(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_99,c_0_88])])).

cnf(c_0_103,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_94]),c_0_101]),c_0_102]),
    [proof]).

%------------------------------------------------------------------------------
