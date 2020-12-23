%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:49 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 132 expanded)
%              Number of clauses        :   40 (  54 expanded)
%              Number of leaves         :   15 (  36 expanded)
%              Depth                    :    6
%              Number of atoms          :  218 ( 408 expanded)
%              Number of equality atoms :   20 (  60 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal clause size      :   25 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t4_waybel_7,axiom,(
    ! [X1] : u1_struct_0(k3_yellow_1(X1)) = k9_setfam_1(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_waybel_7)).

fof(d2_yellow_1,axiom,(
    ! [X1] : k3_yellow_1(X1) = k3_lattice3(k1_lattice3(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_yellow_1)).

fof(t2_yellow19,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
            & v2_waybel_0(X2,k3_yellow_1(X1))
            & v13_waybel_0(X2,k3_yellow_1(X1))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) )
         => ! [X3] :
              ~ ( r2_hidden(X3,X2)
                & v1_xboole_0(X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_yellow19)).

fof(t8_waybel_7,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & v1_yellow_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v2_waybel_0(X2,X1)
            & v13_waybel_0(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => ( v1_subset_1(X2,u1_struct_0(X1))
          <=> ~ r2_hidden(k3_yellow_0(X1),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_waybel_7)).

fof(redefinition_k9_setfam_1,axiom,(
    ! [X1] : k9_setfam_1(X1) = k1_zfmisc_1(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(fc3_yellow_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v13_lattices(X1)
        & l3_lattices(X1) )
     => ( v1_orders_2(k3_lattice3(X1))
        & v3_orders_2(k3_lattice3(X1))
        & v4_orders_2(k3_lattice3(X1))
        & v5_orders_2(k3_lattice3(X1))
        & v1_yellow_0(k3_lattice3(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_yellow_1)).

fof(t3_lattice3,axiom,(
    ! [X1] :
      ( v13_lattices(k1_lattice3(X1))
      & k5_lattices(k1_lattice3(X1)) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_lattice3)).

fof(fc2_lattice3,axiom,(
    ! [X1] :
      ( v3_lattices(k1_lattice3(X1))
      & v10_lattices(k1_lattice3(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_lattice3)).

fof(dt_k1_lattice3,axiom,(
    ! [X1] :
      ( v3_lattices(k1_lattice3(X1))
      & l3_lattices(k1_lattice3(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_lattice3)).

fof(fc1_lattice3,axiom,(
    ! [X1] :
      ( ~ v2_struct_0(k1_lattice3(X1))
      & v3_lattices(k1_lattice3(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_lattice3)).

fof(fc7_yellow_1,axiom,(
    ! [X1] :
      ( ~ v2_struct_0(k3_yellow_1(X1))
      & v1_orders_2(k3_yellow_1(X1))
      & v3_orders_2(k3_yellow_1(X1))
      & v4_orders_2(k3_yellow_1(X1))
      & v5_orders_2(k3_yellow_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_yellow_1)).

fof(dt_k3_yellow_1,axiom,(
    ! [X1] :
      ( v1_orders_2(k3_yellow_1(X1))
      & l1_orders_2(k3_yellow_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_yellow_1)).

fof(t18_yellow_1,axiom,(
    ! [X1] : k3_yellow_0(k3_yellow_1(X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_yellow_1)).

fof(c_0_15,plain,(
    ! [X17] : u1_struct_0(k3_yellow_1(X17)) = k9_setfam_1(X17) ),
    inference(variable_rename,[status(thm)],[t4_waybel_7])).

fof(c_0_16,plain,(
    ! [X12] : k3_yellow_1(X12) = k3_lattice3(k1_lattice3(X12)) ),
    inference(variable_rename,[status(thm)],[d2_yellow_1])).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ( ~ v1_xboole_0(X2)
              & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
              & v2_waybel_0(X2,k3_yellow_1(X1))
              & v13_waybel_0(X2,k3_yellow_1(X1))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) )
           => ! [X3] :
                ~ ( r2_hidden(X3,X2)
                  & v1_xboole_0(X3) ) ) ) ),
    inference(assume_negation,[status(cth)],[t2_yellow19])).

fof(c_0_18,plain,(
    ! [X18,X19] :
      ( ( ~ v1_subset_1(X19,u1_struct_0(X18))
        | ~ r2_hidden(k3_yellow_0(X18),X19)
        | v1_xboole_0(X19)
        | ~ v2_waybel_0(X19,X18)
        | ~ v13_waybel_0(X19,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | v2_struct_0(X18)
        | ~ v3_orders_2(X18)
        | ~ v4_orders_2(X18)
        | ~ v5_orders_2(X18)
        | ~ v1_yellow_0(X18)
        | ~ l1_orders_2(X18) )
      & ( r2_hidden(k3_yellow_0(X18),X19)
        | v1_subset_1(X19,u1_struct_0(X18))
        | v1_xboole_0(X19)
        | ~ v2_waybel_0(X19,X18)
        | ~ v13_waybel_0(X19,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | v2_struct_0(X18)
        | ~ v3_orders_2(X18)
        | ~ v4_orders_2(X18)
        | ~ v5_orders_2(X18)
        | ~ v1_yellow_0(X18)
        | ~ l1_orders_2(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t8_waybel_7])])])])])).

fof(c_0_19,plain,(
    ! [X7] : k9_setfam_1(X7) = k1_zfmisc_1(X7) ),
    inference(variable_rename,[status(thm)],[redefinition_k9_setfam_1])).

cnf(c_0_20,plain,
    ( u1_struct_0(k3_yellow_1(X1)) = k9_setfam_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( k3_yellow_1(X1) = k3_lattice3(k1_lattice3(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_22,plain,(
    ! [X4] :
      ( ~ v1_xboole_0(X4)
      | X4 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

fof(c_0_23,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0)
    & ~ v1_xboole_0(esk2_0)
    & v1_subset_1(esk2_0,u1_struct_0(k3_yellow_1(esk1_0)))
    & v2_waybel_0(esk2_0,k3_yellow_1(esk1_0))
    & v13_waybel_0(esk2_0,k3_yellow_1(esk1_0))
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(esk1_0))))
    & r2_hidden(esk3_0,esk2_0)
    & v1_xboole_0(esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_17])])])])).

cnf(c_0_24,plain,
    ( v1_xboole_0(X1)
    | v2_struct_0(X2)
    | ~ v1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_hidden(k3_yellow_0(X2),X1)
    | ~ v2_waybel_0(X1,X2)
    | ~ v13_waybel_0(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ v1_yellow_0(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( k9_setfam_1(X1) = k1_zfmisc_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( u1_struct_0(k3_lattice3(k1_lattice3(X1))) = k9_setfam_1(X1) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

fof(c_0_27,plain,(
    ! [X5,X6] :
      ( ~ r2_hidden(X5,X6)
      | ~ v1_xboole_0(X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

fof(c_0_28,plain,(
    ! [X14] :
      ( ( v1_orders_2(k3_lattice3(X14))
        | v2_struct_0(X14)
        | ~ v10_lattices(X14)
        | ~ v13_lattices(X14)
        | ~ l3_lattices(X14) )
      & ( v3_orders_2(k3_lattice3(X14))
        | v2_struct_0(X14)
        | ~ v10_lattices(X14)
        | ~ v13_lattices(X14)
        | ~ l3_lattices(X14) )
      & ( v4_orders_2(k3_lattice3(X14))
        | v2_struct_0(X14)
        | ~ v10_lattices(X14)
        | ~ v13_lattices(X14)
        | ~ l3_lattices(X14) )
      & ( v5_orders_2(k3_lattice3(X14))
        | v2_struct_0(X14)
        | ~ v10_lattices(X14)
        | ~ v13_lattices(X14)
        | ~ l3_lattices(X14) )
      & ( v1_yellow_0(k3_lattice3(X14))
        | v2_struct_0(X14)
        | ~ v10_lattices(X14)
        | ~ v13_lattices(X14)
        | ~ l3_lattices(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc3_yellow_1])])])])).

fof(c_0_29,plain,(
    ! [X11] :
      ( v13_lattices(k1_lattice3(X11))
      & k5_lattices(k1_lattice3(X11)) = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[t3_lattice3])).

fof(c_0_30,plain,(
    ! [X10] :
      ( v3_lattices(k1_lattice3(X10))
      & v10_lattices(k1_lattice3(X10)) ) ),
    inference(variable_rename,[status(thm)],[fc2_lattice3])).

fof(c_0_31,plain,(
    ! [X8] :
      ( v3_lattices(k1_lattice3(X8))
      & l3_lattices(k1_lattice3(X8)) ) ),
    inference(variable_rename,[status(thm)],[dt_k1_lattice3])).

fof(c_0_32,plain,(
    ! [X9] :
      ( ~ v2_struct_0(k1_lattice3(X9))
      & v3_lattices(k1_lattice3(X9)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_lattice3])])).

fof(c_0_33,plain,(
    ! [X15] :
      ( ~ v2_struct_0(k3_yellow_1(X15))
      & v1_orders_2(k3_yellow_1(X15))
      & v3_orders_2(k3_yellow_1(X15))
      & v4_orders_2(k3_yellow_1(X15))
      & v5_orders_2(k3_yellow_1(X15)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc7_yellow_1])])).

fof(c_0_34,plain,(
    ! [X13] :
      ( v1_orders_2(k3_yellow_1(X13))
      & l1_orders_2(k3_yellow_1(X13)) ) ),
    inference(variable_rename,[status(thm)],[dt_k3_yellow_1])).

fof(c_0_35,plain,(
    ! [X16] : k3_yellow_0(k3_yellow_1(X16)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t18_yellow_1])).

cnf(c_0_36,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_37,negated_conjecture,
    ( v1_xboole_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_38,plain,
    ( v1_xboole_0(X1)
    | v2_struct_0(X2)
    | ~ l1_orders_2(X2)
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ v1_yellow_0(X2)
    | ~ v2_waybel_0(X1,X2)
    | ~ v13_waybel_0(X1,X2)
    | ~ v1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_hidden(k3_yellow_0(X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(X2))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_25]),c_0_26])).

cnf(c_0_39,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(esk1_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_41,negated_conjecture,
    ( v1_subset_1(esk2_0,u1_struct_0(k3_yellow_1(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_42,negated_conjecture,
    ( v13_waybel_0(esk2_0,k3_yellow_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_43,negated_conjecture,
    ( v2_waybel_0(esk2_0,k3_yellow_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_44,plain,
    ( v1_yellow_0(k3_lattice3(X1))
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ v13_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_45,plain,
    ( v13_lattices(k1_lattice3(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_46,plain,
    ( v10_lattices(k1_lattice3(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_47,plain,
    ( l3_lattices(k1_lattice3(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_48,plain,
    ( ~ v2_struct_0(k1_lattice3(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_49,plain,
    ( v5_orders_2(k3_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_50,plain,
    ( v4_orders_2(k3_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_51,plain,
    ( v3_orders_2(k3_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_52,plain,
    ( l1_orders_2(k3_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_53,plain,
    ( k3_yellow_0(k3_yellow_1(X1)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_55,negated_conjecture,
    ( esk3_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_56,plain,
    ( ~ v2_struct_0(k3_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_57,plain,
    ( v2_struct_0(X1)
    | ~ v1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(X1)))))
    | ~ v13_waybel_0(X2,X1)
    | ~ v2_waybel_0(X2,X1)
    | ~ v1_yellow_0(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ r2_hidden(k3_yellow_0(X1),X2) ),
    inference(csr,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_58,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(esk1_0))))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_25]),c_0_21]),c_0_26])).

cnf(c_0_59,negated_conjecture,
    ( v1_subset_1(esk2_0,u1_struct_0(k3_lattice3(k1_lattice3(esk1_0)))) ),
    inference(rw,[status(thm)],[c_0_41,c_0_21])).

cnf(c_0_60,negated_conjecture,
    ( v13_waybel_0(esk2_0,k3_lattice3(k1_lattice3(esk1_0))) ),
    inference(rw,[status(thm)],[c_0_42,c_0_21])).

cnf(c_0_61,negated_conjecture,
    ( v2_waybel_0(esk2_0,k3_lattice3(k1_lattice3(esk1_0))) ),
    inference(rw,[status(thm)],[c_0_43,c_0_21])).

cnf(c_0_62,plain,
    ( v1_yellow_0(k3_lattice3(k1_lattice3(X1))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46]),c_0_47])]),c_0_48])).

cnf(c_0_63,plain,
    ( v5_orders_2(k3_lattice3(k1_lattice3(X1))) ),
    inference(rw,[status(thm)],[c_0_49,c_0_21])).

cnf(c_0_64,plain,
    ( v4_orders_2(k3_lattice3(k1_lattice3(X1))) ),
    inference(rw,[status(thm)],[c_0_50,c_0_21])).

cnf(c_0_65,plain,
    ( v3_orders_2(k3_lattice3(k1_lattice3(X1))) ),
    inference(rw,[status(thm)],[c_0_51,c_0_21])).

cnf(c_0_66,plain,
    ( l1_orders_2(k3_lattice3(k1_lattice3(X1))) ),
    inference(rw,[status(thm)],[c_0_52,c_0_21])).

cnf(c_0_67,plain,
    ( k3_yellow_0(k3_lattice3(k1_lattice3(X1))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_53,c_0_21])).

cnf(c_0_68,negated_conjecture,
    ( r2_hidden(k1_xboole_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_69,plain,
    ( ~ v2_struct_0(k3_lattice3(k1_lattice3(X1))) ),
    inference(rw,[status(thm)],[c_0_56,c_0_21])).

cnf(c_0_70,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59]),c_0_60]),c_0_61]),c_0_62]),c_0_63]),c_0_64]),c_0_65]),c_0_66]),c_0_67]),c_0_68])]),c_0_69]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:06:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.028 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t4_waybel_7, axiom, ![X1]:u1_struct_0(k3_yellow_1(X1))=k9_setfam_1(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_waybel_7)).
% 0.13/0.38  fof(d2_yellow_1, axiom, ![X1]:k3_yellow_1(X1)=k3_lattice3(k1_lattice3(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_yellow_1)).
% 0.13/0.38  fof(t2_yellow19, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(((((~(v1_xboole_0(X2))&v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))))&v2_waybel_0(X2,k3_yellow_1(X1)))&v13_waybel_0(X2,k3_yellow_1(X1)))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))))=>![X3]:~((r2_hidden(X3,X2)&v1_xboole_0(X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_yellow19)).
% 0.13/0.38  fof(t8_waybel_7, axiom, ![X1]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&v1_yellow_0(X1))&l1_orders_2(X1))=>![X2]:((((~(v1_xboole_0(X2))&v2_waybel_0(X2,X1))&v13_waybel_0(X2,X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v1_subset_1(X2,u1_struct_0(X1))<=>~(r2_hidden(k3_yellow_0(X1),X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_waybel_7)).
% 0.13/0.38  fof(redefinition_k9_setfam_1, axiom, ![X1]:k9_setfam_1(X1)=k1_zfmisc_1(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_setfam_1)).
% 0.13/0.38  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.13/0.38  fof(t7_boole, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&v1_xboole_0(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_boole)).
% 0.13/0.38  fof(fc3_yellow_1, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v13_lattices(X1))&l3_lattices(X1))=>((((v1_orders_2(k3_lattice3(X1))&v3_orders_2(k3_lattice3(X1)))&v4_orders_2(k3_lattice3(X1)))&v5_orders_2(k3_lattice3(X1)))&v1_yellow_0(k3_lattice3(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_yellow_1)).
% 0.13/0.38  fof(t3_lattice3, axiom, ![X1]:(v13_lattices(k1_lattice3(X1))&k5_lattices(k1_lattice3(X1))=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_lattice3)).
% 0.13/0.38  fof(fc2_lattice3, axiom, ![X1]:(v3_lattices(k1_lattice3(X1))&v10_lattices(k1_lattice3(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_lattice3)).
% 0.13/0.38  fof(dt_k1_lattice3, axiom, ![X1]:(v3_lattices(k1_lattice3(X1))&l3_lattices(k1_lattice3(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_lattice3)).
% 0.13/0.38  fof(fc1_lattice3, axiom, ![X1]:(~(v2_struct_0(k1_lattice3(X1)))&v3_lattices(k1_lattice3(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_lattice3)).
% 0.13/0.38  fof(fc7_yellow_1, axiom, ![X1]:((((~(v2_struct_0(k3_yellow_1(X1)))&v1_orders_2(k3_yellow_1(X1)))&v3_orders_2(k3_yellow_1(X1)))&v4_orders_2(k3_yellow_1(X1)))&v5_orders_2(k3_yellow_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_yellow_1)).
% 0.13/0.38  fof(dt_k3_yellow_1, axiom, ![X1]:(v1_orders_2(k3_yellow_1(X1))&l1_orders_2(k3_yellow_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_yellow_1)).
% 0.13/0.38  fof(t18_yellow_1, axiom, ![X1]:k3_yellow_0(k3_yellow_1(X1))=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_yellow_1)).
% 0.13/0.38  fof(c_0_15, plain, ![X17]:u1_struct_0(k3_yellow_1(X17))=k9_setfam_1(X17), inference(variable_rename,[status(thm)],[t4_waybel_7])).
% 0.13/0.38  fof(c_0_16, plain, ![X12]:k3_yellow_1(X12)=k3_lattice3(k1_lattice3(X12)), inference(variable_rename,[status(thm)],[d2_yellow_1])).
% 0.13/0.38  fof(c_0_17, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(((((~(v1_xboole_0(X2))&v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))))&v2_waybel_0(X2,k3_yellow_1(X1)))&v13_waybel_0(X2,k3_yellow_1(X1)))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))))=>![X3]:~((r2_hidden(X3,X2)&v1_xboole_0(X3)))))), inference(assume_negation,[status(cth)],[t2_yellow19])).
% 0.13/0.38  fof(c_0_18, plain, ![X18, X19]:((~v1_subset_1(X19,u1_struct_0(X18))|~r2_hidden(k3_yellow_0(X18),X19)|(v1_xboole_0(X19)|~v2_waybel_0(X19,X18)|~v13_waybel_0(X19,X18)|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18))))|(v2_struct_0(X18)|~v3_orders_2(X18)|~v4_orders_2(X18)|~v5_orders_2(X18)|~v1_yellow_0(X18)|~l1_orders_2(X18)))&(r2_hidden(k3_yellow_0(X18),X19)|v1_subset_1(X19,u1_struct_0(X18))|(v1_xboole_0(X19)|~v2_waybel_0(X19,X18)|~v13_waybel_0(X19,X18)|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18))))|(v2_struct_0(X18)|~v3_orders_2(X18)|~v4_orders_2(X18)|~v5_orders_2(X18)|~v1_yellow_0(X18)|~l1_orders_2(X18)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t8_waybel_7])])])])])).
% 0.13/0.38  fof(c_0_19, plain, ![X7]:k9_setfam_1(X7)=k1_zfmisc_1(X7), inference(variable_rename,[status(thm)],[redefinition_k9_setfam_1])).
% 0.13/0.38  cnf(c_0_20, plain, (u1_struct_0(k3_yellow_1(X1))=k9_setfam_1(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_21, plain, (k3_yellow_1(X1)=k3_lattice3(k1_lattice3(X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  fof(c_0_22, plain, ![X4]:(~v1_xboole_0(X4)|X4=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.13/0.38  fof(c_0_23, negated_conjecture, (~v1_xboole_0(esk1_0)&(((((~v1_xboole_0(esk2_0)&v1_subset_1(esk2_0,u1_struct_0(k3_yellow_1(esk1_0))))&v2_waybel_0(esk2_0,k3_yellow_1(esk1_0)))&v13_waybel_0(esk2_0,k3_yellow_1(esk1_0)))&m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(esk1_0)))))&(r2_hidden(esk3_0,esk2_0)&v1_xboole_0(esk3_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_17])])])])).
% 0.13/0.38  cnf(c_0_24, plain, (v1_xboole_0(X1)|v2_struct_0(X2)|~v1_subset_1(X1,u1_struct_0(X2))|~r2_hidden(k3_yellow_0(X2),X1)|~v2_waybel_0(X1,X2)|~v13_waybel_0(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~v1_yellow_0(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.38  cnf(c_0_25, plain, (k9_setfam_1(X1)=k1_zfmisc_1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_26, plain, (u1_struct_0(k3_lattice3(k1_lattice3(X1)))=k9_setfam_1(X1)), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 0.13/0.38  fof(c_0_27, plain, ![X5, X6]:(~r2_hidden(X5,X6)|~v1_xboole_0(X6)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).
% 0.13/0.38  fof(c_0_28, plain, ![X14]:(((((v1_orders_2(k3_lattice3(X14))|(v2_struct_0(X14)|~v10_lattices(X14)|~v13_lattices(X14)|~l3_lattices(X14)))&(v3_orders_2(k3_lattice3(X14))|(v2_struct_0(X14)|~v10_lattices(X14)|~v13_lattices(X14)|~l3_lattices(X14))))&(v4_orders_2(k3_lattice3(X14))|(v2_struct_0(X14)|~v10_lattices(X14)|~v13_lattices(X14)|~l3_lattices(X14))))&(v5_orders_2(k3_lattice3(X14))|(v2_struct_0(X14)|~v10_lattices(X14)|~v13_lattices(X14)|~l3_lattices(X14))))&(v1_yellow_0(k3_lattice3(X14))|(v2_struct_0(X14)|~v10_lattices(X14)|~v13_lattices(X14)|~l3_lattices(X14)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc3_yellow_1])])])])).
% 0.13/0.38  fof(c_0_29, plain, ![X11]:(v13_lattices(k1_lattice3(X11))&k5_lattices(k1_lattice3(X11))=k1_xboole_0), inference(variable_rename,[status(thm)],[t3_lattice3])).
% 0.13/0.38  fof(c_0_30, plain, ![X10]:(v3_lattices(k1_lattice3(X10))&v10_lattices(k1_lattice3(X10))), inference(variable_rename,[status(thm)],[fc2_lattice3])).
% 0.13/0.38  fof(c_0_31, plain, ![X8]:(v3_lattices(k1_lattice3(X8))&l3_lattices(k1_lattice3(X8))), inference(variable_rename,[status(thm)],[dt_k1_lattice3])).
% 0.13/0.38  fof(c_0_32, plain, ![X9]:(~v2_struct_0(k1_lattice3(X9))&v3_lattices(k1_lattice3(X9))), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_lattice3])])).
% 0.13/0.38  fof(c_0_33, plain, ![X15]:((((~v2_struct_0(k3_yellow_1(X15))&v1_orders_2(k3_yellow_1(X15)))&v3_orders_2(k3_yellow_1(X15)))&v4_orders_2(k3_yellow_1(X15)))&v5_orders_2(k3_yellow_1(X15))), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc7_yellow_1])])).
% 0.13/0.38  fof(c_0_34, plain, ![X13]:(v1_orders_2(k3_yellow_1(X13))&l1_orders_2(k3_yellow_1(X13))), inference(variable_rename,[status(thm)],[dt_k3_yellow_1])).
% 0.13/0.38  fof(c_0_35, plain, ![X16]:k3_yellow_0(k3_yellow_1(X16))=k1_xboole_0, inference(variable_rename,[status(thm)],[t18_yellow_1])).
% 0.13/0.38  cnf(c_0_36, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.38  cnf(c_0_37, negated_conjecture, (v1_xboole_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.38  cnf(c_0_38, plain, (v1_xboole_0(X1)|v2_struct_0(X2)|~l1_orders_2(X2)|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~v1_yellow_0(X2)|~v2_waybel_0(X1,X2)|~v13_waybel_0(X1,X2)|~v1_subset_1(X1,u1_struct_0(X2))|~r2_hidden(k3_yellow_0(X2),X1)|~m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(X2)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_25]), c_0_26])).
% 0.13/0.38  cnf(c_0_39, plain, (~r2_hidden(X1,X2)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.13/0.38  cnf(c_0_40, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(esk1_0))))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.38  cnf(c_0_41, negated_conjecture, (v1_subset_1(esk2_0,u1_struct_0(k3_yellow_1(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.38  cnf(c_0_42, negated_conjecture, (v13_waybel_0(esk2_0,k3_yellow_1(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.38  cnf(c_0_43, negated_conjecture, (v2_waybel_0(esk2_0,k3_yellow_1(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.38  cnf(c_0_44, plain, (v1_yellow_0(k3_lattice3(X1))|v2_struct_0(X1)|~v10_lattices(X1)|~v13_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.13/0.38  cnf(c_0_45, plain, (v13_lattices(k1_lattice3(X1))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.38  cnf(c_0_46, plain, (v10_lattices(k1_lattice3(X1))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.13/0.38  cnf(c_0_47, plain, (l3_lattices(k1_lattice3(X1))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.13/0.38  cnf(c_0_48, plain, (~v2_struct_0(k1_lattice3(X1))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.13/0.38  cnf(c_0_49, plain, (v5_orders_2(k3_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.13/0.38  cnf(c_0_50, plain, (v4_orders_2(k3_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.13/0.38  cnf(c_0_51, plain, (v3_orders_2(k3_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.13/0.38  cnf(c_0_52, plain, (l1_orders_2(k3_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.13/0.38  cnf(c_0_53, plain, (k3_yellow_0(k3_yellow_1(X1))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.38  cnf(c_0_54, negated_conjecture, (r2_hidden(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.38  cnf(c_0_55, negated_conjecture, (esk3_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.13/0.38  cnf(c_0_56, plain, (~v2_struct_0(k3_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.13/0.38  cnf(c_0_57, plain, (v2_struct_0(X1)|~v1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(X1)))))|~v13_waybel_0(X2,X1)|~v2_waybel_0(X2,X1)|~v1_yellow_0(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~l1_orders_2(X1)|~r2_hidden(k3_yellow_0(X1),X2)), inference(csr,[status(thm)],[c_0_38, c_0_39])).
% 0.13/0.38  cnf(c_0_58, negated_conjecture, (m1_subset_1(esk2_0,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(esk1_0)))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_25]), c_0_21]), c_0_26])).
% 0.13/0.38  cnf(c_0_59, negated_conjecture, (v1_subset_1(esk2_0,u1_struct_0(k3_lattice3(k1_lattice3(esk1_0))))), inference(rw,[status(thm)],[c_0_41, c_0_21])).
% 0.13/0.38  cnf(c_0_60, negated_conjecture, (v13_waybel_0(esk2_0,k3_lattice3(k1_lattice3(esk1_0)))), inference(rw,[status(thm)],[c_0_42, c_0_21])).
% 0.13/0.38  cnf(c_0_61, negated_conjecture, (v2_waybel_0(esk2_0,k3_lattice3(k1_lattice3(esk1_0)))), inference(rw,[status(thm)],[c_0_43, c_0_21])).
% 0.13/0.38  cnf(c_0_62, plain, (v1_yellow_0(k3_lattice3(k1_lattice3(X1)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46]), c_0_47])]), c_0_48])).
% 0.13/0.38  cnf(c_0_63, plain, (v5_orders_2(k3_lattice3(k1_lattice3(X1)))), inference(rw,[status(thm)],[c_0_49, c_0_21])).
% 0.13/0.38  cnf(c_0_64, plain, (v4_orders_2(k3_lattice3(k1_lattice3(X1)))), inference(rw,[status(thm)],[c_0_50, c_0_21])).
% 0.13/0.38  cnf(c_0_65, plain, (v3_orders_2(k3_lattice3(k1_lattice3(X1)))), inference(rw,[status(thm)],[c_0_51, c_0_21])).
% 0.13/0.38  cnf(c_0_66, plain, (l1_orders_2(k3_lattice3(k1_lattice3(X1)))), inference(rw,[status(thm)],[c_0_52, c_0_21])).
% 0.13/0.38  cnf(c_0_67, plain, (k3_yellow_0(k3_lattice3(k1_lattice3(X1)))=k1_xboole_0), inference(rw,[status(thm)],[c_0_53, c_0_21])).
% 0.13/0.38  cnf(c_0_68, negated_conjecture, (r2_hidden(k1_xboole_0,esk2_0)), inference(rw,[status(thm)],[c_0_54, c_0_55])).
% 0.13/0.38  cnf(c_0_69, plain, (~v2_struct_0(k3_lattice3(k1_lattice3(X1)))), inference(rw,[status(thm)],[c_0_56, c_0_21])).
% 0.13/0.38  cnf(c_0_70, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_59]), c_0_60]), c_0_61]), c_0_62]), c_0_63]), c_0_64]), c_0_65]), c_0_66]), c_0_67]), c_0_68])]), c_0_69]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 71
% 0.13/0.38  # Proof object clause steps            : 40
% 0.13/0.38  # Proof object formula steps           : 31
% 0.13/0.38  # Proof object conjectures             : 16
% 0.13/0.38  # Proof object clause conjectures      : 13
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 23
% 0.13/0.38  # Proof object initial formulas used   : 15
% 0.13/0.38  # Proof object generating inferences   : 3
% 0.13/0.38  # Proof object simplifying inferences  : 33
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 15
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 36
% 0.13/0.38  # Removed in clause preprocessing      : 3
% 0.13/0.38  # Initial clauses in saturation        : 33
% 0.13/0.38  # Processed clauses                    : 68
% 0.13/0.38  # ...of these trivial                  : 3
% 0.13/0.38  # ...subsumed                          : 2
% 0.13/0.38  # ...remaining for further processing  : 63
% 0.13/0.38  # Other redundant clauses eliminated   : 0
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 0
% 0.13/0.38  # Backward-rewritten                   : 2
% 0.13/0.38  # Generated clauses                    : 9
% 0.13/0.38  # ...of the previous two non-trivial   : 6
% 0.13/0.38  # Contextual simplify-reflections      : 1
% 0.13/0.38  # Paramodulations                      : 9
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 0
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 31
% 0.13/0.38  #    Positive orientable unit clauses  : 19
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 4
% 0.13/0.38  #    Non-unit-clauses                  : 8
% 0.13/0.38  # Current number of unprocessed clauses: 1
% 0.13/0.38  # ...number of literals in the above   : 12
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 35
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 94
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 2
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 1
% 0.13/0.38  # Unit Clause-clause subsumption calls : 3
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 1
% 0.13/0.38  # BW rewrite match successes           : 1
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 2430
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.030 s
% 0.13/0.38  # System time              : 0.003 s
% 0.13/0.38  # Total time               : 0.034 s
% 0.13/0.38  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
