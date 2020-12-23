%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:49 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 452 expanded)
%              Number of clauses        :   47 ( 189 expanded)
%              Number of leaves         :   16 ( 127 expanded)
%              Depth                    :    9
%              Number of atoms          :  240 ( 740 expanded)
%              Number of equality atoms :   45 ( 397 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   24 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t17_yellow_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
     => ! [X3] :
          ( m1_subset_1(X3,u1_struct_0(k3_yellow_1(X1)))
         => ( k13_lattice3(k3_yellow_1(X1),X2,X3) = k2_xboole_0(X2,X3)
            & k12_lattice3(k3_yellow_1(X1),X2,X3) = k3_xboole_0(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_yellow_1)).

fof(t4_yellow_1,axiom,(
    ! [X1] : k3_yellow_1(X1) = k2_yellow_1(k9_setfam_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_yellow_1)).

fof(d1_yellow_1,axiom,(
    ! [X1] : k2_yellow_1(X1) = g1_orders_2(X1,k1_yellow_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_yellow_1)).

fof(d2_yellow_1,axiom,(
    ! [X1] : k3_yellow_1(X1) = k3_lattice3(k1_lattice3(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_yellow_1)).

fof(dt_k2_yellow_1,axiom,(
    ! [X1] :
      ( v1_orders_2(k2_yellow_1(X1))
      & l1_orders_2(k2_yellow_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(fc5_yellow_1,axiom,(
    ! [X1] :
      ( v1_orders_2(k2_yellow_1(X1))
      & v3_orders_2(k2_yellow_1(X1))
      & v4_orders_2(k2_yellow_1(X1))
      & v5_orders_2(k2_yellow_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow_1)).

fof(fc1_yellow_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & l3_lattices(X1) )
     => ( v1_orders_2(k3_lattice3(X1))
        & v3_orders_2(k3_lattice3(X1))
        & v4_orders_2(k3_lattice3(X1))
        & v5_orders_2(k3_lattice3(X1))
        & v1_lattice3(k3_lattice3(X1))
        & v2_lattice3(k3_lattice3(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_yellow_1)).

fof(fc2_lattice3,axiom,(
    ! [X1] :
      ( v3_lattices(k1_lattice3(X1))
      & v10_lattices(k1_lattice3(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_lattice3)).

fof(dt_k1_lattice3,axiom,(
    ! [X1] :
      ( v3_lattices(k1_lattice3(X1))
      & l3_lattices(k1_lattice3(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_lattice3)).

fof(fc1_lattice3,axiom,(
    ! [X1] :
      ( ~ v2_struct_0(k1_lattice3(X1))
      & v3_lattices(k1_lattice3(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_lattice3)).

fof(t8_yellow_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))
             => ( r2_hidden(k2_xboole_0(X2,X3),X1)
               => k10_lattice3(k2_yellow_1(X1),X2,X3) = k2_xboole_0(X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_yellow_1)).

fof(l19_yellow_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
     => ! [X3] :
          ( m1_subset_1(X3,u1_struct_0(k3_yellow_1(X1)))
         => ( r2_hidden(k3_xboole_0(X2,X3),k9_setfam_1(X1))
            & r2_hidden(k2_xboole_0(X2,X3),k9_setfam_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l19_yellow_1)).

fof(redefinition_k13_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( v5_orders_2(X1)
        & v1_lattice3(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k13_lattice3(X1,X2,X3) = k10_lattice3(X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k13_lattice3)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

fof(t9_yellow_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))
             => ( r2_hidden(k3_xboole_0(X2,X3),X1)
               => k11_lattice3(k2_yellow_1(X1),X2,X3) = k3_xboole_0(X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_yellow_1)).

fof(redefinition_k12_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( v5_orders_2(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k12_lattice3(X1,X2,X3) = k11_lattice3(X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
       => ! [X3] :
            ( m1_subset_1(X3,u1_struct_0(k3_yellow_1(X1)))
           => ( k13_lattice3(k3_yellow_1(X1),X2,X3) = k2_xboole_0(X2,X3)
              & k12_lattice3(k3_yellow_1(X1),X2,X3) = k3_xboole_0(X2,X3) ) ) ) ),
    inference(assume_negation,[status(cth)],[t17_yellow_1])).

fof(c_0_17,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(k3_yellow_1(esk1_0)))
    & m1_subset_1(esk3_0,u1_struct_0(k3_yellow_1(esk1_0)))
    & ( k13_lattice3(k3_yellow_1(esk1_0),esk2_0,esk3_0) != k2_xboole_0(esk2_0,esk3_0)
      | k12_lattice3(k3_yellow_1(esk1_0),esk2_0,esk3_0) != k3_xboole_0(esk2_0,esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

fof(c_0_18,plain,(
    ! [X23] : k3_yellow_1(X23) = k2_yellow_1(k9_setfam_1(X23)) ),
    inference(variable_rename,[status(thm)],[t4_yellow_1])).

fof(c_0_19,plain,(
    ! [X15] : k2_yellow_1(X15) = g1_orders_2(X15,k1_yellow_1(X15)) ),
    inference(variable_rename,[status(thm)],[d1_yellow_1])).

fof(c_0_20,plain,(
    ! [X16] : k3_yellow_1(X16) = k3_lattice3(k1_lattice3(X16)) ),
    inference(variable_rename,[status(thm)],[d2_yellow_1])).

fof(c_0_21,plain,(
    ! [X17] :
      ( v1_orders_2(k2_yellow_1(X17))
      & l1_orders_2(k2_yellow_1(X17)) ) ),
    inference(variable_rename,[status(thm)],[dt_k2_yellow_1])).

fof(c_0_22,plain,(
    ! [X19] :
      ( v1_orders_2(k2_yellow_1(X19))
      & v3_orders_2(k2_yellow_1(X19))
      & v4_orders_2(k2_yellow_1(X19))
      & v5_orders_2(k2_yellow_1(X19)) ) ),
    inference(variable_rename,[status(thm)],[fc5_yellow_1])).

cnf(c_0_23,negated_conjecture,
    ( k13_lattice3(k3_yellow_1(esk1_0),esk2_0,esk3_0) != k2_xboole_0(esk2_0,esk3_0)
    | k12_lattice3(k3_yellow_1(esk1_0),esk2_0,esk3_0) != k3_xboole_0(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( k3_yellow_1(X1) = k2_yellow_1(k9_setfam_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( k2_yellow_1(X1) = g1_orders_2(X1,k1_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( k3_yellow_1(X1) = k3_lattice3(k1_lattice3(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_27,plain,(
    ! [X18] :
      ( ( v1_orders_2(k3_lattice3(X18))
        | v2_struct_0(X18)
        | ~ v10_lattices(X18)
        | ~ l3_lattices(X18) )
      & ( v3_orders_2(k3_lattice3(X18))
        | v2_struct_0(X18)
        | ~ v10_lattices(X18)
        | ~ l3_lattices(X18) )
      & ( v4_orders_2(k3_lattice3(X18))
        | v2_struct_0(X18)
        | ~ v10_lattices(X18)
        | ~ l3_lattices(X18) )
      & ( v5_orders_2(k3_lattice3(X18))
        | v2_struct_0(X18)
        | ~ v10_lattices(X18)
        | ~ l3_lattices(X18) )
      & ( v1_lattice3(k3_lattice3(X18))
        | v2_struct_0(X18)
        | ~ v10_lattices(X18)
        | ~ l3_lattices(X18) )
      & ( v2_lattice3(k3_lattice3(X18))
        | v2_struct_0(X18)
        | ~ v10_lattices(X18)
        | ~ l3_lattices(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_yellow_1])])])])).

fof(c_0_28,plain,(
    ! [X8] :
      ( v3_lattices(k1_lattice3(X8))
      & v10_lattices(k1_lattice3(X8)) ) ),
    inference(variable_rename,[status(thm)],[fc2_lattice3])).

fof(c_0_29,plain,(
    ! [X6] :
      ( v3_lattices(k1_lattice3(X6))
      & l3_lattices(k1_lattice3(X6)) ) ),
    inference(variable_rename,[status(thm)],[dt_k1_lattice3])).

fof(c_0_30,plain,(
    ! [X7] :
      ( ~ v2_struct_0(k1_lattice3(X7))
      & v3_lattices(k1_lattice3(X7)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_lattice3])])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(k3_yellow_1(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(k3_yellow_1(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_33,plain,
    ( l1_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_34,plain,
    ( v5_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_35,plain,(
    ! [X24,X25,X26] :
      ( v1_xboole_0(X24)
      | ~ m1_subset_1(X25,u1_struct_0(k2_yellow_1(X24)))
      | ~ m1_subset_1(X26,u1_struct_0(k2_yellow_1(X24)))
      | ~ r2_hidden(k2_xboole_0(X25,X26),X24)
      | k10_lattice3(k2_yellow_1(X24),X25,X26) = k2_xboole_0(X25,X26) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t8_yellow_1])])])])).

fof(c_0_36,plain,(
    ! [X20,X21,X22] :
      ( ( r2_hidden(k3_xboole_0(X21,X22),k9_setfam_1(X20))
        | ~ m1_subset_1(X22,u1_struct_0(k3_yellow_1(X20)))
        | ~ m1_subset_1(X21,u1_struct_0(k3_yellow_1(X20))) )
      & ( r2_hidden(k2_xboole_0(X21,X22),k9_setfam_1(X20))
        | ~ m1_subset_1(X22,u1_struct_0(k3_yellow_1(X20)))
        | ~ m1_subset_1(X21,u1_struct_0(k3_yellow_1(X20))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l19_yellow_1])])])])).

cnf(c_0_37,negated_conjecture,
    ( k12_lattice3(g1_orders_2(k9_setfam_1(esk1_0),k1_yellow_1(k9_setfam_1(esk1_0))),esk2_0,esk3_0) != k3_xboole_0(esk2_0,esk3_0)
    | k13_lattice3(g1_orders_2(k9_setfam_1(esk1_0),k1_yellow_1(k9_setfam_1(esk1_0))),esk2_0,esk3_0) != k2_xboole_0(esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_24]),c_0_24]),c_0_25]),c_0_25])).

cnf(c_0_38,plain,
    ( g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))) = k3_lattice3(k1_lattice3(X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_24]),c_0_25])).

fof(c_0_39,plain,(
    ! [X12,X13,X14] :
      ( ~ v5_orders_2(X12)
      | ~ v1_lattice3(X12)
      | ~ l1_orders_2(X12)
      | ~ m1_subset_1(X13,u1_struct_0(X12))
      | ~ m1_subset_1(X14,u1_struct_0(X12))
      | k13_lattice3(X12,X13,X14) = k10_lattice3(X12,X13,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k13_lattice3])])).

cnf(c_0_40,plain,
    ( v1_lattice3(k3_lattice3(X1))
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_41,plain,
    ( v10_lattices(k1_lattice3(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_42,plain,
    ( l3_lattices(k1_lattice3(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_43,plain,
    ( ~ v2_struct_0(k1_lattice3(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(g1_orders_2(k9_setfam_1(esk1_0),k1_yellow_1(k9_setfam_1(esk1_0))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_24]),c_0_25])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(g1_orders_2(k9_setfam_1(esk1_0),k1_yellow_1(k9_setfam_1(esk1_0))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_24]),c_0_25])).

cnf(c_0_46,plain,
    ( l1_orders_2(g1_orders_2(X1,k1_yellow_1(X1))) ),
    inference(rw,[status(thm)],[c_0_33,c_0_25])).

cnf(c_0_47,plain,
    ( v5_orders_2(g1_orders_2(X1,k1_yellow_1(X1))) ),
    inference(rw,[status(thm)],[c_0_34,c_0_25])).

cnf(c_0_48,plain,
    ( v1_xboole_0(X1)
    | k10_lattice3(k2_yellow_1(X1),X2,X3) = k2_xboole_0(X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))
    | ~ r2_hidden(k2_xboole_0(X2,X3),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_49,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,X5)
      | ~ v1_xboole_0(X5) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_50,plain,
    ( r2_hidden(k2_xboole_0(X1,X2),k9_setfam_1(X3))
    | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X3)))
    | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_51,plain,(
    ! [X27,X28,X29] :
      ( v1_xboole_0(X27)
      | ~ m1_subset_1(X28,u1_struct_0(k2_yellow_1(X27)))
      | ~ m1_subset_1(X29,u1_struct_0(k2_yellow_1(X27)))
      | ~ r2_hidden(k3_xboole_0(X28,X29),X27)
      | k11_lattice3(k2_yellow_1(X27),X28,X29) = k3_xboole_0(X28,X29) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t9_yellow_1])])])])).

cnf(c_0_52,negated_conjecture,
    ( k12_lattice3(k3_lattice3(k1_lattice3(esk1_0)),esk2_0,esk3_0) != k3_xboole_0(esk2_0,esk3_0)
    | k13_lattice3(k3_lattice3(k1_lattice3(esk1_0)),esk2_0,esk3_0) != k2_xboole_0(esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_38]),c_0_38])).

cnf(c_0_53,plain,
    ( k13_lattice3(X1,X2,X3) = k10_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_54,plain,
    ( v1_lattice3(k3_lattice3(k1_lattice3(X1))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])]),c_0_43])).

cnf(c_0_55,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(k3_lattice3(k1_lattice3(esk1_0)))) ),
    inference(rw,[status(thm)],[c_0_44,c_0_38])).

cnf(c_0_56,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(k3_lattice3(k1_lattice3(esk1_0)))) ),
    inference(rw,[status(thm)],[c_0_45,c_0_38])).

cnf(c_0_57,plain,
    ( l1_orders_2(k3_lattice3(k1_lattice3(X1))) ),
    inference(spm,[status(thm)],[c_0_46,c_0_38])).

cnf(c_0_58,plain,
    ( v5_orders_2(k3_lattice3(k1_lattice3(X1))) ),
    inference(spm,[status(thm)],[c_0_47,c_0_38])).

fof(c_0_59,plain,(
    ! [X9,X10,X11] :
      ( ~ v5_orders_2(X9)
      | ~ v2_lattice3(X9)
      | ~ l1_orders_2(X9)
      | ~ m1_subset_1(X10,u1_struct_0(X9))
      | ~ m1_subset_1(X11,u1_struct_0(X9))
      | k12_lattice3(X9,X10,X11) = k11_lattice3(X9,X10,X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k12_lattice3])])).

cnf(c_0_60,plain,
    ( v2_lattice3(k3_lattice3(X1))
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_61,plain,
    ( k10_lattice3(g1_orders_2(X1,k1_yellow_1(X1)),X2,X3) = k2_xboole_0(X2,X3)
    | v1_xboole_0(X1)
    | ~ r2_hidden(k2_xboole_0(X2,X3),X1)
    | ~ m1_subset_1(X3,u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))))
    | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_25]),c_0_25]),c_0_25])).

cnf(c_0_62,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_63,plain,
    ( r2_hidden(k2_xboole_0(X1,X2),k9_setfam_1(X3))
    | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(k9_setfam_1(X3),k1_yellow_1(k9_setfam_1(X3)))))
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(k9_setfam_1(X3),k1_yellow_1(k9_setfam_1(X3))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_24]),c_0_24]),c_0_25]),c_0_25])).

cnf(c_0_64,plain,
    ( v1_xboole_0(X1)
    | k11_lattice3(k2_yellow_1(X1),X2,X3) = k3_xboole_0(X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))
    | ~ r2_hidden(k3_xboole_0(X2,X3),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_65,plain,
    ( r2_hidden(k3_xboole_0(X1,X2),k9_setfam_1(X3))
    | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X3)))
    | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_66,negated_conjecture,
    ( k12_lattice3(k3_lattice3(k1_lattice3(esk1_0)),esk2_0,esk3_0) != k3_xboole_0(esk2_0,esk3_0)
    | k10_lattice3(k3_lattice3(k1_lattice3(esk1_0)),esk2_0,esk3_0) != k2_xboole_0(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54]),c_0_55]),c_0_56]),c_0_57]),c_0_58])])).

cnf(c_0_67,plain,
    ( k12_lattice3(X1,X2,X3) = k11_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_68,plain,
    ( v2_lattice3(k3_lattice3(k1_lattice3(X1))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_41]),c_0_42])]),c_0_43])).

cnf(c_0_69,plain,
    ( k10_lattice3(g1_orders_2(X1,k1_yellow_1(X1)),X2,X3) = k2_xboole_0(X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))))
    | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))))
    | ~ r2_hidden(k2_xboole_0(X2,X3),X1) ),
    inference(csr,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_70,plain,
    ( r2_hidden(k2_xboole_0(X1,X2),k9_setfam_1(X3))
    | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X3))))
    | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X3)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_38]),c_0_38])).

cnf(c_0_71,plain,
    ( k11_lattice3(g1_orders_2(X1,k1_yellow_1(X1)),X2,X3) = k3_xboole_0(X2,X3)
    | v1_xboole_0(X1)
    | ~ r2_hidden(k3_xboole_0(X2,X3),X1)
    | ~ m1_subset_1(X3,u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))))
    | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_25]),c_0_25]),c_0_25])).

cnf(c_0_72,plain,
    ( r2_hidden(k3_xboole_0(X1,X2),k9_setfam_1(X3))
    | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(k9_setfam_1(X3),k1_yellow_1(k9_setfam_1(X3)))))
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(k9_setfam_1(X3),k1_yellow_1(k9_setfam_1(X3))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_24]),c_0_24]),c_0_25]),c_0_25])).

cnf(c_0_73,negated_conjecture,
    ( k11_lattice3(k3_lattice3(k1_lattice3(esk1_0)),esk2_0,esk3_0) != k3_xboole_0(esk2_0,esk3_0)
    | k10_lattice3(k3_lattice3(k1_lattice3(esk1_0)),esk2_0,esk3_0) != k2_xboole_0(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_55]),c_0_56]),c_0_57]),c_0_68]),c_0_58])])).

cnf(c_0_74,plain,
    ( k10_lattice3(k3_lattice3(k1_lattice3(X1)),X2,X3) = k2_xboole_0(X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
    | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_38]),c_0_70])).

cnf(c_0_75,plain,
    ( k11_lattice3(g1_orders_2(X1,k1_yellow_1(X1)),X2,X3) = k3_xboole_0(X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))))
    | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))))
    | ~ r2_hidden(k3_xboole_0(X2,X3),X1) ),
    inference(csr,[status(thm)],[c_0_71,c_0_62])).

cnf(c_0_76,plain,
    ( r2_hidden(k3_xboole_0(X1,X2),k9_setfam_1(X3))
    | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X3))))
    | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X3)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72,c_0_38]),c_0_38])).

cnf(c_0_77,negated_conjecture,
    ( k11_lattice3(k3_lattice3(k1_lattice3(esk1_0)),esk2_0,esk3_0) != k3_xboole_0(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_55]),c_0_56])])).

cnf(c_0_78,plain,
    ( k11_lattice3(k3_lattice3(k1_lattice3(X1)),X2,X3) = k3_xboole_0(X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
    | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_38]),c_0_76])).

cnf(c_0_79,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_55]),c_0_56])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:13:01 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.14/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.14/0.40  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.14/0.40  #
% 0.14/0.40  # Preprocessing time       : 0.049 s
% 0.14/0.40  # Presaturation interreduction done
% 0.14/0.40  
% 0.14/0.40  # Proof found!
% 0.14/0.40  # SZS status Theorem
% 0.14/0.40  # SZS output start CNFRefutation
% 0.14/0.40  fof(t17_yellow_1, conjecture, ![X1, X2]:(m1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(k3_yellow_1(X1)))=>(k13_lattice3(k3_yellow_1(X1),X2,X3)=k2_xboole_0(X2,X3)&k12_lattice3(k3_yellow_1(X1),X2,X3)=k3_xboole_0(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_yellow_1)).
% 0.14/0.40  fof(t4_yellow_1, axiom, ![X1]:k3_yellow_1(X1)=k2_yellow_1(k9_setfam_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_yellow_1)).
% 0.14/0.40  fof(d1_yellow_1, axiom, ![X1]:k2_yellow_1(X1)=g1_orders_2(X1,k1_yellow_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_yellow_1)).
% 0.14/0.40  fof(d2_yellow_1, axiom, ![X1]:k3_yellow_1(X1)=k3_lattice3(k1_lattice3(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_yellow_1)).
% 0.14/0.40  fof(dt_k2_yellow_1, axiom, ![X1]:(v1_orders_2(k2_yellow_1(X1))&l1_orders_2(k2_yellow_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 0.14/0.40  fof(fc5_yellow_1, axiom, ![X1]:(((v1_orders_2(k2_yellow_1(X1))&v3_orders_2(k2_yellow_1(X1)))&v4_orders_2(k2_yellow_1(X1)))&v5_orders_2(k2_yellow_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_yellow_1)).
% 0.14/0.40  fof(fc1_yellow_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v10_lattices(X1))&l3_lattices(X1))=>(((((v1_orders_2(k3_lattice3(X1))&v3_orders_2(k3_lattice3(X1)))&v4_orders_2(k3_lattice3(X1)))&v5_orders_2(k3_lattice3(X1)))&v1_lattice3(k3_lattice3(X1)))&v2_lattice3(k3_lattice3(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_yellow_1)).
% 0.14/0.40  fof(fc2_lattice3, axiom, ![X1]:(v3_lattices(k1_lattice3(X1))&v10_lattices(k1_lattice3(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_lattice3)).
% 0.14/0.40  fof(dt_k1_lattice3, axiom, ![X1]:(v3_lattices(k1_lattice3(X1))&l3_lattices(k1_lattice3(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_lattice3)).
% 0.14/0.40  fof(fc1_lattice3, axiom, ![X1]:(~(v2_struct_0(k1_lattice3(X1)))&v3_lattices(k1_lattice3(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_lattice3)).
% 0.14/0.40  fof(t8_yellow_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))=>(r2_hidden(k2_xboole_0(X2,X3),X1)=>k10_lattice3(k2_yellow_1(X1),X2,X3)=k2_xboole_0(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_yellow_1)).
% 0.14/0.40  fof(l19_yellow_1, axiom, ![X1, X2]:(m1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(k3_yellow_1(X1)))=>(r2_hidden(k3_xboole_0(X2,X3),k9_setfam_1(X1))&r2_hidden(k2_xboole_0(X2,X3),k9_setfam_1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l19_yellow_1)).
% 0.14/0.40  fof(redefinition_k13_lattice3, axiom, ![X1, X2, X3]:(((((v5_orders_2(X1)&v1_lattice3(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k13_lattice3(X1,X2,X3)=k10_lattice3(X1,X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k13_lattice3)).
% 0.14/0.40  fof(t7_boole, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&v1_xboole_0(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_boole)).
% 0.14/0.40  fof(t9_yellow_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))=>(r2_hidden(k3_xboole_0(X2,X3),X1)=>k11_lattice3(k2_yellow_1(X1),X2,X3)=k3_xboole_0(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_yellow_1)).
% 0.14/0.40  fof(redefinition_k12_lattice3, axiom, ![X1, X2, X3]:(((((v5_orders_2(X1)&v2_lattice3(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k12_lattice3(X1,X2,X3)=k11_lattice3(X1,X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k12_lattice3)).
% 0.14/0.40  fof(c_0_16, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(k3_yellow_1(X1)))=>(k13_lattice3(k3_yellow_1(X1),X2,X3)=k2_xboole_0(X2,X3)&k12_lattice3(k3_yellow_1(X1),X2,X3)=k3_xboole_0(X2,X3))))), inference(assume_negation,[status(cth)],[t17_yellow_1])).
% 0.14/0.40  fof(c_0_17, negated_conjecture, (m1_subset_1(esk2_0,u1_struct_0(k3_yellow_1(esk1_0)))&(m1_subset_1(esk3_0,u1_struct_0(k3_yellow_1(esk1_0)))&(k13_lattice3(k3_yellow_1(esk1_0),esk2_0,esk3_0)!=k2_xboole_0(esk2_0,esk3_0)|k12_lattice3(k3_yellow_1(esk1_0),esk2_0,esk3_0)!=k3_xboole_0(esk2_0,esk3_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).
% 0.14/0.40  fof(c_0_18, plain, ![X23]:k3_yellow_1(X23)=k2_yellow_1(k9_setfam_1(X23)), inference(variable_rename,[status(thm)],[t4_yellow_1])).
% 0.14/0.40  fof(c_0_19, plain, ![X15]:k2_yellow_1(X15)=g1_orders_2(X15,k1_yellow_1(X15)), inference(variable_rename,[status(thm)],[d1_yellow_1])).
% 0.14/0.40  fof(c_0_20, plain, ![X16]:k3_yellow_1(X16)=k3_lattice3(k1_lattice3(X16)), inference(variable_rename,[status(thm)],[d2_yellow_1])).
% 0.14/0.40  fof(c_0_21, plain, ![X17]:(v1_orders_2(k2_yellow_1(X17))&l1_orders_2(k2_yellow_1(X17))), inference(variable_rename,[status(thm)],[dt_k2_yellow_1])).
% 0.14/0.40  fof(c_0_22, plain, ![X19]:(((v1_orders_2(k2_yellow_1(X19))&v3_orders_2(k2_yellow_1(X19)))&v4_orders_2(k2_yellow_1(X19)))&v5_orders_2(k2_yellow_1(X19))), inference(variable_rename,[status(thm)],[fc5_yellow_1])).
% 0.14/0.40  cnf(c_0_23, negated_conjecture, (k13_lattice3(k3_yellow_1(esk1_0),esk2_0,esk3_0)!=k2_xboole_0(esk2_0,esk3_0)|k12_lattice3(k3_yellow_1(esk1_0),esk2_0,esk3_0)!=k3_xboole_0(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.40  cnf(c_0_24, plain, (k3_yellow_1(X1)=k2_yellow_1(k9_setfam_1(X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.14/0.40  cnf(c_0_25, plain, (k2_yellow_1(X1)=g1_orders_2(X1,k1_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.14/0.40  cnf(c_0_26, plain, (k3_yellow_1(X1)=k3_lattice3(k1_lattice3(X1))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.14/0.40  fof(c_0_27, plain, ![X18]:((((((v1_orders_2(k3_lattice3(X18))|(v2_struct_0(X18)|~v10_lattices(X18)|~l3_lattices(X18)))&(v3_orders_2(k3_lattice3(X18))|(v2_struct_0(X18)|~v10_lattices(X18)|~l3_lattices(X18))))&(v4_orders_2(k3_lattice3(X18))|(v2_struct_0(X18)|~v10_lattices(X18)|~l3_lattices(X18))))&(v5_orders_2(k3_lattice3(X18))|(v2_struct_0(X18)|~v10_lattices(X18)|~l3_lattices(X18))))&(v1_lattice3(k3_lattice3(X18))|(v2_struct_0(X18)|~v10_lattices(X18)|~l3_lattices(X18))))&(v2_lattice3(k3_lattice3(X18))|(v2_struct_0(X18)|~v10_lattices(X18)|~l3_lattices(X18)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_yellow_1])])])])).
% 0.14/0.40  fof(c_0_28, plain, ![X8]:(v3_lattices(k1_lattice3(X8))&v10_lattices(k1_lattice3(X8))), inference(variable_rename,[status(thm)],[fc2_lattice3])).
% 0.14/0.40  fof(c_0_29, plain, ![X6]:(v3_lattices(k1_lattice3(X6))&l3_lattices(k1_lattice3(X6))), inference(variable_rename,[status(thm)],[dt_k1_lattice3])).
% 0.14/0.40  fof(c_0_30, plain, ![X7]:(~v2_struct_0(k1_lattice3(X7))&v3_lattices(k1_lattice3(X7))), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_lattice3])])).
% 0.14/0.40  cnf(c_0_31, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(k3_yellow_1(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.40  cnf(c_0_32, negated_conjecture, (m1_subset_1(esk2_0,u1_struct_0(k3_yellow_1(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.40  cnf(c_0_33, plain, (l1_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.14/0.40  cnf(c_0_34, plain, (v5_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.40  fof(c_0_35, plain, ![X24, X25, X26]:(v1_xboole_0(X24)|(~m1_subset_1(X25,u1_struct_0(k2_yellow_1(X24)))|(~m1_subset_1(X26,u1_struct_0(k2_yellow_1(X24)))|(~r2_hidden(k2_xboole_0(X25,X26),X24)|k10_lattice3(k2_yellow_1(X24),X25,X26)=k2_xboole_0(X25,X26))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t8_yellow_1])])])])).
% 0.14/0.40  fof(c_0_36, plain, ![X20, X21, X22]:((r2_hidden(k3_xboole_0(X21,X22),k9_setfam_1(X20))|~m1_subset_1(X22,u1_struct_0(k3_yellow_1(X20)))|~m1_subset_1(X21,u1_struct_0(k3_yellow_1(X20))))&(r2_hidden(k2_xboole_0(X21,X22),k9_setfam_1(X20))|~m1_subset_1(X22,u1_struct_0(k3_yellow_1(X20)))|~m1_subset_1(X21,u1_struct_0(k3_yellow_1(X20))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l19_yellow_1])])])])).
% 0.14/0.40  cnf(c_0_37, negated_conjecture, (k12_lattice3(g1_orders_2(k9_setfam_1(esk1_0),k1_yellow_1(k9_setfam_1(esk1_0))),esk2_0,esk3_0)!=k3_xboole_0(esk2_0,esk3_0)|k13_lattice3(g1_orders_2(k9_setfam_1(esk1_0),k1_yellow_1(k9_setfam_1(esk1_0))),esk2_0,esk3_0)!=k2_xboole_0(esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_24]), c_0_24]), c_0_25]), c_0_25])).
% 0.14/0.40  cnf(c_0_38, plain, (g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1)))=k3_lattice3(k1_lattice3(X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_24]), c_0_25])).
% 0.14/0.40  fof(c_0_39, plain, ![X12, X13, X14]:(~v5_orders_2(X12)|~v1_lattice3(X12)|~l1_orders_2(X12)|~m1_subset_1(X13,u1_struct_0(X12))|~m1_subset_1(X14,u1_struct_0(X12))|k13_lattice3(X12,X13,X14)=k10_lattice3(X12,X13,X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k13_lattice3])])).
% 0.14/0.40  cnf(c_0_40, plain, (v1_lattice3(k3_lattice3(X1))|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.14/0.40  cnf(c_0_41, plain, (v10_lattices(k1_lattice3(X1))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.14/0.40  cnf(c_0_42, plain, (l3_lattices(k1_lattice3(X1))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.14/0.40  cnf(c_0_43, plain, (~v2_struct_0(k1_lattice3(X1))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.14/0.40  cnf(c_0_44, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(g1_orders_2(k9_setfam_1(esk1_0),k1_yellow_1(k9_setfam_1(esk1_0)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_24]), c_0_25])).
% 0.14/0.40  cnf(c_0_45, negated_conjecture, (m1_subset_1(esk2_0,u1_struct_0(g1_orders_2(k9_setfam_1(esk1_0),k1_yellow_1(k9_setfam_1(esk1_0)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_24]), c_0_25])).
% 0.14/0.40  cnf(c_0_46, plain, (l1_orders_2(g1_orders_2(X1,k1_yellow_1(X1)))), inference(rw,[status(thm)],[c_0_33, c_0_25])).
% 0.14/0.40  cnf(c_0_47, plain, (v5_orders_2(g1_orders_2(X1,k1_yellow_1(X1)))), inference(rw,[status(thm)],[c_0_34, c_0_25])).
% 0.14/0.40  cnf(c_0_48, plain, (v1_xboole_0(X1)|k10_lattice3(k2_yellow_1(X1),X2,X3)=k2_xboole_0(X2,X3)|~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))|~m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))|~r2_hidden(k2_xboole_0(X2,X3),X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.14/0.40  fof(c_0_49, plain, ![X4, X5]:(~r2_hidden(X4,X5)|~v1_xboole_0(X5)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).
% 0.14/0.40  cnf(c_0_50, plain, (r2_hidden(k2_xboole_0(X1,X2),k9_setfam_1(X3))|~m1_subset_1(X2,u1_struct_0(k3_yellow_1(X3)))|~m1_subset_1(X1,u1_struct_0(k3_yellow_1(X3)))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.14/0.40  fof(c_0_51, plain, ![X27, X28, X29]:(v1_xboole_0(X27)|(~m1_subset_1(X28,u1_struct_0(k2_yellow_1(X27)))|(~m1_subset_1(X29,u1_struct_0(k2_yellow_1(X27)))|(~r2_hidden(k3_xboole_0(X28,X29),X27)|k11_lattice3(k2_yellow_1(X27),X28,X29)=k3_xboole_0(X28,X29))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t9_yellow_1])])])])).
% 0.14/0.40  cnf(c_0_52, negated_conjecture, (k12_lattice3(k3_lattice3(k1_lattice3(esk1_0)),esk2_0,esk3_0)!=k3_xboole_0(esk2_0,esk3_0)|k13_lattice3(k3_lattice3(k1_lattice3(esk1_0)),esk2_0,esk3_0)!=k2_xboole_0(esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_38]), c_0_38])).
% 0.14/0.40  cnf(c_0_53, plain, (k13_lattice3(X1,X2,X3)=k10_lattice3(X1,X2,X3)|~v5_orders_2(X1)|~v1_lattice3(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.14/0.40  cnf(c_0_54, plain, (v1_lattice3(k3_lattice3(k1_lattice3(X1)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42])]), c_0_43])).
% 0.14/0.40  cnf(c_0_55, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(k3_lattice3(k1_lattice3(esk1_0))))), inference(rw,[status(thm)],[c_0_44, c_0_38])).
% 0.14/0.40  cnf(c_0_56, negated_conjecture, (m1_subset_1(esk2_0,u1_struct_0(k3_lattice3(k1_lattice3(esk1_0))))), inference(rw,[status(thm)],[c_0_45, c_0_38])).
% 0.14/0.40  cnf(c_0_57, plain, (l1_orders_2(k3_lattice3(k1_lattice3(X1)))), inference(spm,[status(thm)],[c_0_46, c_0_38])).
% 0.14/0.40  cnf(c_0_58, plain, (v5_orders_2(k3_lattice3(k1_lattice3(X1)))), inference(spm,[status(thm)],[c_0_47, c_0_38])).
% 0.14/0.40  fof(c_0_59, plain, ![X9, X10, X11]:(~v5_orders_2(X9)|~v2_lattice3(X9)|~l1_orders_2(X9)|~m1_subset_1(X10,u1_struct_0(X9))|~m1_subset_1(X11,u1_struct_0(X9))|k12_lattice3(X9,X10,X11)=k11_lattice3(X9,X10,X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k12_lattice3])])).
% 0.14/0.40  cnf(c_0_60, plain, (v2_lattice3(k3_lattice3(X1))|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.14/0.40  cnf(c_0_61, plain, (k10_lattice3(g1_orders_2(X1,k1_yellow_1(X1)),X2,X3)=k2_xboole_0(X2,X3)|v1_xboole_0(X1)|~r2_hidden(k2_xboole_0(X2,X3),X1)|~m1_subset_1(X3,u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))))|~m1_subset_1(X2,u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_25]), c_0_25]), c_0_25])).
% 0.14/0.40  cnf(c_0_62, plain, (~r2_hidden(X1,X2)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.14/0.40  cnf(c_0_63, plain, (r2_hidden(k2_xboole_0(X1,X2),k9_setfam_1(X3))|~m1_subset_1(X2,u1_struct_0(g1_orders_2(k9_setfam_1(X3),k1_yellow_1(k9_setfam_1(X3)))))|~m1_subset_1(X1,u1_struct_0(g1_orders_2(k9_setfam_1(X3),k1_yellow_1(k9_setfam_1(X3)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_24]), c_0_24]), c_0_25]), c_0_25])).
% 0.14/0.40  cnf(c_0_64, plain, (v1_xboole_0(X1)|k11_lattice3(k2_yellow_1(X1),X2,X3)=k3_xboole_0(X2,X3)|~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))|~m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))|~r2_hidden(k3_xboole_0(X2,X3),X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.14/0.40  cnf(c_0_65, plain, (r2_hidden(k3_xboole_0(X1,X2),k9_setfam_1(X3))|~m1_subset_1(X2,u1_struct_0(k3_yellow_1(X3)))|~m1_subset_1(X1,u1_struct_0(k3_yellow_1(X3)))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.14/0.40  cnf(c_0_66, negated_conjecture, (k12_lattice3(k3_lattice3(k1_lattice3(esk1_0)),esk2_0,esk3_0)!=k3_xboole_0(esk2_0,esk3_0)|k10_lattice3(k3_lattice3(k1_lattice3(esk1_0)),esk2_0,esk3_0)!=k2_xboole_0(esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54]), c_0_55]), c_0_56]), c_0_57]), c_0_58])])).
% 0.14/0.40  cnf(c_0_67, plain, (k12_lattice3(X1,X2,X3)=k11_lattice3(X1,X2,X3)|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.14/0.40  cnf(c_0_68, plain, (v2_lattice3(k3_lattice3(k1_lattice3(X1)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_41]), c_0_42])]), c_0_43])).
% 0.14/0.40  cnf(c_0_69, plain, (k10_lattice3(g1_orders_2(X1,k1_yellow_1(X1)),X2,X3)=k2_xboole_0(X2,X3)|~m1_subset_1(X3,u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))))|~m1_subset_1(X2,u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))))|~r2_hidden(k2_xboole_0(X2,X3),X1)), inference(csr,[status(thm)],[c_0_61, c_0_62])).
% 0.14/0.40  cnf(c_0_70, plain, (r2_hidden(k2_xboole_0(X1,X2),k9_setfam_1(X3))|~m1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X3))))|~m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X3))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_38]), c_0_38])).
% 0.14/0.40  cnf(c_0_71, plain, (k11_lattice3(g1_orders_2(X1,k1_yellow_1(X1)),X2,X3)=k3_xboole_0(X2,X3)|v1_xboole_0(X1)|~r2_hidden(k3_xboole_0(X2,X3),X1)|~m1_subset_1(X3,u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))))|~m1_subset_1(X2,u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64, c_0_25]), c_0_25]), c_0_25])).
% 0.14/0.40  cnf(c_0_72, plain, (r2_hidden(k3_xboole_0(X1,X2),k9_setfam_1(X3))|~m1_subset_1(X2,u1_struct_0(g1_orders_2(k9_setfam_1(X3),k1_yellow_1(k9_setfam_1(X3)))))|~m1_subset_1(X1,u1_struct_0(g1_orders_2(k9_setfam_1(X3),k1_yellow_1(k9_setfam_1(X3)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65, c_0_24]), c_0_24]), c_0_25]), c_0_25])).
% 0.14/0.40  cnf(c_0_73, negated_conjecture, (k11_lattice3(k3_lattice3(k1_lattice3(esk1_0)),esk2_0,esk3_0)!=k3_xboole_0(esk2_0,esk3_0)|k10_lattice3(k3_lattice3(k1_lattice3(esk1_0)),esk2_0,esk3_0)!=k2_xboole_0(esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_55]), c_0_56]), c_0_57]), c_0_68]), c_0_58])])).
% 0.14/0.40  cnf(c_0_74, plain, (k10_lattice3(k3_lattice3(k1_lattice3(X1)),X2,X3)=k2_xboole_0(X2,X3)|~m1_subset_1(X3,u1_struct_0(k3_lattice3(k1_lattice3(X1))))|~m1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_38]), c_0_70])).
% 0.14/0.40  cnf(c_0_75, plain, (k11_lattice3(g1_orders_2(X1,k1_yellow_1(X1)),X2,X3)=k3_xboole_0(X2,X3)|~m1_subset_1(X3,u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))))|~m1_subset_1(X2,u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))))|~r2_hidden(k3_xboole_0(X2,X3),X1)), inference(csr,[status(thm)],[c_0_71, c_0_62])).
% 0.14/0.40  cnf(c_0_76, plain, (r2_hidden(k3_xboole_0(X1,X2),k9_setfam_1(X3))|~m1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X3))))|~m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X3))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72, c_0_38]), c_0_38])).
% 0.14/0.40  cnf(c_0_77, negated_conjecture, (k11_lattice3(k3_lattice3(k1_lattice3(esk1_0)),esk2_0,esk3_0)!=k3_xboole_0(esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_55]), c_0_56])])).
% 0.14/0.40  cnf(c_0_78, plain, (k11_lattice3(k3_lattice3(k1_lattice3(X1)),X2,X3)=k3_xboole_0(X2,X3)|~m1_subset_1(X3,u1_struct_0(k3_lattice3(k1_lattice3(X1))))|~m1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_38]), c_0_76])).
% 0.14/0.40  cnf(c_0_79, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_55]), c_0_56])]), ['proof']).
% 0.14/0.40  # SZS output end CNFRefutation
% 0.14/0.40  # Proof object total steps             : 80
% 0.14/0.40  # Proof object clause steps            : 47
% 0.14/0.40  # Proof object formula steps           : 33
% 0.14/0.40  # Proof object conjectures             : 16
% 0.14/0.40  # Proof object clause conjectures      : 13
% 0.14/0.40  # Proof object formula conjectures     : 3
% 0.14/0.40  # Proof object initial clauses used    : 20
% 0.14/0.40  # Proof object initial formulas used   : 16
% 0.14/0.40  # Proof object generating inferences   : 10
% 0.14/0.40  # Proof object simplifying inferences  : 62
% 0.14/0.40  # Training examples: 0 positive, 0 negative
% 0.14/0.40  # Parsed axioms                        : 16
% 0.14/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.40  # Initial clauses                      : 31
% 0.14/0.40  # Removed in clause preprocessing      : 2
% 0.14/0.40  # Initial clauses in saturation        : 29
% 0.14/0.40  # Processed clauses                    : 74
% 0.14/0.40  # ...of these trivial                  : 3
% 0.14/0.40  # ...subsumed                          : 2
% 0.14/0.40  # ...remaining for further processing  : 69
% 0.14/0.40  # Other redundant clauses eliminated   : 0
% 0.14/0.40  # Clauses deleted for lack of memory   : 0
% 0.14/0.40  # Backward-subsumed                    : 0
% 0.14/0.40  # Backward-rewritten                   : 3
% 0.14/0.40  # Generated clauses                    : 21
% 0.14/0.40  # ...of the previous two non-trivial   : 19
% 0.14/0.40  # Contextual simplify-reflections      : 4
% 0.14/0.40  # Paramodulations                      : 21
% 0.14/0.40  # Factorizations                       : 0
% 0.14/0.40  # Equation resolutions                 : 0
% 0.14/0.40  # Propositional unsat checks           : 0
% 0.14/0.40  #    Propositional check models        : 0
% 0.14/0.40  #    Propositional check unsatisfiable : 0
% 0.14/0.40  #    Propositional clauses             : 0
% 0.14/0.40  #    Propositional clauses after purity: 0
% 0.14/0.40  #    Propositional unsat core size     : 0
% 0.14/0.40  #    Propositional preprocessing time  : 0.000
% 0.14/0.40  #    Propositional encoding time       : 0.000
% 0.14/0.40  #    Propositional solver time         : 0.000
% 0.14/0.40  #    Success case prop preproc time    : 0.000
% 0.14/0.40  #    Success case prop encoding time   : 0.000
% 0.14/0.40  #    Success case prop solver time     : 0.000
% 0.14/0.40  # Current number of processed clauses  : 40
% 0.14/0.40  #    Positive orientable unit clauses  : 18
% 0.14/0.40  #    Positive unorientable unit clauses: 0
% 0.14/0.40  #    Negative unit clauses             : 2
% 0.14/0.40  #    Non-unit-clauses                  : 20
% 0.14/0.40  # Current number of unprocessed clauses: 0
% 0.14/0.40  # ...number of literals in the above   : 0
% 0.14/0.40  # Current number of archived formulas  : 0
% 0.14/0.40  # Current number of archived clauses   : 31
% 0.14/0.40  # Clause-clause subsumption calls (NU) : 157
% 0.14/0.40  # Rec. Clause-clause subsumption calls : 74
% 0.14/0.40  # Non-unit clause-clause subsumptions  : 6
% 0.14/0.40  # Unit Clause-clause subsumption calls : 4
% 0.14/0.40  # Rewrite failures with RHS unbound    : 0
% 0.14/0.40  # BW rewrite match attempts            : 1
% 0.14/0.40  # BW rewrite match successes           : 1
% 0.14/0.40  # Condensation attempts                : 0
% 0.14/0.40  # Condensation successes               : 0
% 0.14/0.40  # Termbank termtop insertions          : 3104
% 0.14/0.40  
% 0.14/0.40  # -------------------------------------------------
% 0.14/0.40  # User time                : 0.052 s
% 0.14/0.40  # System time              : 0.007 s
% 0.14/0.40  # Total time               : 0.059 s
% 0.14/0.40  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
