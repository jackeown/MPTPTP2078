%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1960+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:04 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 187 expanded)
%              Number of clauses        :   49 (  79 expanded)
%              Number of leaves         :   21 (  53 expanded)
%              Depth                    :   12
%              Number of atoms          :  340 ( 792 expanded)
%              Number of equality atoms :   63 ( 101 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   36 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t17_yellow_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
     => ! [X3] :
          ( m1_subset_1(X3,u1_struct_0(k3_yellow_1(X1)))
         => ( k13_lattice3(k3_yellow_1(X1),X2,X3) = k2_xboole_0(X2,X3)
            & k12_lattice3(k3_yellow_1(X1),X2,X3) = k3_xboole_0(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_yellow_1)).

fof(redefinition_k12_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( v5_orders_2(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k12_lattice3(X1,X2,X3) = k11_lattice3(X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

fof(fc7_yellow_1,axiom,(
    ! [X1] :
      ( ~ v2_struct_0(k3_yellow_1(X1))
      & v1_orders_2(k3_yellow_1(X1))
      & v3_orders_2(k3_yellow_1(X1))
      & v4_orders_2(k3_yellow_1(X1))
      & v5_orders_2(k3_yellow_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_yellow_1)).

fof(dt_k3_yellow_1,axiom,(
    ! [X1] :
      ( v1_orders_2(k3_yellow_1(X1))
      & l1_orders_2(k3_yellow_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow_1)).

fof(d23_waybel_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r6_waybel_1(X1,X2,X3)
              <=> ( k10_lattice3(X1,X2,X3) = k4_yellow_0(X1)
                  & k11_lattice3(X1,X2,X3) = k3_yellow_0(X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d23_waybel_1)).

fof(t19_yellow_1,axiom,(
    ! [X1] : k4_yellow_0(k3_yellow_1(X1)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_yellow_1)).

fof(t18_yellow_1,axiom,(
    ! [X1] : k3_yellow_0(k3_yellow_1(X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_yellow_1)).

fof(redefinition_k13_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( v5_orders_2(X1)
        & v1_lattice3(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k13_lattice3(X1,X2,X3) = k10_lattice3(X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k13_lattice3)).

fof(t4_waybel_7,axiom,(
    ! [X1] : u1_struct_0(k3_yellow_1(X1)) = k9_setfam_1(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_waybel_7)).

fof(redefinition_k9_setfam_1,axiom,(
    ! [X1] : k9_setfam_1(X1) = k1_zfmisc_1(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

fof(t11_yellow_5,axiom,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & v1_lattice3(X1)
        & v2_lattice3(X1)
        & v11_waybel_1(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r6_waybel_1(X1,X2,X3)
              <=> X3 = k7_waybel_1(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_yellow_5)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc8_waybel_1)).

fof(t45_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => X2 = k2_xboole_0(X1,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(dt_k6_subset_1,axiom,(
    ! [X1,X2] : m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(fc1_waybel_7,axiom,(
    ! [X1] :
      ( v1_orders_2(k3_yellow_1(X1))
      & v11_waybel_1(k3_yellow_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_waybel_7)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t9_waybel_7,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
     => k7_waybel_1(k3_yellow_1(X1),X2) = k6_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_waybel_7)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(c_0_21,plain,(
    ! [X29,X30,X31] :
      ( ( k13_lattice3(k3_yellow_1(X29),X30,X31) = k2_xboole_0(X30,X31)
        | ~ m1_subset_1(X31,u1_struct_0(k3_yellow_1(X29)))
        | ~ m1_subset_1(X30,u1_struct_0(k3_yellow_1(X29))) )
      & ( k12_lattice3(k3_yellow_1(X29),X30,X31) = k3_xboole_0(X30,X31)
        | ~ m1_subset_1(X31,u1_struct_0(k3_yellow_1(X29)))
        | ~ m1_subset_1(X30,u1_struct_0(k3_yellow_1(X29))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t17_yellow_1])])])])).

fof(c_0_22,plain,(
    ! [X15,X16,X17] :
      ( ~ v5_orders_2(X15)
      | ~ v2_lattice3(X15)
      | ~ l1_orders_2(X15)
      | ~ m1_subset_1(X16,u1_struct_0(X15))
      | ~ m1_subset_1(X17,u1_struct_0(X15))
      | k12_lattice3(X15,X16,X17) = k11_lattice3(X15,X16,X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k12_lattice3])])).

fof(c_0_23,plain,(
    ! [X14] :
      ( ~ v2_struct_0(k3_yellow_1(X14))
      & v1_orders_2(k3_yellow_1(X14))
      & v3_orders_2(k3_yellow_1(X14))
      & v4_orders_2(k3_yellow_1(X14))
      & v5_orders_2(k3_yellow_1(X14)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc7_yellow_1])])).

fof(c_0_24,plain,(
    ! [X10] :
      ( v1_orders_2(k3_yellow_1(X10))
      & l1_orders_2(k3_yellow_1(X10)) ) ),
    inference(variable_rename,[status(thm)],[dt_k3_yellow_1])).

fof(c_0_25,plain,(
    ! [X5,X6,X7] :
      ( ( k10_lattice3(X5,X6,X7) = k4_yellow_0(X5)
        | ~ r6_waybel_1(X5,X6,X7)
        | ~ m1_subset_1(X7,u1_struct_0(X5))
        | ~ m1_subset_1(X6,u1_struct_0(X5))
        | v2_struct_0(X5)
        | ~ l1_orders_2(X5) )
      & ( k11_lattice3(X5,X6,X7) = k3_yellow_0(X5)
        | ~ r6_waybel_1(X5,X6,X7)
        | ~ m1_subset_1(X7,u1_struct_0(X5))
        | ~ m1_subset_1(X6,u1_struct_0(X5))
        | v2_struct_0(X5)
        | ~ l1_orders_2(X5) )
      & ( k10_lattice3(X5,X6,X7) != k4_yellow_0(X5)
        | k11_lattice3(X5,X6,X7) != k3_yellow_0(X5)
        | r6_waybel_1(X5,X6,X7)
        | ~ m1_subset_1(X7,u1_struct_0(X5))
        | ~ m1_subset_1(X6,u1_struct_0(X5))
        | v2_struct_0(X5)
        | ~ l1_orders_2(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d23_waybel_1])])])])])).

cnf(c_0_26,plain,
    ( k12_lattice3(k3_yellow_1(X1),X2,X3) = k3_xboole_0(X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(k3_yellow_1(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( k12_lattice3(X1,X2,X3) = k11_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( v5_orders_2(k3_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( l1_orders_2(k3_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_30,plain,(
    ! [X33] : k4_yellow_0(k3_yellow_1(X33)) = X33 ),
    inference(variable_rename,[status(thm)],[t19_yellow_1])).

fof(c_0_31,plain,(
    ! [X32] : k3_yellow_0(k3_yellow_1(X32)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t18_yellow_1])).

fof(c_0_32,plain,(
    ! [X18,X19,X20] :
      ( ~ v5_orders_2(X18)
      | ~ v1_lattice3(X18)
      | ~ l1_orders_2(X18)
      | ~ m1_subset_1(X19,u1_struct_0(X18))
      | ~ m1_subset_1(X20,u1_struct_0(X18))
      | k13_lattice3(X18,X19,X20) = k10_lattice3(X18,X19,X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k13_lattice3])])).

fof(c_0_33,plain,(
    ! [X38] : u1_struct_0(k3_yellow_1(X38)) = k9_setfam_1(X38) ),
    inference(variable_rename,[status(thm)],[t4_waybel_7])).

fof(c_0_34,plain,(
    ! [X23] : k9_setfam_1(X23) = k1_zfmisc_1(X23) ),
    inference(variable_rename,[status(thm)],[redefinition_k9_setfam_1])).

fof(c_0_35,plain,(
    ! [X26,X27,X28] :
      ( ( ~ r6_waybel_1(X26,X27,X28)
        | X28 = k7_waybel_1(X26,X27)
        | ~ m1_subset_1(X28,u1_struct_0(X26))
        | ~ m1_subset_1(X27,u1_struct_0(X26))
        | ~ v3_orders_2(X26)
        | ~ v4_orders_2(X26)
        | ~ v5_orders_2(X26)
        | ~ v1_lattice3(X26)
        | ~ v2_lattice3(X26)
        | ~ v11_waybel_1(X26)
        | ~ l1_orders_2(X26) )
      & ( X28 != k7_waybel_1(X26,X27)
        | r6_waybel_1(X26,X27,X28)
        | ~ m1_subset_1(X28,u1_struct_0(X26))
        | ~ m1_subset_1(X27,u1_struct_0(X26))
        | ~ v3_orders_2(X26)
        | ~ v4_orders_2(X26)
        | ~ v5_orders_2(X26)
        | ~ v1_lattice3(X26)
        | ~ v2_lattice3(X26)
        | ~ v11_waybel_1(X26)
        | ~ l1_orders_2(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_yellow_5])])])])).

fof(c_0_36,plain,(
    ! [X4] :
      ( ( ~ v2_struct_0(X4)
        | v2_struct_0(X4)
        | ~ v11_waybel_1(X4)
        | ~ l1_orders_2(X4) )
      & ( v3_orders_2(X4)
        | v2_struct_0(X4)
        | ~ v11_waybel_1(X4)
        | ~ l1_orders_2(X4) )
      & ( v4_orders_2(X4)
        | v2_struct_0(X4)
        | ~ v11_waybel_1(X4)
        | ~ l1_orders_2(X4) )
      & ( v5_orders_2(X4)
        | v2_struct_0(X4)
        | ~ v11_waybel_1(X4)
        | ~ l1_orders_2(X4) )
      & ( v1_lattice3(X4)
        | v2_struct_0(X4)
        | ~ v11_waybel_1(X4)
        | ~ l1_orders_2(X4) )
      & ( v2_lattice3(X4)
        | v2_struct_0(X4)
        | ~ v11_waybel_1(X4)
        | ~ l1_orders_2(X4) )
      & ( v3_yellow_0(X4)
        | v2_struct_0(X4)
        | ~ v11_waybel_1(X4)
        | ~ l1_orders_2(X4) )
      & ( v2_waybel_1(X4)
        | v2_struct_0(X4)
        | ~ v11_waybel_1(X4)
        | ~ l1_orders_2(X4) )
      & ( v10_waybel_1(X4)
        | v2_struct_0(X4)
        | ~ v11_waybel_1(X4)
        | ~ l1_orders_2(X4) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc8_waybel_1])])])])).

cnf(c_0_37,plain,
    ( r6_waybel_1(X1,X2,X3)
    | v2_struct_0(X1)
    | k10_lattice3(X1,X2,X3) != k4_yellow_0(X1)
    | k11_lattice3(X1,X2,X3) != k3_yellow_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_38,plain,
    ( k11_lattice3(k3_yellow_1(X1),X2,X3) = k3_xboole_0(X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(k3_yellow_1(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
    | ~ v2_lattice3(k3_yellow_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29])])).

cnf(c_0_39,plain,
    ( k4_yellow_0(k3_yellow_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,plain,
    ( k3_yellow_0(k3_yellow_1(X1)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_41,plain,
    ( ~ v2_struct_0(k3_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_42,plain,
    ( k13_lattice3(k3_yellow_1(X1),X2,X3) = k2_xboole_0(X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(k3_yellow_1(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_43,plain,
    ( k13_lattice3(X1,X2,X3) = k10_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_44,plain,(
    ! [X36,X37] :
      ( ~ r1_tarski(X36,X37)
      | X37 = k2_xboole_0(X36,k4_xboole_0(X37,X36)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_xboole_1])])).

fof(c_0_45,plain,(
    ! [X21,X22] : k6_subset_1(X21,X22) = k4_xboole_0(X21,X22) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

fof(c_0_46,plain,(
    ! [X11,X12] : m1_subset_1(k6_subset_1(X11,X12),k1_zfmisc_1(X11)) ),
    inference(variable_rename,[status(thm)],[dt_k6_subset_1])).

cnf(c_0_47,plain,
    ( u1_struct_0(k3_yellow_1(X1)) = k9_setfam_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_48,plain,
    ( k9_setfam_1(X1) = k1_zfmisc_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_49,plain,(
    ! [X34,X35] :
      ( ( ~ m1_subset_1(X34,k1_zfmisc_1(X35))
        | r1_tarski(X34,X35) )
      & ( ~ r1_tarski(X34,X35)
        | m1_subset_1(X34,k1_zfmisc_1(X35)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_50,plain,
    ( X3 = k7_waybel_1(X1,X2)
    | ~ r6_waybel_1(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ v11_waybel_1(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_51,plain,
    ( v2_lattice3(X1)
    | v2_struct_0(X1)
    | ~ v11_waybel_1(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_52,plain,
    ( v3_orders_2(X1)
    | v2_struct_0(X1)
    | ~ v11_waybel_1(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_53,plain,
    ( v4_orders_2(X1)
    | v2_struct_0(X1)
    | ~ v11_waybel_1(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_54,plain,
    ( v5_orders_2(X1)
    | v2_struct_0(X1)
    | ~ v11_waybel_1(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_55,plain,
    ( v1_lattice3(X1)
    | v2_struct_0(X1)
    | ~ v11_waybel_1(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_56,plain,(
    ! [X13] :
      ( v1_orders_2(k3_yellow_1(X13))
      & v11_waybel_1(k3_yellow_1(X13)) ) ),
    inference(variable_rename,[status(thm)],[fc1_waybel_7])).

cnf(c_0_57,plain,
    ( r6_waybel_1(k3_yellow_1(X1),X2,X3)
    | k10_lattice3(k3_yellow_1(X1),X2,X3) != X1
    | k3_xboole_0(X2,X3) != k1_xboole_0
    | ~ m1_subset_1(X3,u1_struct_0(k3_yellow_1(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
    | ~ v2_lattice3(k3_yellow_1(X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39]),c_0_40]),c_0_29])]),c_0_41])).

cnf(c_0_58,plain,
    ( k10_lattice3(k3_yellow_1(X1),X2,X3) = k2_xboole_0(X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(k3_yellow_1(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
    | ~ v1_lattice3(k3_yellow_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_28]),c_0_29])])).

cnf(c_0_59,plain,
    ( X2 = k2_xboole_0(X1,k4_xboole_0(X2,X1))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_60,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_61,plain,
    ( m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_62,plain,
    ( u1_struct_0(k3_yellow_1(X1)) = k1_zfmisc_1(X1) ),
    inference(rw,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_63,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

fof(c_0_64,plain,(
    ! [X39,X40] : r1_xboole_0(k4_xboole_0(X39,X40),X40) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

cnf(c_0_65,plain,
    ( X1 = k7_waybel_1(X2,X3)
    | v2_struct_0(X2)
    | ~ r6_waybel_1(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v11_waybel_1(X2)
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52]),c_0_53]),c_0_54]),c_0_55])).

cnf(c_0_66,plain,
    ( v11_waybel_1(k3_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_67,plain,
    ( r6_waybel_1(k3_yellow_1(k2_xboole_0(X1,X2)),X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0
    | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_xboole_0(X1,X2))))
    | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_xboole_0(X1,X2))))
    | ~ v2_lattice3(k3_yellow_1(k2_xboole_0(X1,X2)))
    | ~ v1_lattice3(k3_yellow_1(k2_xboole_0(X1,X2))) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58])])).

cnf(c_0_68,plain,
    ( X2 = k2_xboole_0(X1,k6_subset_1(X2,X1))
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_69,plain,
    ( m1_subset_1(k6_subset_1(X1,X2),u1_struct_0(k3_yellow_1(X1))) ),
    inference(rw,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_70,plain,
    ( m1_subset_1(X1,u1_struct_0(k3_yellow_1(X2)))
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_63,c_0_62])).

fof(c_0_71,plain,(
    ! [X24,X25] :
      ( ~ r1_xboole_0(X24,X25)
      | r1_xboole_0(X25,X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_72,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

fof(c_0_73,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
       => k7_waybel_1(k3_yellow_1(X1),X2) = k6_subset_1(X1,X2) ) ),
    inference(assume_negation,[status(cth)],[t9_waybel_7])).

cnf(c_0_74,plain,
    ( X1 = k7_waybel_1(k3_yellow_1(X2),X3)
    | ~ r6_waybel_1(k3_yellow_1(X2),X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(k3_yellow_1(X2))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_29])]),c_0_41])).

cnf(c_0_75,plain,
    ( r6_waybel_1(k3_yellow_1(X1),X2,k6_subset_1(X1,X2))
    | k3_xboole_0(X2,k6_subset_1(X1,X2)) != k1_xboole_0
    | ~ r1_tarski(X2,X1)
    | ~ v2_lattice3(k3_yellow_1(X1))
    | ~ v1_lattice3(k3_yellow_1(X1)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_69])]),c_0_70])).

fof(c_0_76,plain,(
    ! [X8,X9] :
      ( ( ~ r1_xboole_0(X8,X9)
        | k3_xboole_0(X8,X9) = k1_xboole_0 )
      & ( k3_xboole_0(X8,X9) != k1_xboole_0
        | r1_xboole_0(X8,X9) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_77,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_78,plain,
    ( r1_xboole_0(k6_subset_1(X1,X2),X2) ),
    inference(rw,[status(thm)],[c_0_72,c_0_60])).

fof(c_0_79,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(k3_yellow_1(esk1_0)))
    & k7_waybel_1(k3_yellow_1(esk1_0),esk2_0) != k6_subset_1(esk1_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_73])])])).

cnf(c_0_80,plain,
    ( k7_waybel_1(k3_yellow_1(X1),X2) = k6_subset_1(X1,X2)
    | k3_xboole_0(X2,k6_subset_1(X1,X2)) != k1_xboole_0
    | ~ r1_tarski(X2,X1)
    | ~ v2_lattice3(k3_yellow_1(X1))
    | ~ v1_lattice3(k3_yellow_1(X1)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_69])]),c_0_70])).

cnf(c_0_81,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_82,plain,
    ( r1_xboole_0(X1,k6_subset_1(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_83,negated_conjecture,
    ( k7_waybel_1(k3_yellow_1(esk1_0),esk2_0) != k6_subset_1(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_84,plain,
    ( k7_waybel_1(k3_yellow_1(X1),X2) = k6_subset_1(X1,X2)
    | ~ r1_tarski(X2,X1)
    | ~ v2_lattice3(k3_yellow_1(X1))
    | ~ v1_lattice3(k3_yellow_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_82])])).

cnf(c_0_85,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_86,negated_conjecture,
    ( ~ r1_tarski(esk2_0,esk1_0)
    | ~ v2_lattice3(k3_yellow_1(esk1_0))
    | ~ v1_lattice3(k3_yellow_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_87,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X2))) ),
    inference(rw,[status(thm)],[c_0_85,c_0_62])).

cnf(c_0_88,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(k3_yellow_1(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_89,negated_conjecture,
    ( ~ v2_lattice3(k3_yellow_1(esk1_0))
    | ~ v1_lattice3(k3_yellow_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_88])])).

cnf(c_0_90,negated_conjecture,
    ( ~ v1_lattice3(k3_yellow_1(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_51]),c_0_66]),c_0_29])]),c_0_41])).

cnf(c_0_91,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_55]),c_0_66]),c_0_29])]),c_0_41]),
    [proof]).

%------------------------------------------------------------------------------
