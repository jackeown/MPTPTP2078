%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1516+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:19 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 231 expanded)
%              Number of clauses        :   51 (  94 expanded)
%              Number of leaves         :   17 (  64 expanded)
%              Depth                    :   12
%              Number of atoms          :  574 (1637 expanded)
%              Number of equality atoms :   60 ( 128 expanded)
%              Maximal formula depth    :   19 (   7 average)
%              Maximal clause size      :   50 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d21_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => ( ( ~ v2_struct_0(X1)
          & v10_lattices(X1)
          & v4_lattice3(X1)
          & l3_lattices(X1) )
       => ! [X2,X3] :
            ( m1_subset_1(X3,u1_struct_0(X1))
           => ( X3 = k15_lattice3(X1,X2)
            <=> ( r4_lattice3(X1,X3,X2)
                & ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( r4_lattice3(X1,X4,X2)
                     => r1_lattices(X1,X3,X4) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d21_lattice3)).

fof(dt_k15_lattice3,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k15_lattice3)).

fof(t23_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & v8_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => r1_lattices(X1,k4_lattices(X1,X2,X3),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_lattices)).

fof(redefinition_k4_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & l1_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k4_lattices(X1,X2,X3) = k2_lattices(X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_lattices)).

fof(dt_l3_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( l1_lattices(X1)
        & l2_lattices(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(d16_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_lattices(X1) )
     => ( v13_lattices(X1)
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ( X2 = k5_lattices(X1)
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => ( k2_lattices(X1,X2,X3) = X2
                    & k2_lattices(X1,X3,X2) = X2 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_lattices)).

fof(dt_k5_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_lattices(X1) )
     => m1_subset_1(k5_lattices(X1),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_lattices)).

fof(t26_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v4_lattices(X1)
        & l2_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( ( r1_lattices(X1,X2,X3)
                  & r1_lattices(X1,X3,X2) )
               => X2 = X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_lattices)).

fof(cc1_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( ( ~ v2_struct_0(X1)
          & v10_lattices(X1) )
       => ( ~ v2_struct_0(X1)
          & v4_lattices(X1)
          & v5_lattices(X1)
          & v6_lattices(X1)
          & v7_lattices(X1)
          & v8_lattices(X1)
          & v9_lattices(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).

fof(commutativity_k4_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & l1_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k4_lattices(X1,X2,X3) = k4_lattices(X1,X3,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k4_lattices)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

fof(d17_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( r4_lattice3(X1,X2,X3)
            <=> ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( r2_hidden(X4,X3)
                   => r1_lattices(X1,X4,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_lattice3)).

fof(dt_k4_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & l1_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k4_lattices(X1,X2,X3),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_lattices)).

fof(t50_lattice3,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v4_lattice3(X1)
        & l3_lattices(X1) )
     => ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v13_lattices(X1)
        & l3_lattices(X1)
        & k5_lattices(X1) = k15_lattice3(X1,k1_xboole_0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_lattice3)).

fof(d13_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_lattices(X1) )
     => ( v13_lattices(X1)
      <=> ? [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
            & ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ( k2_lattices(X1,X2,X3) = X2
                  & k2_lattices(X1,X3,X2) = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_lattices)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(c_0_17,plain,(
    ! [X24,X25,X26,X27] :
      ( ( r4_lattice3(X24,X26,X25)
        | X26 != k15_lattice3(X24,X25)
        | ~ m1_subset_1(X26,u1_struct_0(X24))
        | v2_struct_0(X24)
        | ~ v10_lattices(X24)
        | ~ v4_lattice3(X24)
        | ~ l3_lattices(X24)
        | v2_struct_0(X24)
        | ~ l3_lattices(X24) )
      & ( ~ m1_subset_1(X27,u1_struct_0(X24))
        | ~ r4_lattice3(X24,X27,X25)
        | r1_lattices(X24,X26,X27)
        | X26 != k15_lattice3(X24,X25)
        | ~ m1_subset_1(X26,u1_struct_0(X24))
        | v2_struct_0(X24)
        | ~ v10_lattices(X24)
        | ~ v4_lattice3(X24)
        | ~ l3_lattices(X24)
        | v2_struct_0(X24)
        | ~ l3_lattices(X24) )
      & ( m1_subset_1(esk5_3(X24,X25,X26),u1_struct_0(X24))
        | ~ r4_lattice3(X24,X26,X25)
        | X26 = k15_lattice3(X24,X25)
        | ~ m1_subset_1(X26,u1_struct_0(X24))
        | v2_struct_0(X24)
        | ~ v10_lattices(X24)
        | ~ v4_lattice3(X24)
        | ~ l3_lattices(X24)
        | v2_struct_0(X24)
        | ~ l3_lattices(X24) )
      & ( r4_lattice3(X24,esk5_3(X24,X25,X26),X25)
        | ~ r4_lattice3(X24,X26,X25)
        | X26 = k15_lattice3(X24,X25)
        | ~ m1_subset_1(X26,u1_struct_0(X24))
        | v2_struct_0(X24)
        | ~ v10_lattices(X24)
        | ~ v4_lattice3(X24)
        | ~ l3_lattices(X24)
        | v2_struct_0(X24)
        | ~ l3_lattices(X24) )
      & ( ~ r1_lattices(X24,X26,esk5_3(X24,X25,X26))
        | ~ r4_lattice3(X24,X26,X25)
        | X26 = k15_lattice3(X24,X25)
        | ~ m1_subset_1(X26,u1_struct_0(X24))
        | v2_struct_0(X24)
        | ~ v10_lattices(X24)
        | ~ v4_lattice3(X24)
        | ~ l3_lattices(X24)
        | v2_struct_0(X24)
        | ~ l3_lattices(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d21_lattice3])])])])])])).

cnf(c_0_18,plain,
    ( r1_lattices(X2,X4,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r4_lattice3(X2,X1,X3)
    | X4 != k15_lattice3(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_19,plain,(
    ! [X29,X30] :
      ( v2_struct_0(X29)
      | ~ l3_lattices(X29)
      | m1_subset_1(k15_lattice3(X29,X30),u1_struct_0(X29)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k15_lattice3])])])).

fof(c_0_20,plain,(
    ! [X41,X42,X43] :
      ( v2_struct_0(X41)
      | ~ v6_lattices(X41)
      | ~ v8_lattices(X41)
      | ~ l3_lattices(X41)
      | ~ m1_subset_1(X42,u1_struct_0(X41))
      | ~ m1_subset_1(X43,u1_struct_0(X41))
      | r1_lattices(X41,k4_lattices(X41,X42,X43),X42) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t23_lattices])])])])).

fof(c_0_21,plain,(
    ! [X38,X39,X40] :
      ( v2_struct_0(X38)
      | ~ v6_lattices(X38)
      | ~ l1_lattices(X38)
      | ~ m1_subset_1(X39,u1_struct_0(X38))
      | ~ m1_subset_1(X40,u1_struct_0(X38))
      | k4_lattices(X38,X39,X40) = k2_lattices(X38,X39,X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k4_lattices])])])).

fof(c_0_22,plain,(
    ! [X35] :
      ( ( l1_lattices(X35)
        | ~ l3_lattices(X35) )
      & ( l2_lattices(X35)
        | ~ l3_lattices(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).

fof(c_0_23,plain,(
    ! [X14,X15,X16] :
      ( ( k2_lattices(X14,X15,X16) = X15
        | ~ m1_subset_1(X16,u1_struct_0(X14))
        | X15 != k5_lattices(X14)
        | ~ m1_subset_1(X15,u1_struct_0(X14))
        | ~ v13_lattices(X14)
        | v2_struct_0(X14)
        | ~ l1_lattices(X14) )
      & ( k2_lattices(X14,X16,X15) = X15
        | ~ m1_subset_1(X16,u1_struct_0(X14))
        | X15 != k5_lattices(X14)
        | ~ m1_subset_1(X15,u1_struct_0(X14))
        | ~ v13_lattices(X14)
        | v2_struct_0(X14)
        | ~ l1_lattices(X14) )
      & ( m1_subset_1(esk3_2(X14,X15),u1_struct_0(X14))
        | X15 = k5_lattices(X14)
        | ~ m1_subset_1(X15,u1_struct_0(X14))
        | ~ v13_lattices(X14)
        | v2_struct_0(X14)
        | ~ l1_lattices(X14) )
      & ( k2_lattices(X14,X15,esk3_2(X14,X15)) != X15
        | k2_lattices(X14,esk3_2(X14,X15),X15) != X15
        | X15 = k5_lattices(X14)
        | ~ m1_subset_1(X15,u1_struct_0(X14))
        | ~ v13_lattices(X14)
        | v2_struct_0(X14)
        | ~ l1_lattices(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattices])])])])])])).

fof(c_0_24,plain,(
    ! [X34] :
      ( v2_struct_0(X34)
      | ~ l1_lattices(X34)
      | m1_subset_1(k5_lattices(X34),u1_struct_0(X34)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_lattices])])])).

fof(c_0_25,plain,(
    ! [X44,X45,X46] :
      ( v2_struct_0(X44)
      | ~ v4_lattices(X44)
      | ~ l2_lattices(X44)
      | ~ m1_subset_1(X45,u1_struct_0(X44))
      | ~ m1_subset_1(X46,u1_struct_0(X44))
      | ~ r1_lattices(X44,X45,X46)
      | ~ r1_lattices(X44,X46,X45)
      | X45 = X46 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t26_lattices])])])])).

cnf(c_0_26,plain,
    ( v2_struct_0(X2)
    | r1_lattices(X2,X4,X1)
    | X4 != k15_lattice3(X2,X3)
    | ~ l3_lattices(X2)
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ r4_lattice3(X2,X1,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2)) ),
    inference(cn,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_28,plain,(
    ! [X5] :
      ( ( ~ v2_struct_0(X5)
        | v2_struct_0(X5)
        | ~ v10_lattices(X5)
        | ~ l3_lattices(X5) )
      & ( v4_lattices(X5)
        | v2_struct_0(X5)
        | ~ v10_lattices(X5)
        | ~ l3_lattices(X5) )
      & ( v5_lattices(X5)
        | v2_struct_0(X5)
        | ~ v10_lattices(X5)
        | ~ l3_lattices(X5) )
      & ( v6_lattices(X5)
        | v2_struct_0(X5)
        | ~ v10_lattices(X5)
        | ~ l3_lattices(X5) )
      & ( v7_lattices(X5)
        | v2_struct_0(X5)
        | ~ v10_lattices(X5)
        | ~ l3_lattices(X5) )
      & ( v8_lattices(X5)
        | v2_struct_0(X5)
        | ~ v10_lattices(X5)
        | ~ l3_lattices(X5) )
      & ( v9_lattices(X5)
        | v2_struct_0(X5)
        | ~ v10_lattices(X5)
        | ~ l3_lattices(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).

cnf(c_0_29,plain,
    ( v2_struct_0(X1)
    | r1_lattices(X1,k4_lattices(X1,X2,X3),X2)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( v2_struct_0(X1)
    | k4_lattices(X1,X2,X3) = k2_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ l1_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( l1_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( k2_lattices(X1,X2,X3) = X3
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | X3 != k5_lattices(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v13_lattices(X1)
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_34,plain,(
    ! [X6,X7,X8] :
      ( v2_struct_0(X6)
      | ~ v6_lattices(X6)
      | ~ l1_lattices(X6)
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ m1_subset_1(X8,u1_struct_0(X6))
      | k4_lattices(X6,X7,X8) = k4_lattices(X6,X8,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[commutativity_k4_lattices])])])).

cnf(c_0_35,plain,
    ( v2_struct_0(X1)
    | X2 = X3
    | ~ v4_lattices(X1)
    | ~ l2_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_lattices(X1,X2,X3)
    | ~ r1_lattices(X1,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_36,plain,
    ( r1_lattices(X1,k15_lattice3(X1,X2),X3)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ r4_lattice3(X1,X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_26]),c_0_27])).

cnf(c_0_37,plain,
    ( v4_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_38,plain,
    ( l2_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_39,plain,(
    ! [X51,X52] :
      ( ~ r2_hidden(X51,X52)
      | ~ v1_xboole_0(X52) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

fof(c_0_40,plain,(
    ! [X18,X19,X20,X21,X22] :
      ( ( ~ r4_lattice3(X18,X19,X20)
        | ~ m1_subset_1(X21,u1_struct_0(X18))
        | ~ r2_hidden(X21,X20)
        | r1_lattices(X18,X21,X19)
        | ~ m1_subset_1(X19,u1_struct_0(X18))
        | v2_struct_0(X18)
        | ~ l3_lattices(X18) )
      & ( m1_subset_1(esk4_3(X18,X19,X22),u1_struct_0(X18))
        | r4_lattice3(X18,X19,X22)
        | ~ m1_subset_1(X19,u1_struct_0(X18))
        | v2_struct_0(X18)
        | ~ l3_lattices(X18) )
      & ( r2_hidden(esk4_3(X18,X19,X22),X22)
        | r4_lattice3(X18,X19,X22)
        | ~ m1_subset_1(X19,u1_struct_0(X18))
        | v2_struct_0(X18)
        | ~ l3_lattices(X18) )
      & ( ~ r1_lattices(X18,esk4_3(X18,X19,X22),X19)
        | r4_lattice3(X18,X19,X22)
        | ~ m1_subset_1(X19,u1_struct_0(X18))
        | v2_struct_0(X18)
        | ~ l3_lattices(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_lattice3])])])])])])])).

cnf(c_0_41,plain,
    ( r1_lattices(X1,k2_lattices(X1,X2,X3),X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v8_lattices(X1)
    | ~ v6_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])).

cnf(c_0_42,plain,
    ( k2_lattices(X1,X2,k5_lattices(X1)) = k5_lattices(X1)
    | v2_struct_0(X1)
    | ~ v13_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_32]),c_0_33])).

cnf(c_0_43,plain,
    ( v2_struct_0(X1)
    | k4_lattices(X1,X2,X3) = k4_lattices(X1,X3,X2)
    | ~ v6_lattices(X1)
    | ~ l1_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_44,plain,
    ( X1 = k15_lattice3(X2,X3)
    | v2_struct_0(X2)
    | ~ v4_lattice3(X2)
    | ~ r1_lattices(X2,X1,k15_lattice3(X2,X3))
    | ~ r4_lattice3(X2,X1,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37]),c_0_27]),c_0_38])).

cnf(c_0_45,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_46,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_47,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_48,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),X3)
    | r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_49,plain,(
    ! [X31,X32,X33] :
      ( v2_struct_0(X31)
      | ~ v6_lattices(X31)
      | ~ l1_lattices(X31)
      | ~ m1_subset_1(X32,u1_struct_0(X31))
      | ~ m1_subset_1(X33,u1_struct_0(X31))
      | m1_subset_1(k4_lattices(X31,X32,X33),u1_struct_0(X31)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_lattices])])])).

fof(c_0_50,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v10_lattices(X1)
          & v4_lattice3(X1)
          & l3_lattices(X1) )
       => ( ~ v2_struct_0(X1)
          & v10_lattices(X1)
          & v13_lattices(X1)
          & l3_lattices(X1)
          & k5_lattices(X1) = k15_lattice3(X1,k1_xboole_0) ) ) ),
    inference(assume_negation,[status(cth)],[t50_lattice3])).

cnf(c_0_51,plain,
    ( r1_lattices(X1,k5_lattices(X1),X2)
    | v2_struct_0(X1)
    | ~ v13_lattices(X1)
    | ~ m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v8_lattices(X1)
    | ~ v6_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_31])).

fof(c_0_52,plain,(
    ! [X9,X11,X12] :
      ( ( m1_subset_1(esk1_1(X9),u1_struct_0(X9))
        | ~ v13_lattices(X9)
        | v2_struct_0(X9)
        | ~ l1_lattices(X9) )
      & ( k2_lattices(X9,esk1_1(X9),X11) = esk1_1(X9)
        | ~ m1_subset_1(X11,u1_struct_0(X9))
        | ~ v13_lattices(X9)
        | v2_struct_0(X9)
        | ~ l1_lattices(X9) )
      & ( k2_lattices(X9,X11,esk1_1(X9)) = esk1_1(X9)
        | ~ m1_subset_1(X11,u1_struct_0(X9))
        | ~ v13_lattices(X9)
        | v2_struct_0(X9)
        | ~ l1_lattices(X9) )
      & ( m1_subset_1(esk2_2(X9,X12),u1_struct_0(X9))
        | ~ m1_subset_1(X12,u1_struct_0(X9))
        | v13_lattices(X9)
        | v2_struct_0(X9)
        | ~ l1_lattices(X9) )
      & ( k2_lattices(X9,X12,esk2_2(X9,X12)) != X12
        | k2_lattices(X9,esk2_2(X9,X12),X12) != X12
        | ~ m1_subset_1(X12,u1_struct_0(X9))
        | v13_lattices(X9)
        | v2_struct_0(X9)
        | ~ l1_lattices(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d13_lattices])])])])])])).

cnf(c_0_53,plain,
    ( k4_lattices(X1,X2,X3) = k2_lattices(X1,X3,X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v6_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_43])).

cnf(c_0_54,plain,
    ( k2_lattices(X1,k15_lattice3(X1,X2),X3) = k15_lattice3(X1,X2)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ r4_lattice3(X1,k2_lattices(X1,k15_lattice3(X1,X2),X3),X2)
    | ~ m1_subset_1(k2_lattices(X1,k15_lattice3(X1,X2),X3),u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_41]),c_0_45]),c_0_46]),c_0_27])).

cnf(c_0_55,plain,
    ( r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ v1_xboole_0(X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_56,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k4_lattices(X1,X2,X3),u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ l1_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

fof(c_0_57,negated_conjecture,
    ( ~ v2_struct_0(esk7_0)
    & v10_lattices(esk7_0)
    & v4_lattice3(esk7_0)
    & l3_lattices(esk7_0)
    & ( v2_struct_0(esk7_0)
      | ~ v10_lattices(esk7_0)
      | ~ v13_lattices(esk7_0)
      | ~ l3_lattices(esk7_0)
      | k5_lattices(esk7_0) != k15_lattice3(esk7_0,k1_xboole_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_50])])])])).

fof(c_0_58,plain,(
    ! [X50] :
      ( ~ v1_xboole_0(X50)
      | X50 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_59,plain,
    ( X1 = k5_lattices(X2)
    | v2_struct_0(X2)
    | ~ r1_lattices(X2,X1,k5_lattices(X2))
    | ~ v13_lattices(X2)
    | ~ m1_subset_1(k5_lattices(X2),u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v8_lattices(X2)
    | ~ v6_lattices(X2)
    | ~ v4_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_51]),c_0_38])).

cnf(c_0_60,plain,
    ( v13_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,esk2_2(X1,X2)) != X2
    | k2_lattices(X1,esk2_2(X1,X2),X2) != X2
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_61,plain,
    ( k2_lattices(X1,X2,X3) = k2_lattices(X1,X3,X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v6_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_53])).

cnf(c_0_62,plain,
    ( m1_subset_1(esk2_2(X1,X2),u1_struct_0(X1))
    | v13_lattices(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_63,plain,
    ( k2_lattices(X1,k15_lattice3(X1,X2),X3) = k15_lattice3(X1,X2)
    | v2_struct_0(X1)
    | ~ v1_xboole_0(X2)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(k2_lattices(X1,k15_lattice3(X1,X2),X3),u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_64,plain,
    ( m1_subset_1(k2_lattices(X1,X2,X3),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v6_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_30])).

cnf(c_0_65,negated_conjecture,
    ( v2_struct_0(esk7_0)
    | ~ v10_lattices(esk7_0)
    | ~ v13_lattices(esk7_0)
    | ~ l3_lattices(esk7_0)
    | k5_lattices(esk7_0) != k15_lattice3(esk7_0,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_66,negated_conjecture,
    ( l3_lattices(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_67,negated_conjecture,
    ( v10_lattices(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_68,negated_conjecture,
    ( ~ v2_struct_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_69,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_70,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

cnf(c_0_71,plain,
    ( k15_lattice3(X1,X2) = k5_lattices(X1)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ r4_lattice3(X1,k5_lattices(X1),X2)
    | ~ v13_lattices(X1)
    | ~ m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_36]),c_0_37]),c_0_45]),c_0_46]),c_0_27])).

cnf(c_0_72,plain,
    ( v13_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,esk2_2(X1,X2)) != X2
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v6_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_62])).

cnf(c_0_73,plain,
    ( k2_lattices(X1,k15_lattice3(X1,X2),X3) = k15_lattice3(X1,X2)
    | v2_struct_0(X1)
    | ~ v1_xboole_0(X2)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_45]),c_0_31]),c_0_27])).

cnf(c_0_74,negated_conjecture,
    ( k15_lattice3(esk7_0,k1_xboole_0) != k5_lattices(esk7_0)
    | ~ v13_lattices(esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_66]),c_0_67])]),c_0_68])).

cnf(c_0_75,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_76,plain,
    ( k15_lattice3(X1,X2) = k5_lattices(X1)
    | v2_struct_0(X1)
    | ~ v1_xboole_0(X2)
    | ~ v4_lattice3(X1)
    | ~ v13_lattices(X1)
    | ~ m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_71,c_0_55])).

cnf(c_0_77,plain,
    ( v13_lattices(X1)
    | v2_struct_0(X1)
    | ~ v1_xboole_0(X2)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(esk2_2(X1,k15_lattice3(X1,X2)),u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_45]),c_0_31]),c_0_27])).

cnf(c_0_78,negated_conjecture,
    ( k15_lattice3(esk7_0,o_0_0_xboole_0) != k5_lattices(esk7_0)
    | ~ v13_lattices(esk7_0) ),
    inference(rw,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_79,plain,
    ( k15_lattice3(X1,X2) = k5_lattices(X1)
    | v2_struct_0(X1)
    | ~ v1_xboole_0(X2)
    | ~ v4_lattice3(X1)
    | ~ v13_lattices(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_33]),c_0_31])).

cnf(c_0_80,negated_conjecture,
    ( v4_lattice3(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_81,plain,
    ( v13_lattices(X1)
    | v2_struct_0(X1)
    | ~ v1_xboole_0(X2)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_62]),c_0_31]),c_0_27])).

cnf(c_0_82,negated_conjecture,
    ( ~ v13_lattices(esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_70]),c_0_80]),c_0_67]),c_0_66])]),c_0_68])).

cnf(c_0_83,plain,
    ( v13_lattices(X1)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_81,c_0_70])).

cnf(c_0_84,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_80]),c_0_67]),c_0_66])]),c_0_68]),
    [proof]).

%------------------------------------------------------------------------------
