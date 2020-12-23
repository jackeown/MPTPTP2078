%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:06 EST 2020

% Result     : Theorem 1.28s
% Output     : CNFRefutation 1.28s
% Verified   : 
% Statistics : Number of formulae       :  174 (5165 expanded)
%              Number of clauses        :  121 (1855 expanded)
%              Number of leaves         :   26 (1252 expanded)
%              Depth                    :   21
%              Number of atoms          :  903 (32652 expanded)
%              Number of equality atoms :  100 (3347 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal clause size      :   50 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(dt_k5_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_lattices(X1) )
     => m1_subset_1(k5_lattices(X1),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_lattices)).

fof(dt_l3_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( l1_lattices(X1)
        & l2_lattices(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t34_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v4_lattice3(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( X2 = k16_lattice3(X1,X3)
            <=> ( r3_lattice3(X1,X2,X3)
                & ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( r3_lattice3(X1,X4,X3)
                     => r3_lattices(X1,X4,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_lattice3)).

fof(dt_k16_lattice3,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => m1_subset_1(k16_lattice3(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k16_lattice3)).

fof(dt_k15_lattice3,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k15_lattice3)).

fof(t108_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k3_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_xboole_1)).

fof(t37_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v4_lattice3(X1)
        & l3_lattices(X1) )
     => ! [X2] : k15_lattice3(X1,X2) = k16_lattice3(X1,a_2_2_lattice3(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_lattice3)).

fof(d16_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( r3_lattice3(X1,X2,X3)
            <=> ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( r2_hidden(X4,X3)
                   => r1_lattices(X1,X2,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_lattice3)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t48_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v4_lattice3(X1)
        & l3_lattices(X1) )
     => ! [X2,X3] :
          ( ! [X4] :
              ( m1_subset_1(X4,u1_struct_0(X1))
             => ~ ( r2_hidden(X4,X2)
                  & ! [X5] :
                      ( m1_subset_1(X5,u1_struct_0(X1))
                     => ~ ( r3_lattices(X1,X4,X5)
                          & r2_hidden(X5,X3) ) ) ) )
         => r3_lattices(X1,k15_lattice3(X1,X2),k15_lattice3(X1,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_lattice3)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(fraenkel_a_2_2_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X2)
        & v10_lattices(X2)
        & v4_lattice3(X2)
        & l3_lattices(X2) )
     => ( r2_hidden(X1,a_2_2_lattice3(X2,X3))
      <=> ? [X4] :
            ( m1_subset_1(X4,u1_struct_0(X2))
            & X1 = X4
            & r4_lattice3(X2,X4,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_2_lattice3)).

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

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(fraenkel_a_2_6_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X2)
        & v10_lattices(X2)
        & v4_lattice3(X2)
        & l3_lattices(X2) )
     => ( r2_hidden(X1,a_2_6_lattice3(X2,X3))
      <=> ? [X4] :
            ( m1_subset_1(X4,u1_struct_0(X2))
            & X1 = X4
            & ? [X5] :
                ( m1_subset_1(X5,u1_struct_0(X2))
                & r3_lattices(X2,X5,X4)
                & r2_hidden(X5,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_6_lattice3)).

fof(t43_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v4_lattice3(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( k15_lattice3(X1,k6_domain_1(u1_struct_0(X1),X2)) = X2
            & k16_lattice3(X1,k6_domain_1(u1_struct_0(X1),X2)) = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_lattice3)).

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

fof(t21_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v8_lattices(X1)
        & v9_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r1_lattices(X1,X2,X3)
              <=> k2_lattices(X1,X2,X3) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_lattices)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t47_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v4_lattice3(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( k15_lattice3(X1,X2) = k15_lattice3(X1,a_2_5_lattice3(X1,X2))
          & k16_lattice3(X1,X2) = k16_lattice3(X1,a_2_6_lattice3(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_lattice3)).

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

fof(d6_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_lattices(X1) )
     => ( v6_lattices(X1)
      <=> ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => k2_lattices(X1,X2,X3) = k2_lattices(X1,X3,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_lattices)).

fof(c_0_26,negated_conjecture,(
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

fof(c_0_27,plain,(
    ! [X30] :
      ( v2_struct_0(X30)
      | ~ l1_lattices(X30)
      | m1_subset_1(k5_lattices(X30),u1_struct_0(X30)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_lattices])])])).

fof(c_0_28,plain,(
    ! [X31] :
      ( ( l1_lattices(X31)
        | ~ l3_lattices(X31) )
      & ( l2_lattices(X31)
        | ~ l3_lattices(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).

fof(c_0_29,plain,(
    ! [X19,X20,X21] :
      ( ~ r1_tarski(X19,X20)
      | ~ r1_tarski(X20,X21)
      | r1_tarski(X19,X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_30,plain,(
    ! [X22] : r1_tarski(k1_xboole_0,X22) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_31,plain,(
    ! [X82,X83,X84,X85,X86] :
      ( ( r3_lattice3(X82,X83,X84)
        | X83 != k16_lattice3(X82,X84)
        | ~ m1_subset_1(X83,u1_struct_0(X82))
        | v2_struct_0(X82)
        | ~ v10_lattices(X82)
        | ~ v4_lattice3(X82)
        | ~ l3_lattices(X82) )
      & ( ~ m1_subset_1(X85,u1_struct_0(X82))
        | ~ r3_lattice3(X82,X85,X84)
        | r3_lattices(X82,X85,X83)
        | X83 != k16_lattice3(X82,X84)
        | ~ m1_subset_1(X83,u1_struct_0(X82))
        | v2_struct_0(X82)
        | ~ v10_lattices(X82)
        | ~ v4_lattice3(X82)
        | ~ l3_lattices(X82) )
      & ( m1_subset_1(esk14_3(X82,X83,X86),u1_struct_0(X82))
        | ~ r3_lattice3(X82,X83,X86)
        | X83 = k16_lattice3(X82,X86)
        | ~ m1_subset_1(X83,u1_struct_0(X82))
        | v2_struct_0(X82)
        | ~ v10_lattices(X82)
        | ~ v4_lattice3(X82)
        | ~ l3_lattices(X82) )
      & ( r3_lattice3(X82,esk14_3(X82,X83,X86),X86)
        | ~ r3_lattice3(X82,X83,X86)
        | X83 = k16_lattice3(X82,X86)
        | ~ m1_subset_1(X83,u1_struct_0(X82))
        | v2_struct_0(X82)
        | ~ v10_lattices(X82)
        | ~ v4_lattice3(X82)
        | ~ l3_lattices(X82) )
      & ( ~ r3_lattices(X82,esk14_3(X82,X83,X86),X83)
        | ~ r3_lattice3(X82,X83,X86)
        | X83 = k16_lattice3(X82,X86)
        | ~ m1_subset_1(X83,u1_struct_0(X82))
        | v2_struct_0(X82)
        | ~ v10_lattices(X82)
        | ~ v4_lattice3(X82)
        | ~ l3_lattices(X82) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_lattice3])])])])])])])).

fof(c_0_32,plain,(
    ! [X58,X59] :
      ( v2_struct_0(X58)
      | ~ l3_lattices(X58)
      | m1_subset_1(k16_lattice3(X58,X59),u1_struct_0(X58)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k16_lattice3])])])).

fof(c_0_33,plain,(
    ! [X56,X57] :
      ( v2_struct_0(X56)
      | ~ l3_lattices(X56)
      | m1_subset_1(k15_lattice3(X56,X57),u1_struct_0(X56)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k15_lattice3])])])).

fof(c_0_34,negated_conjecture,
    ( ~ v2_struct_0(esk16_0)
    & v10_lattices(esk16_0)
    & v4_lattice3(esk16_0)
    & l3_lattices(esk16_0)
    & ( v2_struct_0(esk16_0)
      | ~ v10_lattices(esk16_0)
      | ~ v13_lattices(esk16_0)
      | ~ l3_lattices(esk16_0)
      | k5_lattices(esk16_0) != k15_lattice3(esk16_0,k1_xboole_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_26])])])])).

cnf(c_0_35,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,plain,
    ( l1_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_39,plain,(
    ! [X14,X15,X16] :
      ( ~ r1_tarski(X14,X15)
      | r1_tarski(k3_xboole_0(X14,X16),X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t108_xboole_1])])).

cnf(c_0_40,plain,
    ( r3_lattices(X2,X1,X4)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r3_lattice3(X2,X1,X3)
    | X4 != k16_lattice3(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_41,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k16_lattice3(X1,X2),u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_42,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_43,negated_conjecture,
    ( l3_lattices(esk16_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_44,negated_conjecture,
    ( ~ v2_struct_0(esk16_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_45,plain,(
    ! [X88,X89] :
      ( v2_struct_0(X88)
      | ~ v10_lattices(X88)
      | ~ v4_lattice3(X88)
      | ~ l3_lattices(X88)
      | k15_lattice3(X88,X89) = k16_lattice3(X88,a_2_2_lattice3(X88,X89)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t37_lattice3])])])])).

cnf(c_0_46,plain,
    ( r3_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | X2 != k16_lattice3(X1,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_47,plain,(
    ! [X40,X41,X42,X43,X44] :
      ( ( ~ r3_lattice3(X40,X41,X42)
        | ~ m1_subset_1(X43,u1_struct_0(X40))
        | ~ r2_hidden(X43,X42)
        | r1_lattices(X40,X41,X43)
        | ~ m1_subset_1(X41,u1_struct_0(X40))
        | v2_struct_0(X40)
        | ~ l3_lattices(X40) )
      & ( m1_subset_1(esk5_3(X40,X41,X44),u1_struct_0(X40))
        | r3_lattice3(X40,X41,X44)
        | ~ m1_subset_1(X41,u1_struct_0(X40))
        | v2_struct_0(X40)
        | ~ l3_lattices(X40) )
      & ( r2_hidden(esk5_3(X40,X41,X44),X44)
        | r3_lattice3(X40,X41,X44)
        | ~ m1_subset_1(X41,u1_struct_0(X40))
        | v2_struct_0(X40)
        | ~ l3_lattices(X40) )
      & ( ~ r1_lattices(X40,X41,esk5_3(X40,X41,X44))
        | r3_lattice3(X40,X41,X44)
        | ~ m1_subset_1(X41,u1_struct_0(X40))
        | v2_struct_0(X40)
        | ~ l3_lattices(X40) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattice3])])])])])])])).

cnf(c_0_48,plain,
    ( m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

fof(c_0_49,plain,(
    ! [X23,X24] :
      ( ~ r2_hidden(X23,X24)
      | ~ r1_tarski(X24,X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_50,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_51,plain,
    ( r1_tarski(k3_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_52,plain,(
    ! [X97,X98,X99,X101] :
      ( ( m1_subset_1(esk15_3(X97,X98,X99),u1_struct_0(X97))
        | r3_lattices(X97,k15_lattice3(X97,X98),k15_lattice3(X97,X99))
        | v2_struct_0(X97)
        | ~ v10_lattices(X97)
        | ~ v4_lattice3(X97)
        | ~ l3_lattices(X97) )
      & ( r2_hidden(esk15_3(X97,X98,X99),X98)
        | r3_lattices(X97,k15_lattice3(X97,X98),k15_lattice3(X97,X99))
        | v2_struct_0(X97)
        | ~ v10_lattices(X97)
        | ~ v4_lattice3(X97)
        | ~ l3_lattices(X97) )
      & ( ~ m1_subset_1(X101,u1_struct_0(X97))
        | ~ r3_lattices(X97,esk15_3(X97,X98,X99),X101)
        | ~ r2_hidden(X101,X99)
        | r3_lattices(X97,k15_lattice3(X97,X98),k15_lattice3(X97,X99))
        | v2_struct_0(X97)
        | ~ v10_lattices(X97)
        | ~ v4_lattice3(X97)
        | ~ l3_lattices(X97) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t48_lattice3])])])])])])).

fof(c_0_53,plain,(
    ! [X12,X13] :
      ( ( r1_tarski(X12,X13)
        | X12 != X13 )
      & ( r1_tarski(X13,X12)
        | X12 != X13 )
      & ( ~ r1_tarski(X12,X13)
        | ~ r1_tarski(X13,X12)
        | X12 = X13 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_54,plain,(
    ! [X60,X61,X62,X64,X65] :
      ( ( m1_subset_1(esk9_3(X60,X61,X62),u1_struct_0(X61))
        | ~ r2_hidden(X60,a_2_2_lattice3(X61,X62))
        | v2_struct_0(X61)
        | ~ v10_lattices(X61)
        | ~ v4_lattice3(X61)
        | ~ l3_lattices(X61) )
      & ( X60 = esk9_3(X60,X61,X62)
        | ~ r2_hidden(X60,a_2_2_lattice3(X61,X62))
        | v2_struct_0(X61)
        | ~ v10_lattices(X61)
        | ~ v4_lattice3(X61)
        | ~ l3_lattices(X61) )
      & ( r4_lattice3(X61,esk9_3(X60,X61,X62),X62)
        | ~ r2_hidden(X60,a_2_2_lattice3(X61,X62))
        | v2_struct_0(X61)
        | ~ v10_lattices(X61)
        | ~ v4_lattice3(X61)
        | ~ l3_lattices(X61) )
      & ( ~ m1_subset_1(X65,u1_struct_0(X61))
        | X60 != X65
        | ~ r4_lattice3(X61,X65,X64)
        | r2_hidden(X60,a_2_2_lattice3(X61,X64))
        | v2_struct_0(X61)
        | ~ v10_lattices(X61)
        | ~ v4_lattice3(X61)
        | ~ l3_lattices(X61) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_2_lattice3])])])])])])])).

fof(c_0_55,plain,(
    ! [X46,X47,X48,X49] :
      ( ( r4_lattice3(X46,X48,X47)
        | X48 != k15_lattice3(X46,X47)
        | ~ m1_subset_1(X48,u1_struct_0(X46))
        | v2_struct_0(X46)
        | ~ v10_lattices(X46)
        | ~ v4_lattice3(X46)
        | ~ l3_lattices(X46)
        | v2_struct_0(X46)
        | ~ l3_lattices(X46) )
      & ( ~ m1_subset_1(X49,u1_struct_0(X46))
        | ~ r4_lattice3(X46,X49,X47)
        | r1_lattices(X46,X48,X49)
        | X48 != k15_lattice3(X46,X47)
        | ~ m1_subset_1(X48,u1_struct_0(X46))
        | v2_struct_0(X46)
        | ~ v10_lattices(X46)
        | ~ v4_lattice3(X46)
        | ~ l3_lattices(X46)
        | v2_struct_0(X46)
        | ~ l3_lattices(X46) )
      & ( m1_subset_1(esk6_3(X46,X47,X48),u1_struct_0(X46))
        | ~ r4_lattice3(X46,X48,X47)
        | X48 = k15_lattice3(X46,X47)
        | ~ m1_subset_1(X48,u1_struct_0(X46))
        | v2_struct_0(X46)
        | ~ v10_lattices(X46)
        | ~ v4_lattice3(X46)
        | ~ l3_lattices(X46)
        | v2_struct_0(X46)
        | ~ l3_lattices(X46) )
      & ( r4_lattice3(X46,esk6_3(X46,X47,X48),X47)
        | ~ r4_lattice3(X46,X48,X47)
        | X48 = k15_lattice3(X46,X47)
        | ~ m1_subset_1(X48,u1_struct_0(X46))
        | v2_struct_0(X46)
        | ~ v10_lattices(X46)
        | ~ v4_lattice3(X46)
        | ~ l3_lattices(X46)
        | v2_struct_0(X46)
        | ~ l3_lattices(X46) )
      & ( ~ r1_lattices(X46,X48,esk6_3(X46,X47,X48))
        | ~ r4_lattice3(X46,X48,X47)
        | X48 = k15_lattice3(X46,X47)
        | ~ m1_subset_1(X48,u1_struct_0(X46))
        | v2_struct_0(X46)
        | ~ v10_lattices(X46)
        | ~ v4_lattice3(X46)
        | ~ l3_lattices(X46)
        | v2_struct_0(X46)
        | ~ l3_lattices(X46) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d21_lattice3])])])])])])).

cnf(c_0_56,plain,
    ( r3_lattices(X1,X2,k16_lattice3(X1,X3))
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ r3_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_40]),c_0_41])).

cnf(c_0_57,negated_conjecture,
    ( m1_subset_1(k15_lattice3(esk16_0,X1),u1_struct_0(esk16_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44])).

cnf(c_0_58,negated_conjecture,
    ( v4_lattice3(esk16_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_59,negated_conjecture,
    ( v10_lattices(esk16_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_60,plain,
    ( v2_struct_0(X1)
    | k15_lattice3(X1,X2) = k16_lattice3(X1,a_2_2_lattice3(X1,X2))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_61,plain,
    ( r3_lattice3(X1,k16_lattice3(X1,X2),X2)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_46]),c_0_41])).

fof(c_0_62,plain,(
    ! [X25] :
      ( ( ~ v2_struct_0(X25)
        | v2_struct_0(X25)
        | ~ v10_lattices(X25)
        | ~ l3_lattices(X25) )
      & ( v4_lattices(X25)
        | v2_struct_0(X25)
        | ~ v10_lattices(X25)
        | ~ l3_lattices(X25) )
      & ( v5_lattices(X25)
        | v2_struct_0(X25)
        | ~ v10_lattices(X25)
        | ~ l3_lattices(X25) )
      & ( v6_lattices(X25)
        | v2_struct_0(X25)
        | ~ v10_lattices(X25)
        | ~ l3_lattices(X25) )
      & ( v7_lattices(X25)
        | v2_struct_0(X25)
        | ~ v10_lattices(X25)
        | ~ l3_lattices(X25) )
      & ( v8_lattices(X25)
        | v2_struct_0(X25)
        | ~ v10_lattices(X25)
        | ~ l3_lattices(X25) )
      & ( v9_lattices(X25)
        | v2_struct_0(X25)
        | ~ v10_lattices(X25)
        | ~ l3_lattices(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).

cnf(c_0_63,plain,
    ( r1_lattices(X1,X2,X4)
    | v2_struct_0(X1)
    | ~ r3_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_64,negated_conjecture,
    ( m1_subset_1(k5_lattices(esk16_0),u1_struct_0(esk16_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_43]),c_0_44])).

cnf(c_0_65,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_66,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_67,plain,
    ( r2_hidden(esk15_3(X1,X2,X3),X2)
    | r3_lattices(X1,k15_lattice3(X1,X2),k15_lattice3(X1,X3))
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_68,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

fof(c_0_69,plain,(
    ! [X17,X18] : r1_tarski(k3_xboole_0(X17,X18),X17) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_70,plain,
    ( r2_hidden(X3,a_2_2_lattice3(X2,X4))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | X3 != X1
    | ~ r4_lattice3(X2,X1,X4)
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_71,plain,
    ( r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | v2_struct_0(X1)
    | X2 != k15_lattice3(X1,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

fof(c_0_72,plain,(
    ! [X74,X75,X76,X79,X80,X81] :
      ( ( m1_subset_1(esk12_3(X74,X75,X76),u1_struct_0(X75))
        | ~ r2_hidden(X74,a_2_6_lattice3(X75,X76))
        | v2_struct_0(X75)
        | ~ v10_lattices(X75)
        | ~ v4_lattice3(X75)
        | ~ l3_lattices(X75) )
      & ( X74 = esk12_3(X74,X75,X76)
        | ~ r2_hidden(X74,a_2_6_lattice3(X75,X76))
        | v2_struct_0(X75)
        | ~ v10_lattices(X75)
        | ~ v4_lattice3(X75)
        | ~ l3_lattices(X75) )
      & ( m1_subset_1(esk13_3(X74,X75,X76),u1_struct_0(X75))
        | ~ r2_hidden(X74,a_2_6_lattice3(X75,X76))
        | v2_struct_0(X75)
        | ~ v10_lattices(X75)
        | ~ v4_lattice3(X75)
        | ~ l3_lattices(X75) )
      & ( r3_lattices(X75,esk13_3(X74,X75,X76),esk12_3(X74,X75,X76))
        | ~ r2_hidden(X74,a_2_6_lattice3(X75,X76))
        | v2_struct_0(X75)
        | ~ v10_lattices(X75)
        | ~ v4_lattice3(X75)
        | ~ l3_lattices(X75) )
      & ( r2_hidden(esk13_3(X74,X75,X76),X76)
        | ~ r2_hidden(X74,a_2_6_lattice3(X75,X76))
        | v2_struct_0(X75)
        | ~ v10_lattices(X75)
        | ~ v4_lattice3(X75)
        | ~ l3_lattices(X75) )
      & ( ~ m1_subset_1(X80,u1_struct_0(X75))
        | X74 != X80
        | ~ m1_subset_1(X81,u1_struct_0(X75))
        | ~ r3_lattices(X75,X81,X80)
        | ~ r2_hidden(X81,X79)
        | r2_hidden(X74,a_2_6_lattice3(X75,X79))
        | v2_struct_0(X75)
        | ~ v10_lattices(X75)
        | ~ v4_lattice3(X75)
        | ~ l3_lattices(X75) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_6_lattice3])])])])])])])).

cnf(c_0_73,negated_conjecture,
    ( r3_lattices(esk16_0,k15_lattice3(esk16_0,X1),k16_lattice3(esk16_0,X2))
    | ~ r3_lattice3(esk16_0,k15_lattice3(esk16_0,X1),X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58]),c_0_59]),c_0_43])]),c_0_44])).

cnf(c_0_74,negated_conjecture,
    ( k16_lattice3(esk16_0,a_2_2_lattice3(esk16_0,X1)) = k15_lattice3(esk16_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_58]),c_0_59]),c_0_43])]),c_0_44])).

cnf(c_0_75,negated_conjecture,
    ( r3_lattice3(esk16_0,k16_lattice3(esk16_0,X1),X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_58]),c_0_59]),c_0_43])]),c_0_44])).

fof(c_0_76,plain,(
    ! [X93,X94] :
      ( ( k15_lattice3(X93,k6_domain_1(u1_struct_0(X93),X94)) = X94
        | ~ m1_subset_1(X94,u1_struct_0(X93))
        | v2_struct_0(X93)
        | ~ v10_lattices(X93)
        | ~ v4_lattice3(X93)
        | ~ l3_lattices(X93) )
      & ( k16_lattice3(X93,k6_domain_1(u1_struct_0(X93),X94)) = X94
        | ~ m1_subset_1(X94,u1_struct_0(X93))
        | v2_struct_0(X93)
        | ~ v10_lattices(X93)
        | ~ v4_lattice3(X93)
        | ~ l3_lattices(X93) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t43_lattice3])])])])])).

fof(c_0_77,plain,(
    ! [X26,X27,X28] :
      ( ( k2_lattices(X26,X27,X28) = X27
        | ~ m1_subset_1(X28,u1_struct_0(X26))
        | X27 != k5_lattices(X26)
        | ~ m1_subset_1(X27,u1_struct_0(X26))
        | ~ v13_lattices(X26)
        | v2_struct_0(X26)
        | ~ l1_lattices(X26) )
      & ( k2_lattices(X26,X28,X27) = X27
        | ~ m1_subset_1(X28,u1_struct_0(X26))
        | X27 != k5_lattices(X26)
        | ~ m1_subset_1(X27,u1_struct_0(X26))
        | ~ v13_lattices(X26)
        | v2_struct_0(X26)
        | ~ l1_lattices(X26) )
      & ( m1_subset_1(esk2_2(X26,X27),u1_struct_0(X26))
        | X27 = k5_lattices(X26)
        | ~ m1_subset_1(X27,u1_struct_0(X26))
        | ~ v13_lattices(X26)
        | v2_struct_0(X26)
        | ~ l1_lattices(X26) )
      & ( k2_lattices(X26,X27,esk2_2(X26,X27)) != X27
        | k2_lattices(X26,esk2_2(X26,X27),X27) != X27
        | X27 = k5_lattices(X26)
        | ~ m1_subset_1(X27,u1_struct_0(X26))
        | ~ v13_lattices(X26)
        | v2_struct_0(X26)
        | ~ l1_lattices(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattices])])])])])])).

fof(c_0_78,plain,(
    ! [X32,X33,X34] :
      ( ( ~ r1_lattices(X32,X33,X34)
        | k2_lattices(X32,X33,X34) = X33
        | ~ m1_subset_1(X34,u1_struct_0(X32))
        | ~ m1_subset_1(X33,u1_struct_0(X32))
        | v2_struct_0(X32)
        | ~ v8_lattices(X32)
        | ~ v9_lattices(X32)
        | ~ l3_lattices(X32) )
      & ( k2_lattices(X32,X33,X34) != X33
        | r1_lattices(X32,X33,X34)
        | ~ m1_subset_1(X34,u1_struct_0(X32))
        | ~ m1_subset_1(X33,u1_struct_0(X32))
        | v2_struct_0(X32)
        | ~ v8_lattices(X32)
        | ~ v9_lattices(X32)
        | ~ l3_lattices(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t21_lattices])])])])])).

cnf(c_0_79,plain,
    ( v9_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_80,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_81,negated_conjecture,
    ( r1_lattices(esk16_0,X1,k5_lattices(esk16_0))
    | ~ r3_lattice3(esk16_0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk16_0))
    | ~ r2_hidden(k5_lattices(esk16_0),X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_43])]),c_0_44])).

cnf(c_0_82,negated_conjecture,
    ( m1_subset_1(k16_lattice3(esk16_0,X1),u1_struct_0(esk16_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_43]),c_0_44])).

cnf(c_0_83,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_84,negated_conjecture,
    ( r3_lattices(esk16_0,k15_lattice3(esk16_0,X1),k15_lattice3(esk16_0,X2))
    | r2_hidden(esk15_3(esk16_0,X1,X2),X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_58]),c_0_59]),c_0_43])]),c_0_44])).

cnf(c_0_85,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_38])).

cnf(c_0_86,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

fof(c_0_87,plain,(
    ! [X6,X7,X8,X9,X10] :
      ( ( ~ r1_tarski(X6,X7)
        | ~ r2_hidden(X8,X6)
        | r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_2(X9,X10),X9)
        | r1_tarski(X9,X10) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | r1_tarski(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_88,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,a_2_2_lattice3(X1,X3))
    | ~ r4_lattice3(X1,X2,X3)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(er,[status(thm)],[c_0_70])).

cnf(c_0_89,plain,
    ( v2_struct_0(X1)
    | r4_lattice3(X1,X2,X3)
    | X2 != k15_lattice3(X1,X3)
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(cn,[status(thm)],[c_0_71])).

cnf(c_0_90,plain,
    ( r2_hidden(X3,a_2_6_lattice3(X2,X5))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | X3 != X1
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r3_lattices(X2,X4,X1)
    | ~ r2_hidden(X4,X5)
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_91,negated_conjecture,
    ( r3_lattices(esk16_0,k15_lattice3(esk16_0,X1),k15_lattice3(esk16_0,X2))
    | ~ r3_lattice3(esk16_0,k15_lattice3(esk16_0,X1),a_2_2_lattice3(esk16_0,X2)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_92,negated_conjecture,
    ( r3_lattice3(esk16_0,k15_lattice3(esk16_0,X1),a_2_2_lattice3(esk16_0,X1)) ),
    inference(spm,[status(thm)],[c_0_75,c_0_74])).

cnf(c_0_93,plain,
    ( k15_lattice3(X1,k6_domain_1(u1_struct_0(X1),X2)) = X2
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_94,plain,
    ( k2_lattices(X1,X2,X3) = X3
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | X3 != k5_lattices(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v13_lattices(X1)
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_95,plain,
    ( k2_lattices(X1,X2,X3) = X2
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_96,negated_conjecture,
    ( v9_lattices(esk16_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_59]),c_0_43])]),c_0_44])).

cnf(c_0_97,negated_conjecture,
    ( v8_lattices(esk16_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_59]),c_0_43])]),c_0_44])).

cnf(c_0_98,negated_conjecture,
    ( r1_lattices(esk16_0,k16_lattice3(esk16_0,X1),k5_lattices(esk16_0))
    | ~ r3_lattice3(esk16_0,k16_lattice3(esk16_0,X1),X2)
    | ~ r2_hidden(k5_lattices(esk16_0),X2) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_99,negated_conjecture,
    ( r3_lattices(esk16_0,k15_lattice3(esk16_0,k3_xboole_0(X1,X2)),k15_lattice3(esk16_0,X3))
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_100,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_101,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_87])).

cnf(c_0_102,negated_conjecture,
    ( r2_hidden(k15_lattice3(esk16_0,X1),a_2_2_lattice3(esk16_0,X2))
    | ~ r4_lattice3(esk16_0,k15_lattice3(esk16_0,X1),X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_57]),c_0_58]),c_0_59]),c_0_43])]),c_0_44])).

cnf(c_0_103,plain,
    ( r4_lattice3(X1,k15_lattice3(X1,X2),X2)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_89]),c_0_42])).

cnf(c_0_104,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,a_2_6_lattice3(X1,X3))
    | ~ r3_lattices(X1,X4,X2)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ r2_hidden(X4,X3) ),
    inference(er,[status(thm)],[c_0_90])).

cnf(c_0_105,negated_conjecture,
    ( r3_lattices(esk16_0,k15_lattice3(esk16_0,X1),k15_lattice3(esk16_0,X1)) ),
    inference(spm,[status(thm)],[c_0_91,c_0_92])).

cnf(c_0_106,negated_conjecture,
    ( k15_lattice3(esk16_0,k6_domain_1(u1_struct_0(esk16_0),k16_lattice3(esk16_0,X1))) = k16_lattice3(esk16_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_82]),c_0_58]),c_0_59]),c_0_43])]),c_0_44])).

cnf(c_0_107,plain,
    ( k2_lattices(X1,X2,k5_lattices(X1)) = k5_lattices(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v13_lattices(X1)
    | ~ l1_lattices(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_94]),c_0_35])).

cnf(c_0_108,negated_conjecture,
    ( k2_lattices(esk16_0,X1,k5_lattices(esk16_0)) = X1
    | ~ r1_lattices(esk16_0,X1,k5_lattices(esk16_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk16_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_64]),c_0_96]),c_0_97]),c_0_43])]),c_0_44])).

cnf(c_0_109,negated_conjecture,
    ( r1_lattices(esk16_0,k16_lattice3(esk16_0,X1),k5_lattices(esk16_0))
    | ~ r2_hidden(k5_lattices(esk16_0),X1) ),
    inference(spm,[status(thm)],[c_0_98,c_0_75])).

cnf(c_0_110,negated_conjecture,
    ( r3_lattices(esk16_0,k15_lattice3(esk16_0,k1_xboole_0),k15_lattice3(esk16_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_100]),c_0_38])])).

cnf(c_0_111,negated_conjecture,
    ( k15_lattice3(esk16_0,k6_domain_1(u1_struct_0(esk16_0),k5_lattices(esk16_0))) = k5_lattices(esk16_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_64]),c_0_58]),c_0_59]),c_0_43])]),c_0_44])).

fof(c_0_112,plain,(
    ! [X95,X96] :
      ( ( k15_lattice3(X95,X96) = k15_lattice3(X95,a_2_5_lattice3(X95,X96))
        | v2_struct_0(X95)
        | ~ v10_lattices(X95)
        | ~ v4_lattice3(X95)
        | ~ l3_lattices(X95) )
      & ( k16_lattice3(X95,X96) = k16_lattice3(X95,a_2_6_lattice3(X95,X96))
        | v2_struct_0(X95)
        | ~ v10_lattices(X95)
        | ~ v4_lattice3(X95)
        | ~ l3_lattices(X95) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t47_lattice3])])])])])).

cnf(c_0_113,negated_conjecture,
    ( r2_hidden(k15_lattice3(esk16_0,X1),X2)
    | ~ r4_lattice3(esk16_0,k15_lattice3(esk16_0,X1),X3)
    | ~ r1_tarski(a_2_2_lattice3(esk16_0,X3),X2) ),
    inference(spm,[status(thm)],[c_0_101,c_0_102])).

cnf(c_0_114,negated_conjecture,
    ( r4_lattice3(esk16_0,k15_lattice3(esk16_0,X1),X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_58]),c_0_59]),c_0_43])]),c_0_44])).

cnf(c_0_115,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_116,negated_conjecture,
    ( r2_hidden(X1,a_2_6_lattice3(esk16_0,X2))
    | ~ r3_lattices(esk16_0,k16_lattice3(esk16_0,X3),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk16_0))
    | ~ r2_hidden(k16_lattice3(esk16_0,X3),X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_82]),c_0_58]),c_0_59]),c_0_43])]),c_0_44])).

cnf(c_0_117,negated_conjecture,
    ( r3_lattices(esk16_0,k16_lattice3(esk16_0,X1),k16_lattice3(esk16_0,X1)) ),
    inference(spm,[status(thm)],[c_0_105,c_0_106])).

cnf(c_0_118,negated_conjecture,
    ( k2_lattices(esk16_0,k16_lattice3(esk16_0,X1),k5_lattices(esk16_0)) = k5_lattices(esk16_0)
    | ~ v13_lattices(esk16_0)
    | ~ l1_lattices(esk16_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_82]),c_0_44])).

cnf(c_0_119,negated_conjecture,
    ( k2_lattices(esk16_0,k16_lattice3(esk16_0,X1),k5_lattices(esk16_0)) = k16_lattice3(esk16_0,X1)
    | ~ r2_hidden(k5_lattices(esk16_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_109]),c_0_82])])).

cnf(c_0_120,negated_conjecture,
    ( r2_hidden(X1,a_2_6_lattice3(esk16_0,X2))
    | ~ r3_lattices(esk16_0,k15_lattice3(esk16_0,X3),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk16_0))
    | ~ r2_hidden(k15_lattice3(esk16_0,X3),X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_57]),c_0_58]),c_0_59]),c_0_43])]),c_0_44])).

cnf(c_0_121,negated_conjecture,
    ( r3_lattices(esk16_0,k15_lattice3(esk16_0,k1_xboole_0),k5_lattices(esk16_0)) ),
    inference(spm,[status(thm)],[c_0_110,c_0_111])).

cnf(c_0_122,plain,
    ( k16_lattice3(X1,X2) = k16_lattice3(X1,a_2_6_lattice3(X1,X2))
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_112])).

cnf(c_0_123,negated_conjecture,
    ( r2_hidden(k15_lattice3(esk16_0,X1),X2)
    | ~ r1_tarski(a_2_2_lattice3(esk16_0,X1),X2) ),
    inference(spm,[status(thm)],[c_0_113,c_0_114])).

cnf(c_0_124,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_115])).

cnf(c_0_125,negated_conjecture,
    ( r2_hidden(k16_lattice3(esk16_0,X1),a_2_6_lattice3(esk16_0,X2))
    | ~ r2_hidden(k16_lattice3(esk16_0,X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_117]),c_0_82])])).

cnf(c_0_126,plain,
    ( k16_lattice3(X1,k6_domain_1(u1_struct_0(X1),X2)) = X2
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_127,negated_conjecture,
    ( k16_lattice3(esk16_0,X1) = k5_lattices(esk16_0)
    | ~ v13_lattices(esk16_0)
    | ~ l1_lattices(esk16_0)
    | ~ r2_hidden(k5_lattices(esk16_0),X1) ),
    inference(spm,[status(thm)],[c_0_118,c_0_119])).

cnf(c_0_128,negated_conjecture,
    ( r2_hidden(k5_lattices(esk16_0),a_2_6_lattice3(esk16_0,X1))
    | ~ r2_hidden(k15_lattice3(esk16_0,k1_xboole_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_121]),c_0_64])])).

cnf(c_0_129,negated_conjecture,
    ( k16_lattice3(esk16_0,a_2_6_lattice3(esk16_0,X1)) = k16_lattice3(esk16_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122,c_0_58]),c_0_59]),c_0_43])]),c_0_44])).

cnf(c_0_130,negated_conjecture,
    ( r2_hidden(k15_lattice3(esk16_0,X1),a_2_2_lattice3(esk16_0,X1)) ),
    inference(spm,[status(thm)],[c_0_123,c_0_124])).

cnf(c_0_131,negated_conjecture,
    ( k15_lattice3(esk16_0,k6_domain_1(u1_struct_0(esk16_0),k15_lattice3(esk16_0,X1))) = k15_lattice3(esk16_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_57]),c_0_58]),c_0_59]),c_0_43])]),c_0_44])).

cnf(c_0_132,negated_conjecture,
    ( v2_struct_0(esk16_0)
    | ~ v10_lattices(esk16_0)
    | ~ v13_lattices(esk16_0)
    | ~ l3_lattices(esk16_0)
    | k5_lattices(esk16_0) != k15_lattice3(esk16_0,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_133,negated_conjecture,
    ( r2_hidden(k16_lattice3(esk16_0,X1),X2)
    | ~ r2_hidden(k16_lattice3(esk16_0,X1),X3)
    | ~ r1_tarski(a_2_6_lattice3(esk16_0,X3),X2) ),
    inference(spm,[status(thm)],[c_0_101,c_0_125])).

cnf(c_0_134,negated_conjecture,
    ( k16_lattice3(esk16_0,k6_domain_1(u1_struct_0(esk16_0),k15_lattice3(esk16_0,X1))) = k15_lattice3(esk16_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126,c_0_57]),c_0_58]),c_0_59]),c_0_43])]),c_0_44])).

cnf(c_0_135,negated_conjecture,
    ( r2_hidden(k15_lattice3(esk16_0,X1),a_2_6_lattice3(esk16_0,X2))
    | ~ r2_hidden(k15_lattice3(esk16_0,k1_xboole_0),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_110]),c_0_57])])).

fof(c_0_136,plain,(
    ! [X35,X37,X38] :
      ( ( m1_subset_1(esk3_1(X35),u1_struct_0(X35))
        | ~ v13_lattices(X35)
        | v2_struct_0(X35)
        | ~ l1_lattices(X35) )
      & ( k2_lattices(X35,esk3_1(X35),X37) = esk3_1(X35)
        | ~ m1_subset_1(X37,u1_struct_0(X35))
        | ~ v13_lattices(X35)
        | v2_struct_0(X35)
        | ~ l1_lattices(X35) )
      & ( k2_lattices(X35,X37,esk3_1(X35)) = esk3_1(X35)
        | ~ m1_subset_1(X37,u1_struct_0(X35))
        | ~ v13_lattices(X35)
        | v2_struct_0(X35)
        | ~ l1_lattices(X35) )
      & ( m1_subset_1(esk4_2(X35,X38),u1_struct_0(X35))
        | ~ m1_subset_1(X38,u1_struct_0(X35))
        | v13_lattices(X35)
        | v2_struct_0(X35)
        | ~ l1_lattices(X35) )
      & ( k2_lattices(X35,X38,esk4_2(X35,X38)) != X38
        | k2_lattices(X35,esk4_2(X35,X38),X38) != X38
        | ~ m1_subset_1(X38,u1_struct_0(X35))
        | v13_lattices(X35)
        | v2_struct_0(X35)
        | ~ l1_lattices(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d13_lattices])])])])])])).

cnf(c_0_137,plain,
    ( m1_subset_1(esk12_3(X1,X2,X3),u1_struct_0(X2))
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_6_lattice3(X2,X3))
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_138,negated_conjecture,
    ( k16_lattice3(esk16_0,X1) = k5_lattices(esk16_0)
    | ~ v13_lattices(esk16_0)
    | ~ l1_lattices(esk16_0)
    | ~ r2_hidden(k15_lattice3(esk16_0,k1_xboole_0),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127,c_0_128]),c_0_129])).

cnf(c_0_139,negated_conjecture,
    ( r2_hidden(k15_lattice3(esk16_0,X1),a_2_2_lattice3(esk16_0,k6_domain_1(u1_struct_0(esk16_0),k15_lattice3(esk16_0,X1)))) ),
    inference(spm,[status(thm)],[c_0_130,c_0_131])).

cnf(c_0_140,negated_conjecture,
    ( k5_lattices(esk16_0) != k15_lattice3(esk16_0,k1_xboole_0)
    | ~ v13_lattices(esk16_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_132,c_0_43]),c_0_59])]),c_0_44])).

cnf(c_0_141,negated_conjecture,
    ( r2_hidden(k15_lattice3(esk16_0,X1),X2)
    | ~ r2_hidden(k15_lattice3(esk16_0,X1),X3)
    | ~ r1_tarski(a_2_6_lattice3(esk16_0,X3),X2) ),
    inference(spm,[status(thm)],[c_0_133,c_0_134])).

cnf(c_0_142,negated_conjecture,
    ( r2_hidden(k15_lattice3(esk16_0,X1),X2)
    | ~ r2_hidden(k15_lattice3(esk16_0,k1_xboole_0),X3)
    | ~ r1_tarski(a_2_6_lattice3(esk16_0,X3),X2) ),
    inference(spm,[status(thm)],[c_0_101,c_0_135])).

cnf(c_0_143,plain,
    ( m1_subset_1(esk4_2(X1,X2),u1_struct_0(X1))
    | v13_lattices(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_136])).

cnf(c_0_144,negated_conjecture,
    ( m1_subset_1(esk12_3(k15_lattice3(esk16_0,X1),esk16_0,X2),u1_struct_0(esk16_0))
    | ~ r2_hidden(k15_lattice3(esk16_0,k1_xboole_0),X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137,c_0_135]),c_0_58]),c_0_59]),c_0_43])]),c_0_44])).

cnf(c_0_145,negated_conjecture,
    ( ~ v13_lattices(esk16_0)
    | ~ l1_lattices(esk16_0) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_139]),c_0_74]),c_0_131]),c_0_140])).

cnf(c_0_146,plain,
    ( X1 = esk12_3(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_6_lattice3(X2,X3))
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_147,negated_conjecture,
    ( r2_hidden(k15_lattice3(esk16_0,X1),X2)
    | ~ r1_tarski(a_2_6_lattice3(esk16_0,a_2_2_lattice3(esk16_0,X1)),X2) ),
    inference(spm,[status(thm)],[c_0_141,c_0_130])).

cnf(c_0_148,negated_conjecture,
    ( r2_hidden(k15_lattice3(esk16_0,X1),X2)
    | ~ r1_tarski(a_2_6_lattice3(esk16_0,a_2_2_lattice3(esk16_0,k1_xboole_0)),X2) ),
    inference(spm,[status(thm)],[c_0_142,c_0_130])).

cnf(c_0_149,negated_conjecture,
    ( m1_subset_1(esk4_2(esk16_0,esk12_3(k15_lattice3(esk16_0,X1),esk16_0,X2)),u1_struct_0(esk16_0))
    | ~ l1_lattices(esk16_0)
    | ~ r2_hidden(k15_lattice3(esk16_0,k1_xboole_0),X2) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_143,c_0_144]),c_0_44]),c_0_145])).

cnf(c_0_150,negated_conjecture,
    ( esk12_3(k15_lattice3(esk16_0,X1),esk16_0,X2) = k15_lattice3(esk16_0,X1)
    | ~ r2_hidden(k15_lattice3(esk16_0,k1_xboole_0),X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_146,c_0_135]),c_0_58]),c_0_59]),c_0_43])]),c_0_44])).

cnf(c_0_151,negated_conjecture,
    ( r2_hidden(k15_lattice3(esk16_0,X1),a_2_6_lattice3(esk16_0,a_2_2_lattice3(esk16_0,X1))) ),
    inference(spm,[status(thm)],[c_0_147,c_0_124])).

cnf(c_0_152,negated_conjecture,
    ( r1_lattices(esk16_0,X1,k15_lattice3(esk16_0,X2))
    | ~ r3_lattice3(esk16_0,X1,X3)
    | ~ m1_subset_1(X1,u1_struct_0(esk16_0))
    | ~ r2_hidden(k15_lattice3(esk16_0,X2),X3) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_57]),c_0_43])]),c_0_44])).

cnf(c_0_153,negated_conjecture,
    ( r2_hidden(k15_lattice3(esk16_0,X1),a_2_6_lattice3(esk16_0,a_2_2_lattice3(esk16_0,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_148,c_0_124])).

cnf(c_0_154,negated_conjecture,
    ( m1_subset_1(esk4_2(esk16_0,k15_lattice3(esk16_0,X1)),u1_struct_0(esk16_0))
    | ~ l1_lattices(esk16_0)
    | ~ r2_hidden(k15_lattice3(esk16_0,k1_xboole_0),X2) ),
    inference(spm,[status(thm)],[c_0_149,c_0_150])).

cnf(c_0_155,negated_conjecture,
    ( r2_hidden(k15_lattice3(esk16_0,X1),X2)
    | ~ r1_tarski(a_2_6_lattice3(esk16_0,a_2_6_lattice3(esk16_0,a_2_2_lattice3(esk16_0,X1))),X2) ),
    inference(spm,[status(thm)],[c_0_141,c_0_151])).

cnf(c_0_156,negated_conjecture,
    ( r1_lattices(esk16_0,X1,k15_lattice3(esk16_0,X2))
    | ~ r3_lattice3(esk16_0,X1,a_2_6_lattice3(esk16_0,a_2_2_lattice3(esk16_0,k1_xboole_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk16_0)) ),
    inference(spm,[status(thm)],[c_0_152,c_0_153])).

cnf(c_0_157,negated_conjecture,
    ( m1_subset_1(esk4_2(esk16_0,k15_lattice3(esk16_0,X1)),u1_struct_0(esk16_0))
    | ~ r2_hidden(k15_lattice3(esk16_0,k1_xboole_0),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_154,c_0_36]),c_0_43])])).

cnf(c_0_158,negated_conjecture,
    ( r2_hidden(k15_lattice3(esk16_0,X1),a_2_6_lattice3(esk16_0,a_2_6_lattice3(esk16_0,a_2_2_lattice3(esk16_0,X1)))) ),
    inference(spm,[status(thm)],[c_0_155,c_0_124])).

cnf(c_0_159,negated_conjecture,
    ( k2_lattices(esk16_0,X1,k15_lattice3(esk16_0,X2)) = X1
    | ~ r1_lattices(esk16_0,X1,k15_lattice3(esk16_0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(esk16_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_57]),c_0_96]),c_0_97]),c_0_43])]),c_0_44])).

cnf(c_0_160,negated_conjecture,
    ( r1_lattices(esk16_0,k15_lattice3(esk16_0,k1_xboole_0),k15_lattice3(esk16_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_156,c_0_75]),c_0_129]),c_0_74]),c_0_129]),c_0_74]),c_0_57])])).

cnf(c_0_161,negated_conjecture,
    ( m1_subset_1(esk4_2(esk16_0,k15_lattice3(esk16_0,X1)),u1_struct_0(esk16_0)) ),
    inference(spm,[status(thm)],[c_0_157,c_0_158])).

cnf(c_0_162,negated_conjecture,
    ( k2_lattices(esk16_0,k15_lattice3(esk16_0,k1_xboole_0),k15_lattice3(esk16_0,X1)) = k15_lattice3(esk16_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_159,c_0_160]),c_0_57])])).

cnf(c_0_163,negated_conjecture,
    ( k15_lattice3(esk16_0,k6_domain_1(u1_struct_0(esk16_0),esk4_2(esk16_0,k15_lattice3(esk16_0,X1)))) = esk4_2(esk16_0,k15_lattice3(esk16_0,X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_161]),c_0_58]),c_0_59]),c_0_43])]),c_0_44])).

fof(c_0_164,plain,(
    ! [X51,X52,X53] :
      ( ( ~ v6_lattices(X51)
        | ~ m1_subset_1(X52,u1_struct_0(X51))
        | ~ m1_subset_1(X53,u1_struct_0(X51))
        | k2_lattices(X51,X52,X53) = k2_lattices(X51,X53,X52)
        | v2_struct_0(X51)
        | ~ l1_lattices(X51) )
      & ( m1_subset_1(esk7_1(X51),u1_struct_0(X51))
        | v6_lattices(X51)
        | v2_struct_0(X51)
        | ~ l1_lattices(X51) )
      & ( m1_subset_1(esk8_1(X51),u1_struct_0(X51))
        | v6_lattices(X51)
        | v2_struct_0(X51)
        | ~ l1_lattices(X51) )
      & ( k2_lattices(X51,esk7_1(X51),esk8_1(X51)) != k2_lattices(X51,esk8_1(X51),esk7_1(X51))
        | v6_lattices(X51)
        | v2_struct_0(X51)
        | ~ l1_lattices(X51) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d6_lattices])])])])])])).

cnf(c_0_165,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_166,plain,
    ( v13_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,esk4_2(X1,X2)) != X2
    | k2_lattices(X1,esk4_2(X1,X2),X2) != X2
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_136])).

cnf(c_0_167,negated_conjecture,
    ( k2_lattices(esk16_0,k15_lattice3(esk16_0,k1_xboole_0),esk4_2(esk16_0,k15_lattice3(esk16_0,X1))) = k15_lattice3(esk16_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_162,c_0_163])).

cnf(c_0_168,plain,
    ( k2_lattices(X1,X2,X3) = k2_lattices(X1,X3,X2)
    | v2_struct_0(X1)
    | ~ v6_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_164])).

cnf(c_0_169,negated_conjecture,
    ( v6_lattices(esk16_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_165,c_0_59]),c_0_43])]),c_0_44])).

cnf(c_0_170,negated_conjecture,
    ( k2_lattices(esk16_0,esk4_2(esk16_0,k15_lattice3(esk16_0,k1_xboole_0)),k15_lattice3(esk16_0,k1_xboole_0)) != k15_lattice3(esk16_0,k1_xboole_0)
    | ~ l1_lattices(esk16_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_166,c_0_167]),c_0_57])]),c_0_44]),c_0_145])).

cnf(c_0_171,negated_conjecture,
    ( k2_lattices(esk16_0,X1,k15_lattice3(esk16_0,X2)) = k2_lattices(esk16_0,k15_lattice3(esk16_0,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk16_0))
    | ~ l1_lattices(esk16_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_168,c_0_57]),c_0_169])]),c_0_44])).

cnf(c_0_172,negated_conjecture,
    ( ~ l1_lattices(esk16_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_170,c_0_171]),c_0_167]),c_0_161])])).

cnf(c_0_173,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_172,c_0_36]),c_0_43])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:11:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 1.28/1.52  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 1.28/1.52  # and selection function SelectComplexExceptUniqMaxHorn.
% 1.28/1.52  #
% 1.28/1.52  # Preprocessing time       : 0.029 s
% 1.28/1.52  # Presaturation interreduction done
% 1.28/1.52  
% 1.28/1.52  # Proof found!
% 1.28/1.52  # SZS status Theorem
% 1.28/1.52  # SZS output start CNFRefutation
% 1.28/1.52  fof(t50_lattice3, conjecture, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>((((~(v2_struct_0(X1))&v10_lattices(X1))&v13_lattices(X1))&l3_lattices(X1))&k5_lattices(X1)=k15_lattice3(X1,k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_lattice3)).
% 1.28/1.52  fof(dt_k5_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>m1_subset_1(k5_lattices(X1),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_lattices)).
% 1.28/1.52  fof(dt_l3_lattices, axiom, ![X1]:(l3_lattices(X1)=>(l1_lattices(X1)&l2_lattices(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l3_lattices)).
% 1.28/1.52  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 1.28/1.52  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.28/1.52  fof(t34_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(X2=k16_lattice3(X1,X3)<=>(r3_lattice3(X1,X2,X3)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r3_lattice3(X1,X4,X3)=>r3_lattices(X1,X4,X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_lattice3)).
% 1.28/1.52  fof(dt_k16_lattice3, axiom, ![X1, X2]:((~(v2_struct_0(X1))&l3_lattices(X1))=>m1_subset_1(k16_lattice3(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k16_lattice3)).
% 1.28/1.52  fof(dt_k15_lattice3, axiom, ![X1, X2]:((~(v2_struct_0(X1))&l3_lattices(X1))=>m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k15_lattice3)).
% 1.28/1.52  fof(t108_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(k3_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_xboole_1)).
% 1.28/1.52  fof(t37_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:k15_lattice3(X1,X2)=k16_lattice3(X1,a_2_2_lattice3(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_lattice3)).
% 1.28/1.52  fof(d16_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(r3_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X3)=>r1_lattices(X1,X2,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_lattice3)).
% 1.28/1.52  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 1.28/1.52  fof(t48_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2, X3]:(![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>~((r2_hidden(X4,X2)&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>~((r3_lattices(X1,X4,X5)&r2_hidden(X5,X3)))))))=>r3_lattices(X1,k15_lattice3(X1,X2),k15_lattice3(X1,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_lattice3)).
% 1.28/1.52  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.28/1.52  fof(fraenkel_a_2_2_lattice3, axiom, ![X1, X2, X3]:((((~(v2_struct_0(X2))&v10_lattices(X2))&v4_lattice3(X2))&l3_lattices(X2))=>(r2_hidden(X1,a_2_2_lattice3(X2,X3))<=>?[X4]:((m1_subset_1(X4,u1_struct_0(X2))&X1=X4)&r4_lattice3(X2,X4,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_2_lattice3)).
% 1.28/1.52  fof(d21_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(X3=k15_lattice3(X1,X2)<=>(r4_lattice3(X1,X3,X2)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r4_lattice3(X1,X4,X2)=>r1_lattices(X1,X3,X4)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d21_lattice3)).
% 1.28/1.52  fof(cc1_lattices, axiom, ![X1]:(l3_lattices(X1)=>((~(v2_struct_0(X1))&v10_lattices(X1))=>((((((~(v2_struct_0(X1))&v4_lattices(X1))&v5_lattices(X1))&v6_lattices(X1))&v7_lattices(X1))&v8_lattices(X1))&v9_lattices(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattices)).
% 1.28/1.52  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 1.28/1.52  fof(fraenkel_a_2_6_lattice3, axiom, ![X1, X2, X3]:((((~(v2_struct_0(X2))&v10_lattices(X2))&v4_lattice3(X2))&l3_lattices(X2))=>(r2_hidden(X1,a_2_6_lattice3(X2,X3))<=>?[X4]:((m1_subset_1(X4,u1_struct_0(X2))&X1=X4)&?[X5]:((m1_subset_1(X5,u1_struct_0(X2))&r3_lattices(X2,X5,X4))&r2_hidden(X5,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_6_lattice3)).
% 1.28/1.52  fof(t43_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(k15_lattice3(X1,k6_domain_1(u1_struct_0(X1),X2))=X2&k16_lattice3(X1,k6_domain_1(u1_struct_0(X1),X2))=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_lattice3)).
% 1.28/1.52  fof(d16_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>(v13_lattices(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(X2=k5_lattices(X1)<=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(k2_lattices(X1,X2,X3)=X2&k2_lattices(X1,X3,X2)=X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_lattices)).
% 1.28/1.52  fof(t21_lattices, axiom, ![X1]:((((~(v2_struct_0(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_lattices(X1,X2,X3)<=>k2_lattices(X1,X2,X3)=X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_lattices)).
% 1.28/1.52  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.28/1.52  fof(t47_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(k15_lattice3(X1,X2)=k15_lattice3(X1,a_2_5_lattice3(X1,X2))&k16_lattice3(X1,X2)=k16_lattice3(X1,a_2_6_lattice3(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_lattice3)).
% 1.28/1.52  fof(d13_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>(v13_lattices(X1)<=>?[X2]:(m1_subset_1(X2,u1_struct_0(X1))&![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(k2_lattices(X1,X2,X3)=X2&k2_lattices(X1,X3,X2)=X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_lattices)).
% 1.28/1.52  fof(d6_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>(v6_lattices(X1)<=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>k2_lattices(X1,X2,X3)=k2_lattices(X1,X3,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_lattices)).
% 1.28/1.52  fof(c_0_26, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>((((~(v2_struct_0(X1))&v10_lattices(X1))&v13_lattices(X1))&l3_lattices(X1))&k5_lattices(X1)=k15_lattice3(X1,k1_xboole_0)))), inference(assume_negation,[status(cth)],[t50_lattice3])).
% 1.28/1.52  fof(c_0_27, plain, ![X30]:(v2_struct_0(X30)|~l1_lattices(X30)|m1_subset_1(k5_lattices(X30),u1_struct_0(X30))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_lattices])])])).
% 1.28/1.52  fof(c_0_28, plain, ![X31]:((l1_lattices(X31)|~l3_lattices(X31))&(l2_lattices(X31)|~l3_lattices(X31))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).
% 1.28/1.52  fof(c_0_29, plain, ![X19, X20, X21]:(~r1_tarski(X19,X20)|~r1_tarski(X20,X21)|r1_tarski(X19,X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 1.28/1.52  fof(c_0_30, plain, ![X22]:r1_tarski(k1_xboole_0,X22), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 1.28/1.52  fof(c_0_31, plain, ![X82, X83, X84, X85, X86]:(((r3_lattice3(X82,X83,X84)|X83!=k16_lattice3(X82,X84)|~m1_subset_1(X83,u1_struct_0(X82))|(v2_struct_0(X82)|~v10_lattices(X82)|~v4_lattice3(X82)|~l3_lattices(X82)))&(~m1_subset_1(X85,u1_struct_0(X82))|(~r3_lattice3(X82,X85,X84)|r3_lattices(X82,X85,X83))|X83!=k16_lattice3(X82,X84)|~m1_subset_1(X83,u1_struct_0(X82))|(v2_struct_0(X82)|~v10_lattices(X82)|~v4_lattice3(X82)|~l3_lattices(X82))))&((m1_subset_1(esk14_3(X82,X83,X86),u1_struct_0(X82))|~r3_lattice3(X82,X83,X86)|X83=k16_lattice3(X82,X86)|~m1_subset_1(X83,u1_struct_0(X82))|(v2_struct_0(X82)|~v10_lattices(X82)|~v4_lattice3(X82)|~l3_lattices(X82)))&((r3_lattice3(X82,esk14_3(X82,X83,X86),X86)|~r3_lattice3(X82,X83,X86)|X83=k16_lattice3(X82,X86)|~m1_subset_1(X83,u1_struct_0(X82))|(v2_struct_0(X82)|~v10_lattices(X82)|~v4_lattice3(X82)|~l3_lattices(X82)))&(~r3_lattices(X82,esk14_3(X82,X83,X86),X83)|~r3_lattice3(X82,X83,X86)|X83=k16_lattice3(X82,X86)|~m1_subset_1(X83,u1_struct_0(X82))|(v2_struct_0(X82)|~v10_lattices(X82)|~v4_lattice3(X82)|~l3_lattices(X82)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_lattice3])])])])])])])).
% 1.28/1.52  fof(c_0_32, plain, ![X58, X59]:(v2_struct_0(X58)|~l3_lattices(X58)|m1_subset_1(k16_lattice3(X58,X59),u1_struct_0(X58))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k16_lattice3])])])).
% 1.28/1.52  fof(c_0_33, plain, ![X56, X57]:(v2_struct_0(X56)|~l3_lattices(X56)|m1_subset_1(k15_lattice3(X56,X57),u1_struct_0(X56))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k15_lattice3])])])).
% 1.28/1.52  fof(c_0_34, negated_conjecture, ((((~v2_struct_0(esk16_0)&v10_lattices(esk16_0))&v4_lattice3(esk16_0))&l3_lattices(esk16_0))&(v2_struct_0(esk16_0)|~v10_lattices(esk16_0)|~v13_lattices(esk16_0)|~l3_lattices(esk16_0)|k5_lattices(esk16_0)!=k15_lattice3(esk16_0,k1_xboole_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_26])])])])).
% 1.28/1.52  cnf(c_0_35, plain, (v2_struct_0(X1)|m1_subset_1(k5_lattices(X1),u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 1.28/1.52  cnf(c_0_36, plain, (l1_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 1.28/1.52  cnf(c_0_37, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 1.28/1.52  cnf(c_0_38, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 1.28/1.52  fof(c_0_39, plain, ![X14, X15, X16]:(~r1_tarski(X14,X15)|r1_tarski(k3_xboole_0(X14,X16),X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t108_xboole_1])])).
% 1.28/1.52  cnf(c_0_40, plain, (r3_lattices(X2,X1,X4)|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~r3_lattice3(X2,X1,X3)|X4!=k16_lattice3(X2,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 1.28/1.52  cnf(c_0_41, plain, (v2_struct_0(X1)|m1_subset_1(k16_lattice3(X1,X2),u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 1.28/1.52  cnf(c_0_42, plain, (v2_struct_0(X1)|m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 1.28/1.52  cnf(c_0_43, negated_conjecture, (l3_lattices(esk16_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 1.28/1.52  cnf(c_0_44, negated_conjecture, (~v2_struct_0(esk16_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 1.28/1.52  fof(c_0_45, plain, ![X88, X89]:(v2_struct_0(X88)|~v10_lattices(X88)|~v4_lattice3(X88)|~l3_lattices(X88)|k15_lattice3(X88,X89)=k16_lattice3(X88,a_2_2_lattice3(X88,X89))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t37_lattice3])])])])).
% 1.28/1.52  cnf(c_0_46, plain, (r3_lattice3(X1,X2,X3)|v2_struct_0(X1)|X2!=k16_lattice3(X1,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 1.28/1.52  fof(c_0_47, plain, ![X40, X41, X42, X43, X44]:((~r3_lattice3(X40,X41,X42)|(~m1_subset_1(X43,u1_struct_0(X40))|(~r2_hidden(X43,X42)|r1_lattices(X40,X41,X43)))|~m1_subset_1(X41,u1_struct_0(X40))|(v2_struct_0(X40)|~l3_lattices(X40)))&((m1_subset_1(esk5_3(X40,X41,X44),u1_struct_0(X40))|r3_lattice3(X40,X41,X44)|~m1_subset_1(X41,u1_struct_0(X40))|(v2_struct_0(X40)|~l3_lattices(X40)))&((r2_hidden(esk5_3(X40,X41,X44),X44)|r3_lattice3(X40,X41,X44)|~m1_subset_1(X41,u1_struct_0(X40))|(v2_struct_0(X40)|~l3_lattices(X40)))&(~r1_lattices(X40,X41,esk5_3(X40,X41,X44))|r3_lattice3(X40,X41,X44)|~m1_subset_1(X41,u1_struct_0(X40))|(v2_struct_0(X40)|~l3_lattices(X40)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattice3])])])])])])])).
% 1.28/1.52  cnf(c_0_48, plain, (m1_subset_1(k5_lattices(X1),u1_struct_0(X1))|v2_struct_0(X1)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 1.28/1.52  fof(c_0_49, plain, ![X23, X24]:(~r2_hidden(X23,X24)|~r1_tarski(X24,X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 1.28/1.52  cnf(c_0_50, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 1.28/1.52  cnf(c_0_51, plain, (r1_tarski(k3_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 1.28/1.52  fof(c_0_52, plain, ![X97, X98, X99, X101]:((m1_subset_1(esk15_3(X97,X98,X99),u1_struct_0(X97))|r3_lattices(X97,k15_lattice3(X97,X98),k15_lattice3(X97,X99))|(v2_struct_0(X97)|~v10_lattices(X97)|~v4_lattice3(X97)|~l3_lattices(X97)))&((r2_hidden(esk15_3(X97,X98,X99),X98)|r3_lattices(X97,k15_lattice3(X97,X98),k15_lattice3(X97,X99))|(v2_struct_0(X97)|~v10_lattices(X97)|~v4_lattice3(X97)|~l3_lattices(X97)))&(~m1_subset_1(X101,u1_struct_0(X97))|(~r3_lattices(X97,esk15_3(X97,X98,X99),X101)|~r2_hidden(X101,X99))|r3_lattices(X97,k15_lattice3(X97,X98),k15_lattice3(X97,X99))|(v2_struct_0(X97)|~v10_lattices(X97)|~v4_lattice3(X97)|~l3_lattices(X97))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t48_lattice3])])])])])])).
% 1.28/1.52  fof(c_0_53, plain, ![X12, X13]:(((r1_tarski(X12,X13)|X12!=X13)&(r1_tarski(X13,X12)|X12!=X13))&(~r1_tarski(X12,X13)|~r1_tarski(X13,X12)|X12=X13)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 1.28/1.52  fof(c_0_54, plain, ![X60, X61, X62, X64, X65]:((((m1_subset_1(esk9_3(X60,X61,X62),u1_struct_0(X61))|~r2_hidden(X60,a_2_2_lattice3(X61,X62))|(v2_struct_0(X61)|~v10_lattices(X61)|~v4_lattice3(X61)|~l3_lattices(X61)))&(X60=esk9_3(X60,X61,X62)|~r2_hidden(X60,a_2_2_lattice3(X61,X62))|(v2_struct_0(X61)|~v10_lattices(X61)|~v4_lattice3(X61)|~l3_lattices(X61))))&(r4_lattice3(X61,esk9_3(X60,X61,X62),X62)|~r2_hidden(X60,a_2_2_lattice3(X61,X62))|(v2_struct_0(X61)|~v10_lattices(X61)|~v4_lattice3(X61)|~l3_lattices(X61))))&(~m1_subset_1(X65,u1_struct_0(X61))|X60!=X65|~r4_lattice3(X61,X65,X64)|r2_hidden(X60,a_2_2_lattice3(X61,X64))|(v2_struct_0(X61)|~v10_lattices(X61)|~v4_lattice3(X61)|~l3_lattices(X61)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_2_lattice3])])])])])])])).
% 1.28/1.52  fof(c_0_55, plain, ![X46, X47, X48, X49]:(((r4_lattice3(X46,X48,X47)|X48!=k15_lattice3(X46,X47)|~m1_subset_1(X48,u1_struct_0(X46))|(v2_struct_0(X46)|~v10_lattices(X46)|~v4_lattice3(X46)|~l3_lattices(X46))|(v2_struct_0(X46)|~l3_lattices(X46)))&(~m1_subset_1(X49,u1_struct_0(X46))|(~r4_lattice3(X46,X49,X47)|r1_lattices(X46,X48,X49))|X48!=k15_lattice3(X46,X47)|~m1_subset_1(X48,u1_struct_0(X46))|(v2_struct_0(X46)|~v10_lattices(X46)|~v4_lattice3(X46)|~l3_lattices(X46))|(v2_struct_0(X46)|~l3_lattices(X46))))&((m1_subset_1(esk6_3(X46,X47,X48),u1_struct_0(X46))|~r4_lattice3(X46,X48,X47)|X48=k15_lattice3(X46,X47)|~m1_subset_1(X48,u1_struct_0(X46))|(v2_struct_0(X46)|~v10_lattices(X46)|~v4_lattice3(X46)|~l3_lattices(X46))|(v2_struct_0(X46)|~l3_lattices(X46)))&((r4_lattice3(X46,esk6_3(X46,X47,X48),X47)|~r4_lattice3(X46,X48,X47)|X48=k15_lattice3(X46,X47)|~m1_subset_1(X48,u1_struct_0(X46))|(v2_struct_0(X46)|~v10_lattices(X46)|~v4_lattice3(X46)|~l3_lattices(X46))|(v2_struct_0(X46)|~l3_lattices(X46)))&(~r1_lattices(X46,X48,esk6_3(X46,X47,X48))|~r4_lattice3(X46,X48,X47)|X48=k15_lattice3(X46,X47)|~m1_subset_1(X48,u1_struct_0(X46))|(v2_struct_0(X46)|~v10_lattices(X46)|~v4_lattice3(X46)|~l3_lattices(X46))|(v2_struct_0(X46)|~l3_lattices(X46)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d21_lattice3])])])])])])).
% 1.28/1.52  cnf(c_0_56, plain, (r3_lattices(X1,X2,k16_lattice3(X1,X3))|v2_struct_0(X1)|~v4_lattice3(X1)|~r3_lattice3(X1,X2,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_40]), c_0_41])).
% 1.28/1.52  cnf(c_0_57, negated_conjecture, (m1_subset_1(k15_lattice3(esk16_0,X1),u1_struct_0(esk16_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44])).
% 1.28/1.52  cnf(c_0_58, negated_conjecture, (v4_lattice3(esk16_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 1.28/1.52  cnf(c_0_59, negated_conjecture, (v10_lattices(esk16_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 1.28/1.52  cnf(c_0_60, plain, (v2_struct_0(X1)|k15_lattice3(X1,X2)=k16_lattice3(X1,a_2_2_lattice3(X1,X2))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 1.28/1.52  cnf(c_0_61, plain, (r3_lattice3(X1,k16_lattice3(X1,X2),X2)|v2_struct_0(X1)|~v4_lattice3(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_46]), c_0_41])).
% 1.28/1.52  fof(c_0_62, plain, ![X25]:(((((((~v2_struct_0(X25)|(v2_struct_0(X25)|~v10_lattices(X25))|~l3_lattices(X25))&(v4_lattices(X25)|(v2_struct_0(X25)|~v10_lattices(X25))|~l3_lattices(X25)))&(v5_lattices(X25)|(v2_struct_0(X25)|~v10_lattices(X25))|~l3_lattices(X25)))&(v6_lattices(X25)|(v2_struct_0(X25)|~v10_lattices(X25))|~l3_lattices(X25)))&(v7_lattices(X25)|(v2_struct_0(X25)|~v10_lattices(X25))|~l3_lattices(X25)))&(v8_lattices(X25)|(v2_struct_0(X25)|~v10_lattices(X25))|~l3_lattices(X25)))&(v9_lattices(X25)|(v2_struct_0(X25)|~v10_lattices(X25))|~l3_lattices(X25))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).
% 1.28/1.52  cnf(c_0_63, plain, (r1_lattices(X1,X2,X4)|v2_struct_0(X1)|~r3_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X4,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 1.28/1.52  cnf(c_0_64, negated_conjecture, (m1_subset_1(k5_lattices(esk16_0),u1_struct_0(esk16_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_43]), c_0_44])).
% 1.28/1.52  cnf(c_0_65, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 1.28/1.52  cnf(c_0_66, plain, (r1_tarski(k3_xboole_0(X1,X2),X3)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 1.28/1.52  cnf(c_0_67, plain, (r2_hidden(esk15_3(X1,X2,X3),X2)|r3_lattices(X1,k15_lattice3(X1,X2),k15_lattice3(X1,X3))|v2_struct_0(X1)|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 1.28/1.52  cnf(c_0_68, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 1.28/1.52  fof(c_0_69, plain, ![X17, X18]:r1_tarski(k3_xboole_0(X17,X18),X17), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 1.28/1.52  cnf(c_0_70, plain, (r2_hidden(X3,a_2_2_lattice3(X2,X4))|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|X3!=X1|~r4_lattice3(X2,X1,X4)|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 1.28/1.52  cnf(c_0_71, plain, (r4_lattice3(X1,X2,X3)|v2_struct_0(X1)|v2_struct_0(X1)|X2!=k15_lattice3(X1,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 1.28/1.52  fof(c_0_72, plain, ![X74, X75, X76, X79, X80, X81]:((((m1_subset_1(esk12_3(X74,X75,X76),u1_struct_0(X75))|~r2_hidden(X74,a_2_6_lattice3(X75,X76))|(v2_struct_0(X75)|~v10_lattices(X75)|~v4_lattice3(X75)|~l3_lattices(X75)))&(X74=esk12_3(X74,X75,X76)|~r2_hidden(X74,a_2_6_lattice3(X75,X76))|(v2_struct_0(X75)|~v10_lattices(X75)|~v4_lattice3(X75)|~l3_lattices(X75))))&(((m1_subset_1(esk13_3(X74,X75,X76),u1_struct_0(X75))|~r2_hidden(X74,a_2_6_lattice3(X75,X76))|(v2_struct_0(X75)|~v10_lattices(X75)|~v4_lattice3(X75)|~l3_lattices(X75)))&(r3_lattices(X75,esk13_3(X74,X75,X76),esk12_3(X74,X75,X76))|~r2_hidden(X74,a_2_6_lattice3(X75,X76))|(v2_struct_0(X75)|~v10_lattices(X75)|~v4_lattice3(X75)|~l3_lattices(X75))))&(r2_hidden(esk13_3(X74,X75,X76),X76)|~r2_hidden(X74,a_2_6_lattice3(X75,X76))|(v2_struct_0(X75)|~v10_lattices(X75)|~v4_lattice3(X75)|~l3_lattices(X75)))))&(~m1_subset_1(X80,u1_struct_0(X75))|X74!=X80|(~m1_subset_1(X81,u1_struct_0(X75))|~r3_lattices(X75,X81,X80)|~r2_hidden(X81,X79))|r2_hidden(X74,a_2_6_lattice3(X75,X79))|(v2_struct_0(X75)|~v10_lattices(X75)|~v4_lattice3(X75)|~l3_lattices(X75)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_6_lattice3])])])])])])])).
% 1.28/1.52  cnf(c_0_73, negated_conjecture, (r3_lattices(esk16_0,k15_lattice3(esk16_0,X1),k16_lattice3(esk16_0,X2))|~r3_lattice3(esk16_0,k15_lattice3(esk16_0,X1),X2)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_58]), c_0_59]), c_0_43])]), c_0_44])).
% 1.28/1.52  cnf(c_0_74, negated_conjecture, (k16_lattice3(esk16_0,a_2_2_lattice3(esk16_0,X1))=k15_lattice3(esk16_0,X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_58]), c_0_59]), c_0_43])]), c_0_44])).
% 1.28/1.52  cnf(c_0_75, negated_conjecture, (r3_lattice3(esk16_0,k16_lattice3(esk16_0,X1),X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_58]), c_0_59]), c_0_43])]), c_0_44])).
% 1.28/1.52  fof(c_0_76, plain, ![X93, X94]:((k15_lattice3(X93,k6_domain_1(u1_struct_0(X93),X94))=X94|~m1_subset_1(X94,u1_struct_0(X93))|(v2_struct_0(X93)|~v10_lattices(X93)|~v4_lattice3(X93)|~l3_lattices(X93)))&(k16_lattice3(X93,k6_domain_1(u1_struct_0(X93),X94))=X94|~m1_subset_1(X94,u1_struct_0(X93))|(v2_struct_0(X93)|~v10_lattices(X93)|~v4_lattice3(X93)|~l3_lattices(X93)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t43_lattice3])])])])])).
% 1.28/1.52  fof(c_0_77, plain, ![X26, X27, X28]:(((k2_lattices(X26,X27,X28)=X27|~m1_subset_1(X28,u1_struct_0(X26))|X27!=k5_lattices(X26)|~m1_subset_1(X27,u1_struct_0(X26))|~v13_lattices(X26)|(v2_struct_0(X26)|~l1_lattices(X26)))&(k2_lattices(X26,X28,X27)=X27|~m1_subset_1(X28,u1_struct_0(X26))|X27!=k5_lattices(X26)|~m1_subset_1(X27,u1_struct_0(X26))|~v13_lattices(X26)|(v2_struct_0(X26)|~l1_lattices(X26))))&((m1_subset_1(esk2_2(X26,X27),u1_struct_0(X26))|X27=k5_lattices(X26)|~m1_subset_1(X27,u1_struct_0(X26))|~v13_lattices(X26)|(v2_struct_0(X26)|~l1_lattices(X26)))&(k2_lattices(X26,X27,esk2_2(X26,X27))!=X27|k2_lattices(X26,esk2_2(X26,X27),X27)!=X27|X27=k5_lattices(X26)|~m1_subset_1(X27,u1_struct_0(X26))|~v13_lattices(X26)|(v2_struct_0(X26)|~l1_lattices(X26))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattices])])])])])])).
% 1.28/1.52  fof(c_0_78, plain, ![X32, X33, X34]:((~r1_lattices(X32,X33,X34)|k2_lattices(X32,X33,X34)=X33|~m1_subset_1(X34,u1_struct_0(X32))|~m1_subset_1(X33,u1_struct_0(X32))|(v2_struct_0(X32)|~v8_lattices(X32)|~v9_lattices(X32)|~l3_lattices(X32)))&(k2_lattices(X32,X33,X34)!=X33|r1_lattices(X32,X33,X34)|~m1_subset_1(X34,u1_struct_0(X32))|~m1_subset_1(X33,u1_struct_0(X32))|(v2_struct_0(X32)|~v8_lattices(X32)|~v9_lattices(X32)|~l3_lattices(X32)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t21_lattices])])])])])).
% 1.28/1.52  cnf(c_0_79, plain, (v9_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 1.28/1.52  cnf(c_0_80, plain, (v8_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 1.28/1.52  cnf(c_0_81, negated_conjecture, (r1_lattices(esk16_0,X1,k5_lattices(esk16_0))|~r3_lattice3(esk16_0,X1,X2)|~m1_subset_1(X1,u1_struct_0(esk16_0))|~r2_hidden(k5_lattices(esk16_0),X2)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_43])]), c_0_44])).
% 1.28/1.52  cnf(c_0_82, negated_conjecture, (m1_subset_1(k16_lattice3(esk16_0,X1),u1_struct_0(esk16_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_43]), c_0_44])).
% 1.28/1.52  cnf(c_0_83, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_tarski(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 1.28/1.52  cnf(c_0_84, negated_conjecture, (r3_lattices(esk16_0,k15_lattice3(esk16_0,X1),k15_lattice3(esk16_0,X2))|r2_hidden(esk15_3(esk16_0,X1,X2),X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_58]), c_0_59]), c_0_43])]), c_0_44])).
% 1.28/1.52  cnf(c_0_85, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_68, c_0_38])).
% 1.28/1.52  cnf(c_0_86, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_69])).
% 1.28/1.52  fof(c_0_87, plain, ![X6, X7, X8, X9, X10]:((~r1_tarski(X6,X7)|(~r2_hidden(X8,X6)|r2_hidden(X8,X7)))&((r2_hidden(esk1_2(X9,X10),X9)|r1_tarski(X9,X10))&(~r2_hidden(esk1_2(X9,X10),X10)|r1_tarski(X9,X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 1.28/1.52  cnf(c_0_88, plain, (v2_struct_0(X1)|r2_hidden(X2,a_2_2_lattice3(X1,X3))|~r4_lattice3(X1,X2,X3)|~v4_lattice3(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(er,[status(thm)],[c_0_70])).
% 1.28/1.52  cnf(c_0_89, plain, (v2_struct_0(X1)|r4_lattice3(X1,X2,X3)|X2!=k15_lattice3(X1,X3)|~l3_lattices(X1)|~v10_lattices(X1)|~v4_lattice3(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(cn,[status(thm)],[c_0_71])).
% 1.28/1.52  cnf(c_0_90, plain, (r2_hidden(X3,a_2_6_lattice3(X2,X5))|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|X3!=X1|~m1_subset_1(X4,u1_struct_0(X2))|~r3_lattices(X2,X4,X1)|~r2_hidden(X4,X5)|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 1.28/1.52  cnf(c_0_91, negated_conjecture, (r3_lattices(esk16_0,k15_lattice3(esk16_0,X1),k15_lattice3(esk16_0,X2))|~r3_lattice3(esk16_0,k15_lattice3(esk16_0,X1),a_2_2_lattice3(esk16_0,X2))), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 1.28/1.52  cnf(c_0_92, negated_conjecture, (r3_lattice3(esk16_0,k15_lattice3(esk16_0,X1),a_2_2_lattice3(esk16_0,X1))), inference(spm,[status(thm)],[c_0_75, c_0_74])).
% 1.28/1.52  cnf(c_0_93, plain, (k15_lattice3(X1,k6_domain_1(u1_struct_0(X1),X2))=X2|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_76])).
% 1.28/1.52  cnf(c_0_94, plain, (k2_lattices(X1,X2,X3)=X3|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|X3!=k5_lattices(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~v13_lattices(X1)|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_77])).
% 1.28/1.52  cnf(c_0_95, plain, (k2_lattices(X1,X2,X3)=X2|v2_struct_0(X1)|~r1_lattices(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_78])).
% 1.28/1.52  cnf(c_0_96, negated_conjecture, (v9_lattices(esk16_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_59]), c_0_43])]), c_0_44])).
% 1.28/1.52  cnf(c_0_97, negated_conjecture, (v8_lattices(esk16_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_59]), c_0_43])]), c_0_44])).
% 1.28/1.52  cnf(c_0_98, negated_conjecture, (r1_lattices(esk16_0,k16_lattice3(esk16_0,X1),k5_lattices(esk16_0))|~r3_lattice3(esk16_0,k16_lattice3(esk16_0,X1),X2)|~r2_hidden(k5_lattices(esk16_0),X2)), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 1.28/1.52  cnf(c_0_99, negated_conjecture, (r3_lattices(esk16_0,k15_lattice3(esk16_0,k3_xboole_0(X1,X2)),k15_lattice3(esk16_0,X3))|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 1.28/1.52  cnf(c_0_100, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_85, c_0_86])).
% 1.28/1.52  cnf(c_0_101, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_87])).
% 1.28/1.52  cnf(c_0_102, negated_conjecture, (r2_hidden(k15_lattice3(esk16_0,X1),a_2_2_lattice3(esk16_0,X2))|~r4_lattice3(esk16_0,k15_lattice3(esk16_0,X1),X2)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_57]), c_0_58]), c_0_59]), c_0_43])]), c_0_44])).
% 1.28/1.52  cnf(c_0_103, plain, (r4_lattice3(X1,k15_lattice3(X1,X2),X2)|v2_struct_0(X1)|~v4_lattice3(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_89]), c_0_42])).
% 1.28/1.52  cnf(c_0_104, plain, (v2_struct_0(X1)|r2_hidden(X2,a_2_6_lattice3(X1,X3))|~r3_lattices(X1,X4,X2)|~v4_lattice3(X1)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)|~r2_hidden(X4,X3)), inference(er,[status(thm)],[c_0_90])).
% 1.28/1.52  cnf(c_0_105, negated_conjecture, (r3_lattices(esk16_0,k15_lattice3(esk16_0,X1),k15_lattice3(esk16_0,X1))), inference(spm,[status(thm)],[c_0_91, c_0_92])).
% 1.28/1.52  cnf(c_0_106, negated_conjecture, (k15_lattice3(esk16_0,k6_domain_1(u1_struct_0(esk16_0),k16_lattice3(esk16_0,X1)))=k16_lattice3(esk16_0,X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_82]), c_0_58]), c_0_59]), c_0_43])]), c_0_44])).
% 1.28/1.52  cnf(c_0_107, plain, (k2_lattices(X1,X2,k5_lattices(X1))=k5_lattices(X1)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v13_lattices(X1)|~l1_lattices(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_94]), c_0_35])).
% 1.28/1.52  cnf(c_0_108, negated_conjecture, (k2_lattices(esk16_0,X1,k5_lattices(esk16_0))=X1|~r1_lattices(esk16_0,X1,k5_lattices(esk16_0))|~m1_subset_1(X1,u1_struct_0(esk16_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_64]), c_0_96]), c_0_97]), c_0_43])]), c_0_44])).
% 1.28/1.52  cnf(c_0_109, negated_conjecture, (r1_lattices(esk16_0,k16_lattice3(esk16_0,X1),k5_lattices(esk16_0))|~r2_hidden(k5_lattices(esk16_0),X1)), inference(spm,[status(thm)],[c_0_98, c_0_75])).
% 1.28/1.52  cnf(c_0_110, negated_conjecture, (r3_lattices(esk16_0,k15_lattice3(esk16_0,k1_xboole_0),k15_lattice3(esk16_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_100]), c_0_38])])).
% 1.28/1.52  cnf(c_0_111, negated_conjecture, (k15_lattice3(esk16_0,k6_domain_1(u1_struct_0(esk16_0),k5_lattices(esk16_0)))=k5_lattices(esk16_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_64]), c_0_58]), c_0_59]), c_0_43])]), c_0_44])).
% 1.28/1.52  fof(c_0_112, plain, ![X95, X96]:((k15_lattice3(X95,X96)=k15_lattice3(X95,a_2_5_lattice3(X95,X96))|(v2_struct_0(X95)|~v10_lattices(X95)|~v4_lattice3(X95)|~l3_lattices(X95)))&(k16_lattice3(X95,X96)=k16_lattice3(X95,a_2_6_lattice3(X95,X96))|(v2_struct_0(X95)|~v10_lattices(X95)|~v4_lattice3(X95)|~l3_lattices(X95)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t47_lattice3])])])])])).
% 1.28/1.52  cnf(c_0_113, negated_conjecture, (r2_hidden(k15_lattice3(esk16_0,X1),X2)|~r4_lattice3(esk16_0,k15_lattice3(esk16_0,X1),X3)|~r1_tarski(a_2_2_lattice3(esk16_0,X3),X2)), inference(spm,[status(thm)],[c_0_101, c_0_102])).
% 1.28/1.52  cnf(c_0_114, negated_conjecture, (r4_lattice3(esk16_0,k15_lattice3(esk16_0,X1),X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_58]), c_0_59]), c_0_43])]), c_0_44])).
% 1.28/1.52  cnf(c_0_115, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_53])).
% 1.28/1.52  cnf(c_0_116, negated_conjecture, (r2_hidden(X1,a_2_6_lattice3(esk16_0,X2))|~r3_lattices(esk16_0,k16_lattice3(esk16_0,X3),X1)|~m1_subset_1(X1,u1_struct_0(esk16_0))|~r2_hidden(k16_lattice3(esk16_0,X3),X2)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_82]), c_0_58]), c_0_59]), c_0_43])]), c_0_44])).
% 1.28/1.52  cnf(c_0_117, negated_conjecture, (r3_lattices(esk16_0,k16_lattice3(esk16_0,X1),k16_lattice3(esk16_0,X1))), inference(spm,[status(thm)],[c_0_105, c_0_106])).
% 1.28/1.52  cnf(c_0_118, negated_conjecture, (k2_lattices(esk16_0,k16_lattice3(esk16_0,X1),k5_lattices(esk16_0))=k5_lattices(esk16_0)|~v13_lattices(esk16_0)|~l1_lattices(esk16_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_82]), c_0_44])).
% 1.28/1.52  cnf(c_0_119, negated_conjecture, (k2_lattices(esk16_0,k16_lattice3(esk16_0,X1),k5_lattices(esk16_0))=k16_lattice3(esk16_0,X1)|~r2_hidden(k5_lattices(esk16_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_109]), c_0_82])])).
% 1.28/1.52  cnf(c_0_120, negated_conjecture, (r2_hidden(X1,a_2_6_lattice3(esk16_0,X2))|~r3_lattices(esk16_0,k15_lattice3(esk16_0,X3),X1)|~m1_subset_1(X1,u1_struct_0(esk16_0))|~r2_hidden(k15_lattice3(esk16_0,X3),X2)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_57]), c_0_58]), c_0_59]), c_0_43])]), c_0_44])).
% 1.28/1.52  cnf(c_0_121, negated_conjecture, (r3_lattices(esk16_0,k15_lattice3(esk16_0,k1_xboole_0),k5_lattices(esk16_0))), inference(spm,[status(thm)],[c_0_110, c_0_111])).
% 1.28/1.52  cnf(c_0_122, plain, (k16_lattice3(X1,X2)=k16_lattice3(X1,a_2_6_lattice3(X1,X2))|v2_struct_0(X1)|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_112])).
% 1.28/1.52  cnf(c_0_123, negated_conjecture, (r2_hidden(k15_lattice3(esk16_0,X1),X2)|~r1_tarski(a_2_2_lattice3(esk16_0,X1),X2)), inference(spm,[status(thm)],[c_0_113, c_0_114])).
% 1.28/1.52  cnf(c_0_124, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_115])).
% 1.28/1.52  cnf(c_0_125, negated_conjecture, (r2_hidden(k16_lattice3(esk16_0,X1),a_2_6_lattice3(esk16_0,X2))|~r2_hidden(k16_lattice3(esk16_0,X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116, c_0_117]), c_0_82])])).
% 1.28/1.52  cnf(c_0_126, plain, (k16_lattice3(X1,k6_domain_1(u1_struct_0(X1),X2))=X2|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_76])).
% 1.28/1.52  cnf(c_0_127, negated_conjecture, (k16_lattice3(esk16_0,X1)=k5_lattices(esk16_0)|~v13_lattices(esk16_0)|~l1_lattices(esk16_0)|~r2_hidden(k5_lattices(esk16_0),X1)), inference(spm,[status(thm)],[c_0_118, c_0_119])).
% 1.28/1.52  cnf(c_0_128, negated_conjecture, (r2_hidden(k5_lattices(esk16_0),a_2_6_lattice3(esk16_0,X1))|~r2_hidden(k15_lattice3(esk16_0,k1_xboole_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120, c_0_121]), c_0_64])])).
% 1.28/1.52  cnf(c_0_129, negated_conjecture, (k16_lattice3(esk16_0,a_2_6_lattice3(esk16_0,X1))=k16_lattice3(esk16_0,X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122, c_0_58]), c_0_59]), c_0_43])]), c_0_44])).
% 1.28/1.52  cnf(c_0_130, negated_conjecture, (r2_hidden(k15_lattice3(esk16_0,X1),a_2_2_lattice3(esk16_0,X1))), inference(spm,[status(thm)],[c_0_123, c_0_124])).
% 1.28/1.52  cnf(c_0_131, negated_conjecture, (k15_lattice3(esk16_0,k6_domain_1(u1_struct_0(esk16_0),k15_lattice3(esk16_0,X1)))=k15_lattice3(esk16_0,X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_57]), c_0_58]), c_0_59]), c_0_43])]), c_0_44])).
% 1.28/1.52  cnf(c_0_132, negated_conjecture, (v2_struct_0(esk16_0)|~v10_lattices(esk16_0)|~v13_lattices(esk16_0)|~l3_lattices(esk16_0)|k5_lattices(esk16_0)!=k15_lattice3(esk16_0,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 1.28/1.52  cnf(c_0_133, negated_conjecture, (r2_hidden(k16_lattice3(esk16_0,X1),X2)|~r2_hidden(k16_lattice3(esk16_0,X1),X3)|~r1_tarski(a_2_6_lattice3(esk16_0,X3),X2)), inference(spm,[status(thm)],[c_0_101, c_0_125])).
% 1.28/1.52  cnf(c_0_134, negated_conjecture, (k16_lattice3(esk16_0,k6_domain_1(u1_struct_0(esk16_0),k15_lattice3(esk16_0,X1)))=k15_lattice3(esk16_0,X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126, c_0_57]), c_0_58]), c_0_59]), c_0_43])]), c_0_44])).
% 1.28/1.52  cnf(c_0_135, negated_conjecture, (r2_hidden(k15_lattice3(esk16_0,X1),a_2_6_lattice3(esk16_0,X2))|~r2_hidden(k15_lattice3(esk16_0,k1_xboole_0),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120, c_0_110]), c_0_57])])).
% 1.28/1.52  fof(c_0_136, plain, ![X35, X37, X38]:(((m1_subset_1(esk3_1(X35),u1_struct_0(X35))|~v13_lattices(X35)|(v2_struct_0(X35)|~l1_lattices(X35)))&((k2_lattices(X35,esk3_1(X35),X37)=esk3_1(X35)|~m1_subset_1(X37,u1_struct_0(X35))|~v13_lattices(X35)|(v2_struct_0(X35)|~l1_lattices(X35)))&(k2_lattices(X35,X37,esk3_1(X35))=esk3_1(X35)|~m1_subset_1(X37,u1_struct_0(X35))|~v13_lattices(X35)|(v2_struct_0(X35)|~l1_lattices(X35)))))&((m1_subset_1(esk4_2(X35,X38),u1_struct_0(X35))|~m1_subset_1(X38,u1_struct_0(X35))|v13_lattices(X35)|(v2_struct_0(X35)|~l1_lattices(X35)))&(k2_lattices(X35,X38,esk4_2(X35,X38))!=X38|k2_lattices(X35,esk4_2(X35,X38),X38)!=X38|~m1_subset_1(X38,u1_struct_0(X35))|v13_lattices(X35)|(v2_struct_0(X35)|~l1_lattices(X35))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d13_lattices])])])])])])).
% 1.28/1.52  cnf(c_0_137, plain, (m1_subset_1(esk12_3(X1,X2,X3),u1_struct_0(X2))|v2_struct_0(X2)|~r2_hidden(X1,a_2_6_lattice3(X2,X3))|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 1.28/1.52  cnf(c_0_138, negated_conjecture, (k16_lattice3(esk16_0,X1)=k5_lattices(esk16_0)|~v13_lattices(esk16_0)|~l1_lattices(esk16_0)|~r2_hidden(k15_lattice3(esk16_0,k1_xboole_0),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127, c_0_128]), c_0_129])).
% 1.28/1.52  cnf(c_0_139, negated_conjecture, (r2_hidden(k15_lattice3(esk16_0,X1),a_2_2_lattice3(esk16_0,k6_domain_1(u1_struct_0(esk16_0),k15_lattice3(esk16_0,X1))))), inference(spm,[status(thm)],[c_0_130, c_0_131])).
% 1.28/1.52  cnf(c_0_140, negated_conjecture, (k5_lattices(esk16_0)!=k15_lattice3(esk16_0,k1_xboole_0)|~v13_lattices(esk16_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_132, c_0_43]), c_0_59])]), c_0_44])).
% 1.28/1.52  cnf(c_0_141, negated_conjecture, (r2_hidden(k15_lattice3(esk16_0,X1),X2)|~r2_hidden(k15_lattice3(esk16_0,X1),X3)|~r1_tarski(a_2_6_lattice3(esk16_0,X3),X2)), inference(spm,[status(thm)],[c_0_133, c_0_134])).
% 1.28/1.52  cnf(c_0_142, negated_conjecture, (r2_hidden(k15_lattice3(esk16_0,X1),X2)|~r2_hidden(k15_lattice3(esk16_0,k1_xboole_0),X3)|~r1_tarski(a_2_6_lattice3(esk16_0,X3),X2)), inference(spm,[status(thm)],[c_0_101, c_0_135])).
% 1.28/1.52  cnf(c_0_143, plain, (m1_subset_1(esk4_2(X1,X2),u1_struct_0(X1))|v13_lattices(X1)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_136])).
% 1.28/1.52  cnf(c_0_144, negated_conjecture, (m1_subset_1(esk12_3(k15_lattice3(esk16_0,X1),esk16_0,X2),u1_struct_0(esk16_0))|~r2_hidden(k15_lattice3(esk16_0,k1_xboole_0),X2)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137, c_0_135]), c_0_58]), c_0_59]), c_0_43])]), c_0_44])).
% 1.28/1.52  cnf(c_0_145, negated_conjecture, (~v13_lattices(esk16_0)|~l1_lattices(esk16_0)), inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_138, c_0_139]), c_0_74]), c_0_131]), c_0_140])).
% 1.28/1.52  cnf(c_0_146, plain, (X1=esk12_3(X1,X2,X3)|v2_struct_0(X2)|~r2_hidden(X1,a_2_6_lattice3(X2,X3))|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 1.28/1.52  cnf(c_0_147, negated_conjecture, (r2_hidden(k15_lattice3(esk16_0,X1),X2)|~r1_tarski(a_2_6_lattice3(esk16_0,a_2_2_lattice3(esk16_0,X1)),X2)), inference(spm,[status(thm)],[c_0_141, c_0_130])).
% 1.28/1.52  cnf(c_0_148, negated_conjecture, (r2_hidden(k15_lattice3(esk16_0,X1),X2)|~r1_tarski(a_2_6_lattice3(esk16_0,a_2_2_lattice3(esk16_0,k1_xboole_0)),X2)), inference(spm,[status(thm)],[c_0_142, c_0_130])).
% 1.28/1.52  cnf(c_0_149, negated_conjecture, (m1_subset_1(esk4_2(esk16_0,esk12_3(k15_lattice3(esk16_0,X1),esk16_0,X2)),u1_struct_0(esk16_0))|~l1_lattices(esk16_0)|~r2_hidden(k15_lattice3(esk16_0,k1_xboole_0),X2)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_143, c_0_144]), c_0_44]), c_0_145])).
% 1.28/1.52  cnf(c_0_150, negated_conjecture, (esk12_3(k15_lattice3(esk16_0,X1),esk16_0,X2)=k15_lattice3(esk16_0,X1)|~r2_hidden(k15_lattice3(esk16_0,k1_xboole_0),X2)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_146, c_0_135]), c_0_58]), c_0_59]), c_0_43])]), c_0_44])).
% 1.28/1.52  cnf(c_0_151, negated_conjecture, (r2_hidden(k15_lattice3(esk16_0,X1),a_2_6_lattice3(esk16_0,a_2_2_lattice3(esk16_0,X1)))), inference(spm,[status(thm)],[c_0_147, c_0_124])).
% 1.28/1.52  cnf(c_0_152, negated_conjecture, (r1_lattices(esk16_0,X1,k15_lattice3(esk16_0,X2))|~r3_lattice3(esk16_0,X1,X3)|~m1_subset_1(X1,u1_struct_0(esk16_0))|~r2_hidden(k15_lattice3(esk16_0,X2),X3)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_57]), c_0_43])]), c_0_44])).
% 1.28/1.52  cnf(c_0_153, negated_conjecture, (r2_hidden(k15_lattice3(esk16_0,X1),a_2_6_lattice3(esk16_0,a_2_2_lattice3(esk16_0,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_148, c_0_124])).
% 1.28/1.52  cnf(c_0_154, negated_conjecture, (m1_subset_1(esk4_2(esk16_0,k15_lattice3(esk16_0,X1)),u1_struct_0(esk16_0))|~l1_lattices(esk16_0)|~r2_hidden(k15_lattice3(esk16_0,k1_xboole_0),X2)), inference(spm,[status(thm)],[c_0_149, c_0_150])).
% 1.28/1.52  cnf(c_0_155, negated_conjecture, (r2_hidden(k15_lattice3(esk16_0,X1),X2)|~r1_tarski(a_2_6_lattice3(esk16_0,a_2_6_lattice3(esk16_0,a_2_2_lattice3(esk16_0,X1))),X2)), inference(spm,[status(thm)],[c_0_141, c_0_151])).
% 1.28/1.52  cnf(c_0_156, negated_conjecture, (r1_lattices(esk16_0,X1,k15_lattice3(esk16_0,X2))|~r3_lattice3(esk16_0,X1,a_2_6_lattice3(esk16_0,a_2_2_lattice3(esk16_0,k1_xboole_0)))|~m1_subset_1(X1,u1_struct_0(esk16_0))), inference(spm,[status(thm)],[c_0_152, c_0_153])).
% 1.28/1.52  cnf(c_0_157, negated_conjecture, (m1_subset_1(esk4_2(esk16_0,k15_lattice3(esk16_0,X1)),u1_struct_0(esk16_0))|~r2_hidden(k15_lattice3(esk16_0,k1_xboole_0),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_154, c_0_36]), c_0_43])])).
% 1.28/1.52  cnf(c_0_158, negated_conjecture, (r2_hidden(k15_lattice3(esk16_0,X1),a_2_6_lattice3(esk16_0,a_2_6_lattice3(esk16_0,a_2_2_lattice3(esk16_0,X1))))), inference(spm,[status(thm)],[c_0_155, c_0_124])).
% 1.28/1.52  cnf(c_0_159, negated_conjecture, (k2_lattices(esk16_0,X1,k15_lattice3(esk16_0,X2))=X1|~r1_lattices(esk16_0,X1,k15_lattice3(esk16_0,X2))|~m1_subset_1(X1,u1_struct_0(esk16_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_57]), c_0_96]), c_0_97]), c_0_43])]), c_0_44])).
% 1.28/1.52  cnf(c_0_160, negated_conjecture, (r1_lattices(esk16_0,k15_lattice3(esk16_0,k1_xboole_0),k15_lattice3(esk16_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_156, c_0_75]), c_0_129]), c_0_74]), c_0_129]), c_0_74]), c_0_57])])).
% 1.28/1.52  cnf(c_0_161, negated_conjecture, (m1_subset_1(esk4_2(esk16_0,k15_lattice3(esk16_0,X1)),u1_struct_0(esk16_0))), inference(spm,[status(thm)],[c_0_157, c_0_158])).
% 1.28/1.52  cnf(c_0_162, negated_conjecture, (k2_lattices(esk16_0,k15_lattice3(esk16_0,k1_xboole_0),k15_lattice3(esk16_0,X1))=k15_lattice3(esk16_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_159, c_0_160]), c_0_57])])).
% 1.28/1.52  cnf(c_0_163, negated_conjecture, (k15_lattice3(esk16_0,k6_domain_1(u1_struct_0(esk16_0),esk4_2(esk16_0,k15_lattice3(esk16_0,X1))))=esk4_2(esk16_0,k15_lattice3(esk16_0,X1))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_161]), c_0_58]), c_0_59]), c_0_43])]), c_0_44])).
% 1.28/1.52  fof(c_0_164, plain, ![X51, X52, X53]:((~v6_lattices(X51)|(~m1_subset_1(X52,u1_struct_0(X51))|(~m1_subset_1(X53,u1_struct_0(X51))|k2_lattices(X51,X52,X53)=k2_lattices(X51,X53,X52)))|(v2_struct_0(X51)|~l1_lattices(X51)))&((m1_subset_1(esk7_1(X51),u1_struct_0(X51))|v6_lattices(X51)|(v2_struct_0(X51)|~l1_lattices(X51)))&((m1_subset_1(esk8_1(X51),u1_struct_0(X51))|v6_lattices(X51)|(v2_struct_0(X51)|~l1_lattices(X51)))&(k2_lattices(X51,esk7_1(X51),esk8_1(X51))!=k2_lattices(X51,esk8_1(X51),esk7_1(X51))|v6_lattices(X51)|(v2_struct_0(X51)|~l1_lattices(X51)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d6_lattices])])])])])])).
% 1.28/1.52  cnf(c_0_165, plain, (v6_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 1.28/1.52  cnf(c_0_166, plain, (v13_lattices(X1)|v2_struct_0(X1)|k2_lattices(X1,X2,esk4_2(X1,X2))!=X2|k2_lattices(X1,esk4_2(X1,X2),X2)!=X2|~m1_subset_1(X2,u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_136])).
% 1.28/1.52  cnf(c_0_167, negated_conjecture, (k2_lattices(esk16_0,k15_lattice3(esk16_0,k1_xboole_0),esk4_2(esk16_0,k15_lattice3(esk16_0,X1)))=k15_lattice3(esk16_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_162, c_0_163])).
% 1.28/1.52  cnf(c_0_168, plain, (k2_lattices(X1,X2,X3)=k2_lattices(X1,X3,X2)|v2_struct_0(X1)|~v6_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_164])).
% 1.28/1.52  cnf(c_0_169, negated_conjecture, (v6_lattices(esk16_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_165, c_0_59]), c_0_43])]), c_0_44])).
% 1.28/1.52  cnf(c_0_170, negated_conjecture, (k2_lattices(esk16_0,esk4_2(esk16_0,k15_lattice3(esk16_0,k1_xboole_0)),k15_lattice3(esk16_0,k1_xboole_0))!=k15_lattice3(esk16_0,k1_xboole_0)|~l1_lattices(esk16_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_166, c_0_167]), c_0_57])]), c_0_44]), c_0_145])).
% 1.28/1.52  cnf(c_0_171, negated_conjecture, (k2_lattices(esk16_0,X1,k15_lattice3(esk16_0,X2))=k2_lattices(esk16_0,k15_lattice3(esk16_0,X2),X1)|~m1_subset_1(X1,u1_struct_0(esk16_0))|~l1_lattices(esk16_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_168, c_0_57]), c_0_169])]), c_0_44])).
% 1.28/1.52  cnf(c_0_172, negated_conjecture, (~l1_lattices(esk16_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_170, c_0_171]), c_0_167]), c_0_161])])).
% 1.28/1.52  cnf(c_0_173, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_172, c_0_36]), c_0_43])]), ['proof']).
% 1.28/1.52  # SZS output end CNFRefutation
% 1.28/1.52  # Proof object total steps             : 174
% 1.28/1.52  # Proof object clause steps            : 121
% 1.28/1.52  # Proof object formula steps           : 53
% 1.28/1.52  # Proof object conjectures             : 77
% 1.28/1.52  # Proof object clause conjectures      : 74
% 1.28/1.52  # Proof object formula conjectures     : 3
% 1.28/1.52  # Proof object initial clauses used    : 38
% 1.28/1.52  # Proof object initial formulas used   : 26
% 1.28/1.52  # Proof object generating inferences   : 74
% 1.28/1.52  # Proof object simplifying inferences  : 158
% 1.28/1.52  # Training examples: 0 positive, 0 negative
% 1.28/1.52  # Parsed axioms                        : 28
% 1.28/1.52  # Removed by relevancy pruning/SinE    : 0
% 1.28/1.52  # Initial clauses                      : 82
% 1.28/1.52  # Removed in clause preprocessing      : 1
% 1.28/1.52  # Initial clauses in saturation        : 81
% 1.28/1.52  # Processed clauses                    : 13406
% 1.28/1.52  # ...of these trivial                  : 304
% 1.28/1.52  # ...subsumed                          : 10207
% 1.28/1.52  # ...remaining for further processing  : 2895
% 1.28/1.52  # Other redundant clauses eliminated   : 11
% 1.28/1.52  # Clauses deleted for lack of memory   : 0
% 1.28/1.52  # Backward-subsumed                    : 360
% 1.28/1.52  # Backward-rewritten                   : 56
% 1.28/1.52  # Generated clauses                    : 75267
% 1.28/1.52  # ...of the previous two non-trivial   : 70249
% 1.28/1.52  # Contextual simplify-reflections      : 103
% 1.28/1.52  # Paramodulations                      : 75256
% 1.28/1.52  # Factorizations                       : 0
% 1.28/1.52  # Equation resolutions                 : 11
% 1.28/1.52  # Propositional unsat checks           : 0
% 1.28/1.52  #    Propositional check models        : 0
% 1.28/1.52  #    Propositional check unsatisfiable : 0
% 1.28/1.52  #    Propositional clauses             : 0
% 1.28/1.52  #    Propositional clauses after purity: 0
% 1.28/1.52  #    Propositional unsat core size     : 0
% 1.28/1.52  #    Propositional preprocessing time  : 0.000
% 1.28/1.52  #    Propositional encoding time       : 0.000
% 1.28/1.52  #    Propositional solver time         : 0.000
% 1.28/1.52  #    Success case prop preproc time    : 0.000
% 1.28/1.52  #    Success case prop encoding time   : 0.000
% 1.28/1.52  #    Success case prop solver time     : 0.000
% 1.28/1.52  # Current number of processed clauses  : 2388
% 1.28/1.52  #    Positive orientable unit clauses  : 492
% 1.28/1.52  #    Positive unorientable unit clauses: 0
% 1.28/1.52  #    Negative unit clauses             : 96
% 1.28/1.52  #    Non-unit-clauses                  : 1800
% 1.28/1.52  # Current number of unprocessed clauses: 56337
% 1.28/1.52  # ...number of literals in the above   : 175177
% 1.28/1.52  # Current number of archived formulas  : 0
% 1.28/1.52  # Current number of archived clauses   : 496
% 1.28/1.52  # Clause-clause subsumption calls (NU) : 873388
% 1.28/1.52  # Rec. Clause-clause subsumption calls : 519018
% 1.28/1.52  # Non-unit clause-clause subsumptions  : 9336
% 1.28/1.52  # Unit Clause-clause subsumption calls : 128304
% 1.28/1.52  # Rewrite failures with RHS unbound    : 0
% 1.28/1.52  # BW rewrite match attempts            : 4077
% 1.28/1.52  # BW rewrite match successes           : 125
% 1.28/1.52  # Condensation attempts                : 0
% 1.28/1.52  # Condensation successes               : 0
% 1.28/1.52  # Termbank termtop insertions          : 1529982
% 1.34/1.52  
% 1.34/1.52  # -------------------------------------------------
% 1.34/1.52  # User time                : 1.114 s
% 1.34/1.52  # System time              : 0.046 s
% 1.34/1.52  # Total time               : 1.160 s
% 1.34/1.52  # Maximum resident set size: 1616 pages
%------------------------------------------------------------------------------
