%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:07 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 272 expanded)
%              Number of clauses        :   55 ( 114 expanded)
%              Number of leaves         :   16 (  73 expanded)
%              Depth                    :   16
%              Number of atoms          :  662 (2151 expanded)
%              Number of equality atoms :   60 ( 157 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal clause size      :   40 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

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

fof(t45_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v4_lattice3(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( X2 = k15_lattice3(X1,a_2_3_lattice3(X1,X2))
            & X2 = k16_lattice3(X1,a_2_4_lattice3(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_lattice3)).

fof(fraenkel_a_2_4_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X2)
        & v10_lattices(X2)
        & v4_lattice3(X2)
        & l3_lattices(X2)
        & m1_subset_1(X3,u1_struct_0(X2)) )
     => ( r2_hidden(X1,a_2_4_lattice3(X2,X3))
      <=> ? [X4] :
            ( m1_subset_1(X4,u1_struct_0(X2))
            & X1 = X4
            & r3_lattices(X2,X3,X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_4_lattice3)).

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

fof(dt_k15_lattice3,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k15_lattice3)).

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

fof(c_0_16,plain,(
    ! [X7,X8] :
      ( ~ r2_hidden(X7,X8)
      | ~ r1_tarski(X8,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_17,plain,(
    ! [X6] : r1_tarski(k1_xboole_0,X6) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_18,plain,(
    ! [X44,X45,X46,X47,X48] :
      ( ( r3_lattice3(X44,X45,X46)
        | X45 != k16_lattice3(X44,X46)
        | ~ m1_subset_1(X45,u1_struct_0(X44))
        | v2_struct_0(X44)
        | ~ v10_lattices(X44)
        | ~ v4_lattice3(X44)
        | ~ l3_lattices(X44) )
      & ( ~ m1_subset_1(X47,u1_struct_0(X44))
        | ~ r3_lattice3(X44,X47,X46)
        | r3_lattices(X44,X47,X45)
        | X45 != k16_lattice3(X44,X46)
        | ~ m1_subset_1(X45,u1_struct_0(X44))
        | v2_struct_0(X44)
        | ~ v10_lattices(X44)
        | ~ v4_lattice3(X44)
        | ~ l3_lattices(X44) )
      & ( m1_subset_1(esk8_3(X44,X45,X48),u1_struct_0(X44))
        | ~ r3_lattice3(X44,X45,X48)
        | X45 = k16_lattice3(X44,X48)
        | ~ m1_subset_1(X45,u1_struct_0(X44))
        | v2_struct_0(X44)
        | ~ v10_lattices(X44)
        | ~ v4_lattice3(X44)
        | ~ l3_lattices(X44) )
      & ( r3_lattice3(X44,esk8_3(X44,X45,X48),X48)
        | ~ r3_lattice3(X44,X45,X48)
        | X45 = k16_lattice3(X44,X48)
        | ~ m1_subset_1(X45,u1_struct_0(X44))
        | v2_struct_0(X44)
        | ~ v10_lattices(X44)
        | ~ v4_lattice3(X44)
        | ~ l3_lattices(X44) )
      & ( ~ r3_lattices(X44,esk8_3(X44,X45,X48),X45)
        | ~ r3_lattice3(X44,X45,X48)
        | X45 = k16_lattice3(X44,X48)
        | ~ m1_subset_1(X45,u1_struct_0(X44))
        | v2_struct_0(X44)
        | ~ v10_lattices(X44)
        | ~ v4_lattice3(X44)
        | ~ l3_lattices(X44) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_lattice3])])])])])])])).

fof(c_0_19,plain,(
    ! [X50,X51] :
      ( ( X51 = k15_lattice3(X50,a_2_3_lattice3(X50,X51))
        | ~ m1_subset_1(X51,u1_struct_0(X50))
        | v2_struct_0(X50)
        | ~ v10_lattices(X50)
        | ~ v4_lattice3(X50)
        | ~ l3_lattices(X50) )
      & ( X51 = k16_lattice3(X50,a_2_4_lattice3(X50,X51))
        | ~ m1_subset_1(X51,u1_struct_0(X50))
        | v2_struct_0(X50)
        | ~ v10_lattices(X50)
        | ~ v4_lattice3(X50)
        | ~ l3_lattices(X50) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t45_lattice3])])])])])).

fof(c_0_20,plain,(
    ! [X39,X40,X41,X43] :
      ( ( m1_subset_1(esk7_3(X39,X40,X41),u1_struct_0(X40))
        | ~ r2_hidden(X39,a_2_4_lattice3(X40,X41))
        | v2_struct_0(X40)
        | ~ v10_lattices(X40)
        | ~ v4_lattice3(X40)
        | ~ l3_lattices(X40)
        | ~ m1_subset_1(X41,u1_struct_0(X40)) )
      & ( X39 = esk7_3(X39,X40,X41)
        | ~ r2_hidden(X39,a_2_4_lattice3(X40,X41))
        | v2_struct_0(X40)
        | ~ v10_lattices(X40)
        | ~ v4_lattice3(X40)
        | ~ l3_lattices(X40)
        | ~ m1_subset_1(X41,u1_struct_0(X40)) )
      & ( r3_lattices(X40,X41,esk7_3(X39,X40,X41))
        | ~ r2_hidden(X39,a_2_4_lattice3(X40,X41))
        | v2_struct_0(X40)
        | ~ v10_lattices(X40)
        | ~ v4_lattice3(X40)
        | ~ l3_lattices(X40)
        | ~ m1_subset_1(X41,u1_struct_0(X40)) )
      & ( ~ m1_subset_1(X43,u1_struct_0(X40))
        | X39 != X43
        | ~ r3_lattices(X40,X41,X43)
        | r2_hidden(X39,a_2_4_lattice3(X40,X41))
        | v2_struct_0(X40)
        | ~ v10_lattices(X40)
        | ~ v4_lattice3(X40)
        | ~ l3_lattices(X40)
        | ~ m1_subset_1(X41,u1_struct_0(X40)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_4_lattice3])])])])])])).

cnf(c_0_21,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_23,plain,(
    ! [X52,X53,X54,X56] :
      ( ( m1_subset_1(esk9_3(X52,X53,X54),u1_struct_0(X52))
        | r3_lattices(X52,k15_lattice3(X52,X53),k15_lattice3(X52,X54))
        | v2_struct_0(X52)
        | ~ v10_lattices(X52)
        | ~ v4_lattice3(X52)
        | ~ l3_lattices(X52) )
      & ( r2_hidden(esk9_3(X52,X53,X54),X53)
        | r3_lattices(X52,k15_lattice3(X52,X53),k15_lattice3(X52,X54))
        | v2_struct_0(X52)
        | ~ v10_lattices(X52)
        | ~ v4_lattice3(X52)
        | ~ l3_lattices(X52) )
      & ( ~ m1_subset_1(X56,u1_struct_0(X52))
        | ~ r3_lattices(X52,esk9_3(X52,X53,X54),X56)
        | ~ r2_hidden(X56,X54)
        | r3_lattices(X52,k15_lattice3(X52,X53),k15_lattice3(X52,X54))
        | v2_struct_0(X52)
        | ~ v10_lattices(X52)
        | ~ v4_lattice3(X52)
        | ~ l3_lattices(X52) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t48_lattice3])])])])])])).

fof(c_0_24,plain,(
    ! [X24,X25,X26,X27,X28] :
      ( ( ~ r3_lattice3(X24,X25,X26)
        | ~ m1_subset_1(X27,u1_struct_0(X24))
        | ~ r2_hidden(X27,X26)
        | r1_lattices(X24,X25,X27)
        | ~ m1_subset_1(X25,u1_struct_0(X24))
        | v2_struct_0(X24)
        | ~ l3_lattices(X24) )
      & ( m1_subset_1(esk4_3(X24,X25,X28),u1_struct_0(X24))
        | r3_lattice3(X24,X25,X28)
        | ~ m1_subset_1(X25,u1_struct_0(X24))
        | v2_struct_0(X24)
        | ~ l3_lattices(X24) )
      & ( r2_hidden(esk4_3(X24,X25,X28),X28)
        | r3_lattice3(X24,X25,X28)
        | ~ m1_subset_1(X25,u1_struct_0(X24))
        | v2_struct_0(X24)
        | ~ l3_lattices(X24) )
      & ( ~ r1_lattices(X24,X25,esk4_3(X24,X25,X28))
        | r3_lattice3(X24,X25,X28)
        | ~ m1_subset_1(X25,u1_struct_0(X24))
        | v2_struct_0(X24)
        | ~ l3_lattices(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattice3])])])])])])])).

cnf(c_0_25,plain,
    ( r3_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | X2 != k16_lattice3(X1,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( X1 = k16_lattice3(X2,a_2_4_lattice3(X2,X1))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( m1_subset_1(esk7_3(X1,X2,X3),u1_struct_0(X2))
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_4_lattice3(X2,X3))
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( X1 = esk7_3(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_4_lattice3(X2,X3))
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_30,plain,
    ( r2_hidden(esk9_3(X1,X2,X3),X2)
    | r3_lattices(X1,k15_lattice3(X1,X2),k15_lattice3(X1,X3))
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( r1_lattices(X1,X2,X4)
    | v2_struct_0(X1)
    | ~ r3_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,plain,
    ( r3_lattice3(X1,X2,a_2_4_lattice3(X1,X2))
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26])])).

cnf(c_0_33,plain,
    ( m1_subset_1(X1,u1_struct_0(X2))
    | v2_struct_0(X2)
    | ~ v4_lattice3(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2)
    | ~ r2_hidden(X1,a_2_4_lattice3(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_34,plain,
    ( r2_hidden(X3,a_2_4_lattice3(X2,X4))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | X3 != X1
    | ~ r3_lattices(X2,X4,X1)
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2)
    | ~ m1_subset_1(X4,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_35,plain,
    ( r3_lattices(X1,k15_lattice3(X1,k1_xboole_0),k15_lattice3(X1,X2))
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_36,plain,
    ( X1 = k15_lattice3(X2,a_2_3_lattice3(X2,X1))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_37,plain,(
    ! [X35,X36] :
      ( v2_struct_0(X35)
      | ~ l3_lattices(X35)
      | m1_subset_1(k15_lattice3(X35,X36),u1_struct_0(X35)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k15_lattice3])])])).

cnf(c_0_38,plain,
    ( r3_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,esk4_3(X1,X2,X3))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_39,plain,
    ( r1_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ r2_hidden(X3,a_2_4_lattice3(X1,X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])).

cnf(c_0_40,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,a_2_4_lattice3(X1,X3))
    | ~ r3_lattices(X1,X3,X2)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(er,[status(thm)],[c_0_34])).

cnf(c_0_41,plain,
    ( r3_lattices(X1,k15_lattice3(X1,k1_xboole_0),X2)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_42,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_43,plain,
    ( r3_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ r2_hidden(esk4_3(X1,X2,X3),a_2_4_lattice3(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_44,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,a_2_4_lattice3(X1,k15_lattice3(X1,k1_xboole_0)))
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])).

cnf(c_0_45,plain,
    ( r3_lattice3(X1,k15_lattice3(X1,k1_xboole_0),X2)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(esk4_3(X1,k15_lattice3(X1,k1_xboole_0),X2),u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_42])).

cnf(c_0_46,plain,
    ( m1_subset_1(esk4_3(X1,X2,X3),u1_struct_0(X1))
    | r3_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_47,plain,
    ( r3_lattice3(X1,k15_lattice3(X1,k1_xboole_0),X2)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_42])).

cnf(c_0_48,plain,
    ( r1_lattices(X1,k15_lattice3(X1,k1_xboole_0),X2)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ r2_hidden(X2,X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_47]),c_0_42])).

fof(c_0_49,plain,(
    ! [X14] :
      ( v2_struct_0(X14)
      | ~ l1_lattices(X14)
      | m1_subset_1(k5_lattices(X14),u1_struct_0(X14)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_lattices])])])).

fof(c_0_50,plain,(
    ! [X15] :
      ( ( l1_lattices(X15)
        | ~ l3_lattices(X15) )
      & ( l2_lattices(X15)
        | ~ l3_lattices(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).

fof(c_0_51,plain,(
    ! [X10,X11,X12] :
      ( ( k2_lattices(X10,X11,X12) = X11
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | X11 != k5_lattices(X10)
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | ~ v13_lattices(X10)
        | v2_struct_0(X10)
        | ~ l1_lattices(X10) )
      & ( k2_lattices(X10,X12,X11) = X11
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | X11 != k5_lattices(X10)
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | ~ v13_lattices(X10)
        | v2_struct_0(X10)
        | ~ l1_lattices(X10) )
      & ( m1_subset_1(esk1_2(X10,X11),u1_struct_0(X10))
        | X11 = k5_lattices(X10)
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | ~ v13_lattices(X10)
        | v2_struct_0(X10)
        | ~ l1_lattices(X10) )
      & ( k2_lattices(X10,X11,esk1_2(X10,X11)) != X11
        | k2_lattices(X10,esk1_2(X10,X11),X11) != X11
        | X11 = k5_lattices(X10)
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | ~ v13_lattices(X10)
        | v2_struct_0(X10)
        | ~ l1_lattices(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattices])])])])])])).

fof(c_0_52,plain,(
    ! [X16,X17,X18] :
      ( ( ~ r1_lattices(X16,X17,X18)
        | k2_lattices(X16,X17,X18) = X17
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | v2_struct_0(X16)
        | ~ v8_lattices(X16)
        | ~ v9_lattices(X16)
        | ~ l3_lattices(X16) )
      & ( k2_lattices(X16,X17,X18) != X17
        | r1_lattices(X16,X17,X18)
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | v2_struct_0(X16)
        | ~ v8_lattices(X16)
        | ~ v9_lattices(X16)
        | ~ l3_lattices(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t21_lattices])])])])])).

cnf(c_0_53,plain,
    ( r1_lattices(X1,k15_lattice3(X1,k1_xboole_0),X2)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v4_lattice3(X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ v10_lattices(X1)
    | ~ v10_lattices(X3)
    | ~ l3_lattices(X1)
    | ~ l3_lattices(X3) ),
    inference(spm,[status(thm)],[c_0_48,c_0_44])).

cnf(c_0_54,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_55,plain,
    ( l1_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

fof(c_0_56,plain,(
    ! [X9] :
      ( ( ~ v2_struct_0(X9)
        | v2_struct_0(X9)
        | ~ v10_lattices(X9)
        | ~ l3_lattices(X9) )
      & ( v4_lattices(X9)
        | v2_struct_0(X9)
        | ~ v10_lattices(X9)
        | ~ l3_lattices(X9) )
      & ( v5_lattices(X9)
        | v2_struct_0(X9)
        | ~ v10_lattices(X9)
        | ~ l3_lattices(X9) )
      & ( v6_lattices(X9)
        | v2_struct_0(X9)
        | ~ v10_lattices(X9)
        | ~ l3_lattices(X9) )
      & ( v7_lattices(X9)
        | v2_struct_0(X9)
        | ~ v10_lattices(X9)
        | ~ l3_lattices(X9) )
      & ( v8_lattices(X9)
        | v2_struct_0(X9)
        | ~ v10_lattices(X9)
        | ~ l3_lattices(X9) )
      & ( v9_lattices(X9)
        | v2_struct_0(X9)
        | ~ v10_lattices(X9)
        | ~ l3_lattices(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).

fof(c_0_57,plain,(
    ! [X30,X31,X32] :
      ( ( ~ v6_lattices(X30)
        | ~ m1_subset_1(X31,u1_struct_0(X30))
        | ~ m1_subset_1(X32,u1_struct_0(X30))
        | k2_lattices(X30,X31,X32) = k2_lattices(X30,X32,X31)
        | v2_struct_0(X30)
        | ~ l1_lattices(X30) )
      & ( m1_subset_1(esk5_1(X30),u1_struct_0(X30))
        | v6_lattices(X30)
        | v2_struct_0(X30)
        | ~ l1_lattices(X30) )
      & ( m1_subset_1(esk6_1(X30),u1_struct_0(X30))
        | v6_lattices(X30)
        | v2_struct_0(X30)
        | ~ l1_lattices(X30) )
      & ( k2_lattices(X30,esk5_1(X30),esk6_1(X30)) != k2_lattices(X30,esk6_1(X30),esk5_1(X30))
        | v6_lattices(X30)
        | v2_struct_0(X30)
        | ~ l1_lattices(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d6_lattices])])])])])])).

fof(c_0_58,negated_conjecture,(
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

cnf(c_0_59,plain,
    ( k2_lattices(X1,X2,X3) = X3
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | X3 != k5_lattices(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v13_lattices(X1)
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_60,plain,
    ( k2_lattices(X1,X2,X3) = X2
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_61,plain,
    ( r1_lattices(X1,k15_lattice3(X1,k1_xboole_0),k5_lattices(X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_lattice3(X1)
    | ~ v4_lattice3(X2)
    | ~ m1_subset_1(k5_lattices(X2),u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X1)
    | ~ l3_lattices(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55])).

cnf(c_0_62,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_63,plain,
    ( v9_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

fof(c_0_64,plain,(
    ! [X19,X21,X22] :
      ( ( m1_subset_1(esk2_1(X19),u1_struct_0(X19))
        | ~ v13_lattices(X19)
        | v2_struct_0(X19)
        | ~ l1_lattices(X19) )
      & ( k2_lattices(X19,esk2_1(X19),X21) = esk2_1(X19)
        | ~ m1_subset_1(X21,u1_struct_0(X19))
        | ~ v13_lattices(X19)
        | v2_struct_0(X19)
        | ~ l1_lattices(X19) )
      & ( k2_lattices(X19,X21,esk2_1(X19)) = esk2_1(X19)
        | ~ m1_subset_1(X21,u1_struct_0(X19))
        | ~ v13_lattices(X19)
        | v2_struct_0(X19)
        | ~ l1_lattices(X19) )
      & ( m1_subset_1(esk3_2(X19,X22),u1_struct_0(X19))
        | ~ m1_subset_1(X22,u1_struct_0(X19))
        | v13_lattices(X19)
        | v2_struct_0(X19)
        | ~ l1_lattices(X19) )
      & ( k2_lattices(X19,X22,esk3_2(X19,X22)) != X22
        | k2_lattices(X19,esk3_2(X19,X22),X22) != X22
        | ~ m1_subset_1(X22,u1_struct_0(X19))
        | v13_lattices(X19)
        | v2_struct_0(X19)
        | ~ l1_lattices(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d13_lattices])])])])])])).

cnf(c_0_65,plain,
    ( k2_lattices(X1,X2,X3) = k2_lattices(X1,X3,X2)
    | v2_struct_0(X1)
    | ~ v6_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_66,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

fof(c_0_67,negated_conjecture,
    ( ~ v2_struct_0(esk10_0)
    & v10_lattices(esk10_0)
    & v4_lattice3(esk10_0)
    & l3_lattices(esk10_0)
    & ( v2_struct_0(esk10_0)
      | ~ v10_lattices(esk10_0)
      | ~ v13_lattices(esk10_0)
      | ~ l3_lattices(esk10_0)
      | k5_lattices(esk10_0) != k15_lattice3(esk10_0,k1_xboole_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_58])])])])).

cnf(c_0_68,plain,
    ( k2_lattices(X1,X2,k5_lattices(X1)) = k5_lattices(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v13_lattices(X1)
    | ~ l1_lattices(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_59]),c_0_54])).

cnf(c_0_69,plain,
    ( k2_lattices(X1,k15_lattice3(X1,k1_xboole_0),k5_lattices(X2)) = k15_lattice3(X1,k1_xboole_0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v4_lattice3(X2)
    | ~ m1_subset_1(k5_lattices(X2),u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X1)
    | ~ l3_lattices(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_62]),c_0_63]),c_0_42])).

cnf(c_0_70,plain,
    ( v13_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,esk3_2(X1,X2)) != X2
    | k2_lattices(X1,esk3_2(X1,X2),X2) != X2
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_71,plain,
    ( k2_lattices(X1,X2,X3) = k2_lattices(X1,X3,X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_55])).

cnf(c_0_72,plain,
    ( k2_lattices(X1,X2,X3) = X2
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ r2_hidden(X3,a_2_4_lattice3(X1,X2)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_39]),c_0_62]),c_0_63]),c_0_33])).

cnf(c_0_73,negated_conjecture,
    ( v2_struct_0(esk10_0)
    | ~ v10_lattices(esk10_0)
    | ~ v13_lattices(esk10_0)
    | ~ l3_lattices(esk10_0)
    | k5_lattices(esk10_0) != k15_lattice3(esk10_0,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_74,negated_conjecture,
    ( l3_lattices(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_75,negated_conjecture,
    ( v10_lattices(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_76,negated_conjecture,
    ( ~ v2_struct_0(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_77,plain,
    ( k15_lattice3(X1,k1_xboole_0) = k5_lattices(X1)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
    | ~ v13_lattices(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_55]),c_0_42])).

cnf(c_0_78,plain,
    ( v13_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,esk3_2(X1,X2)) != X2
    | ~ m1_subset_1(esk3_2(X1,X2),u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_55])).

cnf(c_0_79,plain,
    ( k2_lattices(X1,k15_lattice3(X1,k1_xboole_0),X2) = k15_lattice3(X1,k1_xboole_0)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_44]),c_0_42])).

cnf(c_0_80,negated_conjecture,
    ( k5_lattices(esk10_0) != k15_lattice3(esk10_0,k1_xboole_0)
    | ~ v13_lattices(esk10_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_74]),c_0_75])]),c_0_76])).

cnf(c_0_81,plain,
    ( k15_lattice3(X1,k1_xboole_0) = k5_lattices(X1)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v13_lattices(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_54]),c_0_55])).

cnf(c_0_82,negated_conjecture,
    ( v4_lattice3(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_83,plain,
    ( v13_lattices(X1)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(esk3_2(X1,k15_lattice3(X1,k1_xboole_0)),u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_42])).

cnf(c_0_84,plain,
    ( m1_subset_1(esk3_2(X1,X2),u1_struct_0(X1))
    | v13_lattices(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_85,negated_conjecture,
    ( ~ v13_lattices(esk10_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_82]),c_0_75]),c_0_74])]),c_0_76])).

cnf(c_0_86,plain,
    ( v13_lattices(X1)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_55]),c_0_42])).

cnf(c_0_87,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_82]),c_0_75]),c_0_74])]),c_0_76]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:36:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.45  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 0.19/0.45  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.45  #
% 0.19/0.45  # Preprocessing time       : 0.054 s
% 0.19/0.45  # Presaturation interreduction done
% 0.19/0.45  
% 0.19/0.45  # Proof found!
% 0.19/0.45  # SZS status Theorem
% 0.19/0.45  # SZS output start CNFRefutation
% 0.19/0.45  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.19/0.45  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.19/0.45  fof(t34_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(X2=k16_lattice3(X1,X3)<=>(r3_lattice3(X1,X2,X3)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r3_lattice3(X1,X4,X3)=>r3_lattices(X1,X4,X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_lattice3)).
% 0.19/0.45  fof(t45_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(X2=k15_lattice3(X1,a_2_3_lattice3(X1,X2))&X2=k16_lattice3(X1,a_2_4_lattice3(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_lattice3)).
% 0.19/0.45  fof(fraenkel_a_2_4_lattice3, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X2))&v10_lattices(X2))&v4_lattice3(X2))&l3_lattices(X2))&m1_subset_1(X3,u1_struct_0(X2)))=>(r2_hidden(X1,a_2_4_lattice3(X2,X3))<=>?[X4]:((m1_subset_1(X4,u1_struct_0(X2))&X1=X4)&r3_lattices(X2,X3,X4)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_4_lattice3)).
% 0.19/0.45  fof(t48_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2, X3]:(![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>~((r2_hidden(X4,X2)&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>~((r3_lattices(X1,X4,X5)&r2_hidden(X5,X3)))))))=>r3_lattices(X1,k15_lattice3(X1,X2),k15_lattice3(X1,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_lattice3)).
% 0.19/0.45  fof(d16_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(r3_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X3)=>r1_lattices(X1,X2,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_lattice3)).
% 0.19/0.45  fof(dt_k15_lattice3, axiom, ![X1, X2]:((~(v2_struct_0(X1))&l3_lattices(X1))=>m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k15_lattice3)).
% 0.19/0.45  fof(dt_k5_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>m1_subset_1(k5_lattices(X1),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_lattices)).
% 0.19/0.45  fof(dt_l3_lattices, axiom, ![X1]:(l3_lattices(X1)=>(l1_lattices(X1)&l2_lattices(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l3_lattices)).
% 0.19/0.45  fof(d16_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>(v13_lattices(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(X2=k5_lattices(X1)<=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(k2_lattices(X1,X2,X3)=X2&k2_lattices(X1,X3,X2)=X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_lattices)).
% 0.19/0.45  fof(t21_lattices, axiom, ![X1]:((((~(v2_struct_0(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_lattices(X1,X2,X3)<=>k2_lattices(X1,X2,X3)=X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_lattices)).
% 0.19/0.45  fof(cc1_lattices, axiom, ![X1]:(l3_lattices(X1)=>((~(v2_struct_0(X1))&v10_lattices(X1))=>((((((~(v2_struct_0(X1))&v4_lattices(X1))&v5_lattices(X1))&v6_lattices(X1))&v7_lattices(X1))&v8_lattices(X1))&v9_lattices(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattices)).
% 0.19/0.45  fof(d6_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>(v6_lattices(X1)<=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>k2_lattices(X1,X2,X3)=k2_lattices(X1,X3,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_lattices)).
% 0.19/0.45  fof(t50_lattice3, conjecture, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>((((~(v2_struct_0(X1))&v10_lattices(X1))&v13_lattices(X1))&l3_lattices(X1))&k5_lattices(X1)=k15_lattice3(X1,k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_lattice3)).
% 0.19/0.45  fof(d13_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>(v13_lattices(X1)<=>?[X2]:(m1_subset_1(X2,u1_struct_0(X1))&![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(k2_lattices(X1,X2,X3)=X2&k2_lattices(X1,X3,X2)=X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_lattices)).
% 0.19/0.45  fof(c_0_16, plain, ![X7, X8]:(~r2_hidden(X7,X8)|~r1_tarski(X8,X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.19/0.45  fof(c_0_17, plain, ![X6]:r1_tarski(k1_xboole_0,X6), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.19/0.45  fof(c_0_18, plain, ![X44, X45, X46, X47, X48]:(((r3_lattice3(X44,X45,X46)|X45!=k16_lattice3(X44,X46)|~m1_subset_1(X45,u1_struct_0(X44))|(v2_struct_0(X44)|~v10_lattices(X44)|~v4_lattice3(X44)|~l3_lattices(X44)))&(~m1_subset_1(X47,u1_struct_0(X44))|(~r3_lattice3(X44,X47,X46)|r3_lattices(X44,X47,X45))|X45!=k16_lattice3(X44,X46)|~m1_subset_1(X45,u1_struct_0(X44))|(v2_struct_0(X44)|~v10_lattices(X44)|~v4_lattice3(X44)|~l3_lattices(X44))))&((m1_subset_1(esk8_3(X44,X45,X48),u1_struct_0(X44))|~r3_lattice3(X44,X45,X48)|X45=k16_lattice3(X44,X48)|~m1_subset_1(X45,u1_struct_0(X44))|(v2_struct_0(X44)|~v10_lattices(X44)|~v4_lattice3(X44)|~l3_lattices(X44)))&((r3_lattice3(X44,esk8_3(X44,X45,X48),X48)|~r3_lattice3(X44,X45,X48)|X45=k16_lattice3(X44,X48)|~m1_subset_1(X45,u1_struct_0(X44))|(v2_struct_0(X44)|~v10_lattices(X44)|~v4_lattice3(X44)|~l3_lattices(X44)))&(~r3_lattices(X44,esk8_3(X44,X45,X48),X45)|~r3_lattice3(X44,X45,X48)|X45=k16_lattice3(X44,X48)|~m1_subset_1(X45,u1_struct_0(X44))|(v2_struct_0(X44)|~v10_lattices(X44)|~v4_lattice3(X44)|~l3_lattices(X44)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_lattice3])])])])])])])).
% 0.19/0.45  fof(c_0_19, plain, ![X50, X51]:((X51=k15_lattice3(X50,a_2_3_lattice3(X50,X51))|~m1_subset_1(X51,u1_struct_0(X50))|(v2_struct_0(X50)|~v10_lattices(X50)|~v4_lattice3(X50)|~l3_lattices(X50)))&(X51=k16_lattice3(X50,a_2_4_lattice3(X50,X51))|~m1_subset_1(X51,u1_struct_0(X50))|(v2_struct_0(X50)|~v10_lattices(X50)|~v4_lattice3(X50)|~l3_lattices(X50)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t45_lattice3])])])])])).
% 0.19/0.45  fof(c_0_20, plain, ![X39, X40, X41, X43]:((((m1_subset_1(esk7_3(X39,X40,X41),u1_struct_0(X40))|~r2_hidden(X39,a_2_4_lattice3(X40,X41))|(v2_struct_0(X40)|~v10_lattices(X40)|~v4_lattice3(X40)|~l3_lattices(X40)|~m1_subset_1(X41,u1_struct_0(X40))))&(X39=esk7_3(X39,X40,X41)|~r2_hidden(X39,a_2_4_lattice3(X40,X41))|(v2_struct_0(X40)|~v10_lattices(X40)|~v4_lattice3(X40)|~l3_lattices(X40)|~m1_subset_1(X41,u1_struct_0(X40)))))&(r3_lattices(X40,X41,esk7_3(X39,X40,X41))|~r2_hidden(X39,a_2_4_lattice3(X40,X41))|(v2_struct_0(X40)|~v10_lattices(X40)|~v4_lattice3(X40)|~l3_lattices(X40)|~m1_subset_1(X41,u1_struct_0(X40)))))&(~m1_subset_1(X43,u1_struct_0(X40))|X39!=X43|~r3_lattices(X40,X41,X43)|r2_hidden(X39,a_2_4_lattice3(X40,X41))|(v2_struct_0(X40)|~v10_lattices(X40)|~v4_lattice3(X40)|~l3_lattices(X40)|~m1_subset_1(X41,u1_struct_0(X40))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_4_lattice3])])])])])])).
% 0.19/0.45  cnf(c_0_21, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.45  cnf(c_0_22, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.45  fof(c_0_23, plain, ![X52, X53, X54, X56]:((m1_subset_1(esk9_3(X52,X53,X54),u1_struct_0(X52))|r3_lattices(X52,k15_lattice3(X52,X53),k15_lattice3(X52,X54))|(v2_struct_0(X52)|~v10_lattices(X52)|~v4_lattice3(X52)|~l3_lattices(X52)))&((r2_hidden(esk9_3(X52,X53,X54),X53)|r3_lattices(X52,k15_lattice3(X52,X53),k15_lattice3(X52,X54))|(v2_struct_0(X52)|~v10_lattices(X52)|~v4_lattice3(X52)|~l3_lattices(X52)))&(~m1_subset_1(X56,u1_struct_0(X52))|(~r3_lattices(X52,esk9_3(X52,X53,X54),X56)|~r2_hidden(X56,X54))|r3_lattices(X52,k15_lattice3(X52,X53),k15_lattice3(X52,X54))|(v2_struct_0(X52)|~v10_lattices(X52)|~v4_lattice3(X52)|~l3_lattices(X52))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t48_lattice3])])])])])])).
% 0.19/0.45  fof(c_0_24, plain, ![X24, X25, X26, X27, X28]:((~r3_lattice3(X24,X25,X26)|(~m1_subset_1(X27,u1_struct_0(X24))|(~r2_hidden(X27,X26)|r1_lattices(X24,X25,X27)))|~m1_subset_1(X25,u1_struct_0(X24))|(v2_struct_0(X24)|~l3_lattices(X24)))&((m1_subset_1(esk4_3(X24,X25,X28),u1_struct_0(X24))|r3_lattice3(X24,X25,X28)|~m1_subset_1(X25,u1_struct_0(X24))|(v2_struct_0(X24)|~l3_lattices(X24)))&((r2_hidden(esk4_3(X24,X25,X28),X28)|r3_lattice3(X24,X25,X28)|~m1_subset_1(X25,u1_struct_0(X24))|(v2_struct_0(X24)|~l3_lattices(X24)))&(~r1_lattices(X24,X25,esk4_3(X24,X25,X28))|r3_lattice3(X24,X25,X28)|~m1_subset_1(X25,u1_struct_0(X24))|(v2_struct_0(X24)|~l3_lattices(X24)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattice3])])])])])])])).
% 0.19/0.45  cnf(c_0_25, plain, (r3_lattice3(X1,X2,X3)|v2_struct_0(X1)|X2!=k16_lattice3(X1,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.45  cnf(c_0_26, plain, (X1=k16_lattice3(X2,a_2_4_lattice3(X2,X1))|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.45  cnf(c_0_27, plain, (m1_subset_1(esk7_3(X1,X2,X3),u1_struct_0(X2))|v2_struct_0(X2)|~r2_hidden(X1,a_2_4_lattice3(X2,X3))|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)|~m1_subset_1(X3,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.45  cnf(c_0_28, plain, (X1=esk7_3(X1,X2,X3)|v2_struct_0(X2)|~r2_hidden(X1,a_2_4_lattice3(X2,X3))|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)|~m1_subset_1(X3,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.45  cnf(c_0_29, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.19/0.45  cnf(c_0_30, plain, (r2_hidden(esk9_3(X1,X2,X3),X2)|r3_lattices(X1,k15_lattice3(X1,X2),k15_lattice3(X1,X3))|v2_struct_0(X1)|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.45  cnf(c_0_31, plain, (r1_lattices(X1,X2,X4)|v2_struct_0(X1)|~r3_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X4,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.45  cnf(c_0_32, plain, (r3_lattice3(X1,X2,a_2_4_lattice3(X1,X2))|v2_struct_0(X1)|~v4_lattice3(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26])])).
% 0.19/0.45  cnf(c_0_33, plain, (m1_subset_1(X1,u1_struct_0(X2))|v2_struct_0(X2)|~v4_lattice3(X2)|~m1_subset_1(X3,u1_struct_0(X2))|~v10_lattices(X2)|~l3_lattices(X2)|~r2_hidden(X1,a_2_4_lattice3(X2,X3))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.19/0.45  cnf(c_0_34, plain, (r2_hidden(X3,a_2_4_lattice3(X2,X4))|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|X3!=X1|~r3_lattices(X2,X4,X1)|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)|~m1_subset_1(X4,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.45  cnf(c_0_35, plain, (r3_lattices(X1,k15_lattice3(X1,k1_xboole_0),k15_lattice3(X1,X2))|v2_struct_0(X1)|~v4_lattice3(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.19/0.45  cnf(c_0_36, plain, (X1=k15_lattice3(X2,a_2_3_lattice3(X2,X1))|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.45  fof(c_0_37, plain, ![X35, X36]:(v2_struct_0(X35)|~l3_lattices(X35)|m1_subset_1(k15_lattice3(X35,X36),u1_struct_0(X35))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k15_lattice3])])])).
% 0.19/0.45  cnf(c_0_38, plain, (r3_lattice3(X1,X2,X3)|v2_struct_0(X1)|~r1_lattices(X1,X2,esk4_3(X1,X2,X3))|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.45  cnf(c_0_39, plain, (r1_lattices(X1,X2,X3)|v2_struct_0(X1)|~v4_lattice3(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)|~r2_hidden(X3,a_2_4_lattice3(X1,X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33])).
% 0.19/0.45  cnf(c_0_40, plain, (v2_struct_0(X1)|r2_hidden(X2,a_2_4_lattice3(X1,X3))|~r3_lattices(X1,X3,X2)|~v4_lattice3(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(er,[status(thm)],[c_0_34])).
% 0.19/0.45  cnf(c_0_41, plain, (r3_lattices(X1,k15_lattice3(X1,k1_xboole_0),X2)|v2_struct_0(X1)|~v4_lattice3(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.19/0.45  cnf(c_0_42, plain, (v2_struct_0(X1)|m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.45  cnf(c_0_43, plain, (r3_lattice3(X1,X2,X3)|v2_struct_0(X1)|~v4_lattice3(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)|~r2_hidden(esk4_3(X1,X2,X3),a_2_4_lattice3(X1,X2))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.19/0.45  cnf(c_0_44, plain, (v2_struct_0(X1)|r2_hidden(X2,a_2_4_lattice3(X1,k15_lattice3(X1,k1_xboole_0)))|~v4_lattice3(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42])).
% 0.19/0.45  cnf(c_0_45, plain, (r3_lattice3(X1,k15_lattice3(X1,k1_xboole_0),X2)|v2_struct_0(X1)|~v4_lattice3(X1)|~m1_subset_1(esk4_3(X1,k15_lattice3(X1,k1_xboole_0),X2),u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_42])).
% 0.19/0.45  cnf(c_0_46, plain, (m1_subset_1(esk4_3(X1,X2,X3),u1_struct_0(X1))|r3_lattice3(X1,X2,X3)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.45  cnf(c_0_47, plain, (r3_lattice3(X1,k15_lattice3(X1,k1_xboole_0),X2)|v2_struct_0(X1)|~v4_lattice3(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_42])).
% 0.19/0.45  cnf(c_0_48, plain, (r1_lattices(X1,k15_lattice3(X1,k1_xboole_0),X2)|v2_struct_0(X1)|~v4_lattice3(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)|~r2_hidden(X2,X3)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_47]), c_0_42])).
% 0.19/0.45  fof(c_0_49, plain, ![X14]:(v2_struct_0(X14)|~l1_lattices(X14)|m1_subset_1(k5_lattices(X14),u1_struct_0(X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_lattices])])])).
% 0.19/0.45  fof(c_0_50, plain, ![X15]:((l1_lattices(X15)|~l3_lattices(X15))&(l2_lattices(X15)|~l3_lattices(X15))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).
% 0.19/0.45  fof(c_0_51, plain, ![X10, X11, X12]:(((k2_lattices(X10,X11,X12)=X11|~m1_subset_1(X12,u1_struct_0(X10))|X11!=k5_lattices(X10)|~m1_subset_1(X11,u1_struct_0(X10))|~v13_lattices(X10)|(v2_struct_0(X10)|~l1_lattices(X10)))&(k2_lattices(X10,X12,X11)=X11|~m1_subset_1(X12,u1_struct_0(X10))|X11!=k5_lattices(X10)|~m1_subset_1(X11,u1_struct_0(X10))|~v13_lattices(X10)|(v2_struct_0(X10)|~l1_lattices(X10))))&((m1_subset_1(esk1_2(X10,X11),u1_struct_0(X10))|X11=k5_lattices(X10)|~m1_subset_1(X11,u1_struct_0(X10))|~v13_lattices(X10)|(v2_struct_0(X10)|~l1_lattices(X10)))&(k2_lattices(X10,X11,esk1_2(X10,X11))!=X11|k2_lattices(X10,esk1_2(X10,X11),X11)!=X11|X11=k5_lattices(X10)|~m1_subset_1(X11,u1_struct_0(X10))|~v13_lattices(X10)|(v2_struct_0(X10)|~l1_lattices(X10))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattices])])])])])])).
% 0.19/0.45  fof(c_0_52, plain, ![X16, X17, X18]:((~r1_lattices(X16,X17,X18)|k2_lattices(X16,X17,X18)=X17|~m1_subset_1(X18,u1_struct_0(X16))|~m1_subset_1(X17,u1_struct_0(X16))|(v2_struct_0(X16)|~v8_lattices(X16)|~v9_lattices(X16)|~l3_lattices(X16)))&(k2_lattices(X16,X17,X18)!=X17|r1_lattices(X16,X17,X18)|~m1_subset_1(X18,u1_struct_0(X16))|~m1_subset_1(X17,u1_struct_0(X16))|(v2_struct_0(X16)|~v8_lattices(X16)|~v9_lattices(X16)|~l3_lattices(X16)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t21_lattices])])])])])).
% 0.19/0.45  cnf(c_0_53, plain, (r1_lattices(X1,k15_lattice3(X1,k1_xboole_0),X2)|v2_struct_0(X3)|v2_struct_0(X1)|~v4_lattice3(X1)|~v4_lattice3(X3)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X3))|~v10_lattices(X1)|~v10_lattices(X3)|~l3_lattices(X1)|~l3_lattices(X3)), inference(spm,[status(thm)],[c_0_48, c_0_44])).
% 0.19/0.45  cnf(c_0_54, plain, (v2_struct_0(X1)|m1_subset_1(k5_lattices(X1),u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.19/0.45  cnf(c_0_55, plain, (l1_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.19/0.45  fof(c_0_56, plain, ![X9]:(((((((~v2_struct_0(X9)|(v2_struct_0(X9)|~v10_lattices(X9))|~l3_lattices(X9))&(v4_lattices(X9)|(v2_struct_0(X9)|~v10_lattices(X9))|~l3_lattices(X9)))&(v5_lattices(X9)|(v2_struct_0(X9)|~v10_lattices(X9))|~l3_lattices(X9)))&(v6_lattices(X9)|(v2_struct_0(X9)|~v10_lattices(X9))|~l3_lattices(X9)))&(v7_lattices(X9)|(v2_struct_0(X9)|~v10_lattices(X9))|~l3_lattices(X9)))&(v8_lattices(X9)|(v2_struct_0(X9)|~v10_lattices(X9))|~l3_lattices(X9)))&(v9_lattices(X9)|(v2_struct_0(X9)|~v10_lattices(X9))|~l3_lattices(X9))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).
% 0.19/0.45  fof(c_0_57, plain, ![X30, X31, X32]:((~v6_lattices(X30)|(~m1_subset_1(X31,u1_struct_0(X30))|(~m1_subset_1(X32,u1_struct_0(X30))|k2_lattices(X30,X31,X32)=k2_lattices(X30,X32,X31)))|(v2_struct_0(X30)|~l1_lattices(X30)))&((m1_subset_1(esk5_1(X30),u1_struct_0(X30))|v6_lattices(X30)|(v2_struct_0(X30)|~l1_lattices(X30)))&((m1_subset_1(esk6_1(X30),u1_struct_0(X30))|v6_lattices(X30)|(v2_struct_0(X30)|~l1_lattices(X30)))&(k2_lattices(X30,esk5_1(X30),esk6_1(X30))!=k2_lattices(X30,esk6_1(X30),esk5_1(X30))|v6_lattices(X30)|(v2_struct_0(X30)|~l1_lattices(X30)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d6_lattices])])])])])])).
% 0.19/0.45  fof(c_0_58, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>((((~(v2_struct_0(X1))&v10_lattices(X1))&v13_lattices(X1))&l3_lattices(X1))&k5_lattices(X1)=k15_lattice3(X1,k1_xboole_0)))), inference(assume_negation,[status(cth)],[t50_lattice3])).
% 0.19/0.45  cnf(c_0_59, plain, (k2_lattices(X1,X2,X3)=X3|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|X3!=k5_lattices(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~v13_lattices(X1)|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.19/0.45  cnf(c_0_60, plain, (k2_lattices(X1,X2,X3)=X2|v2_struct_0(X1)|~r1_lattices(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.19/0.45  cnf(c_0_61, plain, (r1_lattices(X1,k15_lattice3(X1,k1_xboole_0),k5_lattices(X2))|v2_struct_0(X1)|v2_struct_0(X2)|~v4_lattice3(X1)|~v4_lattice3(X2)|~m1_subset_1(k5_lattices(X2),u1_struct_0(X1))|~v10_lattices(X1)|~v10_lattices(X2)|~l3_lattices(X1)|~l3_lattices(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55])).
% 0.19/0.45  cnf(c_0_62, plain, (v8_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.19/0.45  cnf(c_0_63, plain, (v9_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.19/0.45  fof(c_0_64, plain, ![X19, X21, X22]:(((m1_subset_1(esk2_1(X19),u1_struct_0(X19))|~v13_lattices(X19)|(v2_struct_0(X19)|~l1_lattices(X19)))&((k2_lattices(X19,esk2_1(X19),X21)=esk2_1(X19)|~m1_subset_1(X21,u1_struct_0(X19))|~v13_lattices(X19)|(v2_struct_0(X19)|~l1_lattices(X19)))&(k2_lattices(X19,X21,esk2_1(X19))=esk2_1(X19)|~m1_subset_1(X21,u1_struct_0(X19))|~v13_lattices(X19)|(v2_struct_0(X19)|~l1_lattices(X19)))))&((m1_subset_1(esk3_2(X19,X22),u1_struct_0(X19))|~m1_subset_1(X22,u1_struct_0(X19))|v13_lattices(X19)|(v2_struct_0(X19)|~l1_lattices(X19)))&(k2_lattices(X19,X22,esk3_2(X19,X22))!=X22|k2_lattices(X19,esk3_2(X19,X22),X22)!=X22|~m1_subset_1(X22,u1_struct_0(X19))|v13_lattices(X19)|(v2_struct_0(X19)|~l1_lattices(X19))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d13_lattices])])])])])])).
% 0.19/0.45  cnf(c_0_65, plain, (k2_lattices(X1,X2,X3)=k2_lattices(X1,X3,X2)|v2_struct_0(X1)|~v6_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.19/0.45  cnf(c_0_66, plain, (v6_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.19/0.45  fof(c_0_67, negated_conjecture, ((((~v2_struct_0(esk10_0)&v10_lattices(esk10_0))&v4_lattice3(esk10_0))&l3_lattices(esk10_0))&(v2_struct_0(esk10_0)|~v10_lattices(esk10_0)|~v13_lattices(esk10_0)|~l3_lattices(esk10_0)|k5_lattices(esk10_0)!=k15_lattice3(esk10_0,k1_xboole_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_58])])])])).
% 0.19/0.45  cnf(c_0_68, plain, (k2_lattices(X1,X2,k5_lattices(X1))=k5_lattices(X1)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v13_lattices(X1)|~l1_lattices(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_59]), c_0_54])).
% 0.19/0.45  cnf(c_0_69, plain, (k2_lattices(X1,k15_lattice3(X1,k1_xboole_0),k5_lattices(X2))=k15_lattice3(X1,k1_xboole_0)|v2_struct_0(X2)|v2_struct_0(X1)|~v4_lattice3(X1)|~v4_lattice3(X2)|~m1_subset_1(k5_lattices(X2),u1_struct_0(X1))|~v10_lattices(X1)|~v10_lattices(X2)|~l3_lattices(X1)|~l3_lattices(X2)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_62]), c_0_63]), c_0_42])).
% 0.19/0.45  cnf(c_0_70, plain, (v13_lattices(X1)|v2_struct_0(X1)|k2_lattices(X1,X2,esk3_2(X1,X2))!=X2|k2_lattices(X1,esk3_2(X1,X2),X2)!=X2|~m1_subset_1(X2,u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.19/0.45  cnf(c_0_71, plain, (k2_lattices(X1,X2,X3)=k2_lattices(X1,X3,X2)|v2_struct_0(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_55])).
% 0.19/0.45  cnf(c_0_72, plain, (k2_lattices(X1,X2,X3)=X2|v2_struct_0(X1)|~v4_lattice3(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)|~r2_hidden(X3,a_2_4_lattice3(X1,X2))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_39]), c_0_62]), c_0_63]), c_0_33])).
% 0.19/0.45  cnf(c_0_73, negated_conjecture, (v2_struct_0(esk10_0)|~v10_lattices(esk10_0)|~v13_lattices(esk10_0)|~l3_lattices(esk10_0)|k5_lattices(esk10_0)!=k15_lattice3(esk10_0,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.19/0.45  cnf(c_0_74, negated_conjecture, (l3_lattices(esk10_0)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.19/0.45  cnf(c_0_75, negated_conjecture, (v10_lattices(esk10_0)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.19/0.45  cnf(c_0_76, negated_conjecture, (~v2_struct_0(esk10_0)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.19/0.45  cnf(c_0_77, plain, (k15_lattice3(X1,k1_xboole_0)=k5_lattices(X1)|v2_struct_0(X1)|~v4_lattice3(X1)|~m1_subset_1(k5_lattices(X1),u1_struct_0(X1))|~v13_lattices(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_55]), c_0_42])).
% 0.19/0.45  cnf(c_0_78, plain, (v13_lattices(X1)|v2_struct_0(X1)|k2_lattices(X1,X2,esk3_2(X1,X2))!=X2|~m1_subset_1(esk3_2(X1,X2),u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_55])).
% 0.19/0.45  cnf(c_0_79, plain, (k2_lattices(X1,k15_lattice3(X1,k1_xboole_0),X2)=k15_lattice3(X1,k1_xboole_0)|v2_struct_0(X1)|~v4_lattice3(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_44]), c_0_42])).
% 0.19/0.45  cnf(c_0_80, negated_conjecture, (k5_lattices(esk10_0)!=k15_lattice3(esk10_0,k1_xboole_0)|~v13_lattices(esk10_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73, c_0_74]), c_0_75])]), c_0_76])).
% 0.19/0.45  cnf(c_0_81, plain, (k15_lattice3(X1,k1_xboole_0)=k5_lattices(X1)|v2_struct_0(X1)|~v4_lattice3(X1)|~v13_lattices(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_54]), c_0_55])).
% 0.19/0.45  cnf(c_0_82, negated_conjecture, (v4_lattice3(esk10_0)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.19/0.45  cnf(c_0_83, plain, (v13_lattices(X1)|v2_struct_0(X1)|~v4_lattice3(X1)|~m1_subset_1(esk3_2(X1,k15_lattice3(X1,k1_xboole_0)),u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_42])).
% 0.19/0.45  cnf(c_0_84, plain, (m1_subset_1(esk3_2(X1,X2),u1_struct_0(X1))|v13_lattices(X1)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.19/0.45  cnf(c_0_85, negated_conjecture, (~v13_lattices(esk10_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_82]), c_0_75]), c_0_74])]), c_0_76])).
% 0.19/0.45  cnf(c_0_86, plain, (v13_lattices(X1)|v2_struct_0(X1)|~v4_lattice3(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_55]), c_0_42])).
% 0.19/0.45  cnf(c_0_87, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_82]), c_0_75]), c_0_74])]), c_0_76]), ['proof']).
% 0.19/0.45  # SZS output end CNFRefutation
% 0.19/0.45  # Proof object total steps             : 88
% 0.19/0.45  # Proof object clause steps            : 55
% 0.19/0.45  # Proof object formula steps           : 33
% 0.19/0.45  # Proof object conjectures             : 11
% 0.19/0.45  # Proof object clause conjectures      : 8
% 0.19/0.45  # Proof object formula conjectures     : 3
% 0.19/0.45  # Proof object initial clauses used    : 28
% 0.19/0.45  # Proof object initial formulas used   : 16
% 0.19/0.45  # Proof object generating inferences   : 25
% 0.19/0.45  # Proof object simplifying inferences  : 38
% 0.19/0.45  # Training examples: 0 positive, 0 negative
% 0.19/0.45  # Parsed axioms                        : 17
% 0.19/0.45  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.45  # Initial clauses                      : 52
% 0.19/0.45  # Removed in clause preprocessing      : 1
% 0.19/0.45  # Initial clauses in saturation        : 51
% 0.19/0.45  # Processed clauses                    : 326
% 0.19/0.45  # ...of these trivial                  : 0
% 0.19/0.45  # ...subsumed                          : 123
% 0.19/0.45  # ...remaining for further processing  : 203
% 0.19/0.45  # Other redundant clauses eliminated   : 4
% 0.19/0.45  # Clauses deleted for lack of memory   : 0
% 0.19/0.45  # Backward-subsumed                    : 13
% 0.19/0.45  # Backward-rewritten                   : 0
% 0.19/0.45  # Generated clauses                    : 390
% 0.19/0.45  # ...of the previous two non-trivial   : 369
% 0.19/0.45  # Contextual simplify-reflections      : 57
% 0.19/0.45  # Paramodulations                      : 377
% 0.19/0.45  # Factorizations                       : 0
% 0.19/0.45  # Equation resolutions                 : 13
% 0.19/0.45  # Propositional unsat checks           : 0
% 0.19/0.45  #    Propositional check models        : 0
% 0.19/0.45  #    Propositional check unsatisfiable : 0
% 0.19/0.45  #    Propositional clauses             : 0
% 0.19/0.45  #    Propositional clauses after purity: 0
% 0.19/0.45  #    Propositional unsat core size     : 0
% 0.19/0.45  #    Propositional preprocessing time  : 0.000
% 0.19/0.45  #    Propositional encoding time       : 0.000
% 0.19/0.45  #    Propositional solver time         : 0.000
% 0.19/0.45  #    Success case prop preproc time    : 0.000
% 0.19/0.45  #    Success case prop encoding time   : 0.000
% 0.19/0.45  #    Success case prop solver time     : 0.000
% 0.19/0.45  # Current number of processed clauses  : 138
% 0.19/0.45  #    Positive orientable unit clauses  : 4
% 0.19/0.45  #    Positive unorientable unit clauses: 0
% 0.19/0.45  #    Negative unit clauses             : 3
% 0.19/0.45  #    Non-unit-clauses                  : 131
% 0.19/0.45  # Current number of unprocessed clauses: 137
% 0.19/0.45  # ...number of literals in the above   : 1575
% 0.19/0.45  # Current number of archived formulas  : 0
% 0.19/0.45  # Current number of archived clauses   : 64
% 0.19/0.45  # Clause-clause subsumption calls (NU) : 17083
% 0.19/0.45  # Rec. Clause-clause subsumption calls : 345
% 0.19/0.45  # Non-unit clause-clause subsumptions  : 192
% 0.19/0.45  # Unit Clause-clause subsumption calls : 21
% 0.19/0.45  # Rewrite failures with RHS unbound    : 0
% 0.19/0.45  # BW rewrite match attempts            : 0
% 0.19/0.45  # BW rewrite match successes           : 0
% 0.19/0.45  # Condensation attempts                : 0
% 0.19/0.45  # Condensation successes               : 0
% 0.19/0.45  # Termbank termtop insertions          : 20557
% 0.19/0.45  
% 0.19/0.45  # -------------------------------------------------
% 0.19/0.45  # User time                : 0.106 s
% 0.19/0.45  # System time              : 0.005 s
% 0.19/0.45  # Total time               : 0.111 s
% 0.19/0.45  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
