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
% DateTime   : Thu Dec  3 11:15:07 EST 2020

% Result     : Theorem 0.78s
% Output     : CNFRefutation 0.78s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 676 expanded)
%              Number of clauses        :   74 ( 302 expanded)
%              Number of leaves         :   20 ( 181 expanded)
%              Depth                    :   23
%              Number of atoms          :  912 (6258 expanded)
%              Number of equality atoms :   98 ( 519 expanded)
%              Maximal formula depth    :   22 (   8 average)
%              Maximal clause size      :   50 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(t46_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v4_lattice3(X1)
        & l3_lattices(X1) )
     => ! [X2,X3] :
          ( r1_tarski(X2,X3)
         => ( r3_lattices(X1,k15_lattice3(X1,X2),k15_lattice3(X1,X3))
            & r3_lattices(X1,k16_lattice3(X1,X3),k16_lattice3(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_lattice3)).

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

fof(dt_k15_lattice3,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k15_lattice3)).

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

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(dt_l3_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( l1_lattices(X1)
        & l2_lattices(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

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

fof(t37_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v4_lattice3(X1)
        & l3_lattices(X1) )
     => ! [X2] : k15_lattice3(X1,X2) = k16_lattice3(X1,a_2_2_lattice3(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_lattice3)).

fof(c_0_20,plain,(
    ! [X22,X23,X24,X25,X26] :
      ( ( ~ r3_lattice3(X22,X23,X24)
        | ~ m1_subset_1(X25,u1_struct_0(X22))
        | ~ r2_hidden(X25,X24)
        | r1_lattices(X22,X23,X25)
        | ~ m1_subset_1(X23,u1_struct_0(X22))
        | v2_struct_0(X22)
        | ~ l3_lattices(X22) )
      & ( m1_subset_1(esk4_3(X22,X23,X26),u1_struct_0(X22))
        | r3_lattice3(X22,X23,X26)
        | ~ m1_subset_1(X23,u1_struct_0(X22))
        | v2_struct_0(X22)
        | ~ l3_lattices(X22) )
      & ( r2_hidden(esk4_3(X22,X23,X26),X26)
        | r3_lattice3(X22,X23,X26)
        | ~ m1_subset_1(X23,u1_struct_0(X22))
        | v2_struct_0(X22)
        | ~ l3_lattices(X22) )
      & ( ~ r1_lattices(X22,X23,esk4_3(X22,X23,X26))
        | r3_lattice3(X22,X23,X26)
        | ~ m1_subset_1(X23,u1_struct_0(X22))
        | v2_struct_0(X22)
        | ~ l3_lattices(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattice3])])])])])])])).

fof(c_0_21,plain,(
    ! [X56,X57,X58,X59,X60] :
      ( ( r3_lattice3(X56,X57,X58)
        | X57 != k16_lattice3(X56,X58)
        | ~ m1_subset_1(X57,u1_struct_0(X56))
        | v2_struct_0(X56)
        | ~ v10_lattices(X56)
        | ~ v4_lattice3(X56)
        | ~ l3_lattices(X56) )
      & ( ~ m1_subset_1(X59,u1_struct_0(X56))
        | ~ r3_lattice3(X56,X59,X58)
        | r3_lattices(X56,X59,X57)
        | X57 != k16_lattice3(X56,X58)
        | ~ m1_subset_1(X57,u1_struct_0(X56))
        | v2_struct_0(X56)
        | ~ v10_lattices(X56)
        | ~ v4_lattice3(X56)
        | ~ l3_lattices(X56) )
      & ( m1_subset_1(esk11_3(X56,X57,X60),u1_struct_0(X56))
        | ~ r3_lattice3(X56,X57,X60)
        | X57 = k16_lattice3(X56,X60)
        | ~ m1_subset_1(X57,u1_struct_0(X56))
        | v2_struct_0(X56)
        | ~ v10_lattices(X56)
        | ~ v4_lattice3(X56)
        | ~ l3_lattices(X56) )
      & ( r3_lattice3(X56,esk11_3(X56,X57,X60),X60)
        | ~ r3_lattice3(X56,X57,X60)
        | X57 = k16_lattice3(X56,X60)
        | ~ m1_subset_1(X57,u1_struct_0(X56))
        | v2_struct_0(X56)
        | ~ v10_lattices(X56)
        | ~ v4_lattice3(X56)
        | ~ l3_lattices(X56) )
      & ( ~ r3_lattices(X56,esk11_3(X56,X57,X60),X57)
        | ~ r3_lattice3(X56,X57,X60)
        | X57 = k16_lattice3(X56,X60)
        | ~ m1_subset_1(X57,u1_struct_0(X56))
        | v2_struct_0(X56)
        | ~ v10_lattices(X56)
        | ~ v4_lattice3(X56)
        | ~ l3_lattices(X56) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_lattice3])])])])])])])).

cnf(c_0_22,plain,
    ( r1_lattices(X1,X2,X4)
    | v2_struct_0(X1)
    | ~ r3_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_23,plain,
    ( r3_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | X2 != k16_lattice3(X1,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_24,plain,(
    ! [X40,X41] :
      ( v2_struct_0(X40)
      | ~ l3_lattices(X40)
      | m1_subset_1(k16_lattice3(X40,X41),u1_struct_0(X40)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k16_lattice3])])])).

fof(c_0_25,plain,(
    ! [X48,X49,X50,X53,X54,X55] :
      ( ( m1_subset_1(esk9_3(X48,X49,X50),u1_struct_0(X49))
        | ~ r2_hidden(X48,a_2_6_lattice3(X49,X50))
        | v2_struct_0(X49)
        | ~ v10_lattices(X49)
        | ~ v4_lattice3(X49)
        | ~ l3_lattices(X49) )
      & ( X48 = esk9_3(X48,X49,X50)
        | ~ r2_hidden(X48,a_2_6_lattice3(X49,X50))
        | v2_struct_0(X49)
        | ~ v10_lattices(X49)
        | ~ v4_lattice3(X49)
        | ~ l3_lattices(X49) )
      & ( m1_subset_1(esk10_3(X48,X49,X50),u1_struct_0(X49))
        | ~ r2_hidden(X48,a_2_6_lattice3(X49,X50))
        | v2_struct_0(X49)
        | ~ v10_lattices(X49)
        | ~ v4_lattice3(X49)
        | ~ l3_lattices(X49) )
      & ( r3_lattices(X49,esk10_3(X48,X49,X50),esk9_3(X48,X49,X50))
        | ~ r2_hidden(X48,a_2_6_lattice3(X49,X50))
        | v2_struct_0(X49)
        | ~ v10_lattices(X49)
        | ~ v4_lattice3(X49)
        | ~ l3_lattices(X49) )
      & ( r2_hidden(esk10_3(X48,X49,X50),X50)
        | ~ r2_hidden(X48,a_2_6_lattice3(X49,X50))
        | v2_struct_0(X49)
        | ~ v10_lattices(X49)
        | ~ v4_lattice3(X49)
        | ~ l3_lattices(X49) )
      & ( ~ m1_subset_1(X54,u1_struct_0(X49))
        | X48 != X54
        | ~ m1_subset_1(X55,u1_struct_0(X49))
        | ~ r3_lattices(X49,X55,X54)
        | ~ r2_hidden(X55,X53)
        | r2_hidden(X48,a_2_6_lattice3(X49,X53))
        | v2_struct_0(X49)
        | ~ v10_lattices(X49)
        | ~ v4_lattice3(X49)
        | ~ l3_lattices(X49) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_6_lattice3])])])])])])])).

fof(c_0_26,plain,(
    ! [X66,X67,X68] :
      ( ( r3_lattices(X66,k15_lattice3(X66,X67),k15_lattice3(X66,X68))
        | ~ r1_tarski(X67,X68)
        | v2_struct_0(X66)
        | ~ v10_lattices(X66)
        | ~ v4_lattice3(X66)
        | ~ l3_lattices(X66) )
      & ( r3_lattices(X66,k16_lattice3(X66,X68),k16_lattice3(X66,X67))
        | ~ r1_tarski(X67,X68)
        | v2_struct_0(X66)
        | ~ v10_lattices(X66)
        | ~ v4_lattice3(X66)
        | ~ l3_lattices(X66) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t46_lattice3])])])])])).

fof(c_0_27,plain,(
    ! [X69,X70] :
      ( ( k15_lattice3(X69,X70) = k15_lattice3(X69,a_2_5_lattice3(X69,X70))
        | v2_struct_0(X69)
        | ~ v10_lattices(X69)
        | ~ v4_lattice3(X69)
        | ~ l3_lattices(X69) )
      & ( k16_lattice3(X69,X70) = k16_lattice3(X69,a_2_6_lattice3(X69,X70))
        | v2_struct_0(X69)
        | ~ v10_lattices(X69)
        | ~ v4_lattice3(X69)
        | ~ l3_lattices(X69) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t47_lattice3])])])])])).

cnf(c_0_28,plain,
    ( r1_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | X2 != k16_lattice3(X1,X4)
    | ~ v4_lattice3(X1)
    | ~ r2_hidden(X3,X4)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_29,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k16_lattice3(X1,X2),u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,plain,
    ( m1_subset_1(esk9_3(X1,X2,X3),u1_struct_0(X2))
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_6_lattice3(X2,X3))
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,plain,
    ( X1 = esk9_3(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_6_lattice3(X2,X3))
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,plain,
    ( r3_lattices(X1,k15_lattice3(X1,X2),k15_lattice3(X1,X3))
    | v2_struct_0(X1)
    | ~ r1_tarski(X2,X3)
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( k15_lattice3(X1,X2) = k15_lattice3(X1,a_2_5_lattice3(X1,X2))
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_35,plain,(
    ! [X38,X39] :
      ( v2_struct_0(X38)
      | ~ l3_lattices(X38)
      | m1_subset_1(k15_lattice3(X38,X39),u1_struct_0(X38)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k15_lattice3])])])).

fof(c_0_36,plain,(
    ! [X17,X19,X20] :
      ( ( m1_subset_1(esk2_1(X17),u1_struct_0(X17))
        | ~ v13_lattices(X17)
        | v2_struct_0(X17)
        | ~ l1_lattices(X17) )
      & ( k2_lattices(X17,esk2_1(X17),X19) = esk2_1(X17)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ v13_lattices(X17)
        | v2_struct_0(X17)
        | ~ l1_lattices(X17) )
      & ( k2_lattices(X17,X19,esk2_1(X17)) = esk2_1(X17)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ v13_lattices(X17)
        | v2_struct_0(X17)
        | ~ l1_lattices(X17) )
      & ( m1_subset_1(esk3_2(X17,X20),u1_struct_0(X17))
        | ~ m1_subset_1(X20,u1_struct_0(X17))
        | v13_lattices(X17)
        | v2_struct_0(X17)
        | ~ l1_lattices(X17) )
      & ( k2_lattices(X17,X20,esk3_2(X17,X20)) != X20
        | k2_lattices(X17,esk3_2(X17,X20),X20) != X20
        | ~ m1_subset_1(X20,u1_struct_0(X17))
        | v13_lattices(X17)
        | v2_struct_0(X17)
        | ~ l1_lattices(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d13_lattices])])])])])])).

fof(c_0_37,plain,(
    ! [X33,X34,X35] :
      ( ( ~ v6_lattices(X33)
        | ~ m1_subset_1(X34,u1_struct_0(X33))
        | ~ m1_subset_1(X35,u1_struct_0(X33))
        | k2_lattices(X33,X34,X35) = k2_lattices(X33,X35,X34)
        | v2_struct_0(X33)
        | ~ l1_lattices(X33) )
      & ( m1_subset_1(esk6_1(X33),u1_struct_0(X33))
        | v6_lattices(X33)
        | v2_struct_0(X33)
        | ~ l1_lattices(X33) )
      & ( m1_subset_1(esk7_1(X33),u1_struct_0(X33))
        | v6_lattices(X33)
        | v2_struct_0(X33)
        | ~ l1_lattices(X33) )
      & ( k2_lattices(X33,esk6_1(X33),esk7_1(X33)) != k2_lattices(X33,esk7_1(X33),esk6_1(X33))
        | v6_lattices(X33)
        | v2_struct_0(X33)
        | ~ l1_lattices(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d6_lattices])])])])])])).

fof(c_0_38,plain,(
    ! [X14,X15,X16] :
      ( ( ~ r1_lattices(X14,X15,X16)
        | k2_lattices(X14,X15,X16) = X15
        | ~ m1_subset_1(X16,u1_struct_0(X14))
        | ~ m1_subset_1(X15,u1_struct_0(X14))
        | v2_struct_0(X14)
        | ~ v8_lattices(X14)
        | ~ v9_lattices(X14)
        | ~ l3_lattices(X14) )
      & ( k2_lattices(X14,X15,X16) != X15
        | r1_lattices(X14,X15,X16)
        | ~ m1_subset_1(X16,u1_struct_0(X14))
        | ~ m1_subset_1(X15,u1_struct_0(X14))
        | v2_struct_0(X14)
        | ~ v8_lattices(X14)
        | ~ v9_lattices(X14)
        | ~ l3_lattices(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t21_lattices])])])])])).

cnf(c_0_39,plain,
    ( r1_lattices(X1,k16_lattice3(X1,X2),X3)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_28]),c_0_29])).

cnf(c_0_40,plain,
    ( k16_lattice3(X1,X2) = k16_lattice3(X1,a_2_6_lattice3(X1,X2))
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_41,plain,
    ( m1_subset_1(X1,u1_struct_0(X2))
    | v2_struct_0(X2)
    | ~ v4_lattice3(X2)
    | ~ r2_hidden(X1,a_2_6_lattice3(X2,X3))
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

fof(c_0_42,plain,(
    ! [X7] :
      ( ( ~ v2_struct_0(X7)
        | v2_struct_0(X7)
        | ~ v10_lattices(X7)
        | ~ l3_lattices(X7) )
      & ( v4_lattices(X7)
        | v2_struct_0(X7)
        | ~ v10_lattices(X7)
        | ~ l3_lattices(X7) )
      & ( v5_lattices(X7)
        | v2_struct_0(X7)
        | ~ v10_lattices(X7)
        | ~ l3_lattices(X7) )
      & ( v6_lattices(X7)
        | v2_struct_0(X7)
        | ~ v10_lattices(X7)
        | ~ l3_lattices(X7) )
      & ( v7_lattices(X7)
        | v2_struct_0(X7)
        | ~ v10_lattices(X7)
        | ~ l3_lattices(X7) )
      & ( v8_lattices(X7)
        | v2_struct_0(X7)
        | ~ v10_lattices(X7)
        | ~ l3_lattices(X7) )
      & ( v9_lattices(X7)
        | v2_struct_0(X7)
        | ~ v10_lattices(X7)
        | ~ l3_lattices(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,a_2_6_lattice3(X2,X3))
    | v2_struct_0(X2)
    | ~ r3_lattices(X2,X4,X1)
    | ~ v4_lattice3(X2)
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(er,[status(thm)],[c_0_32])).

cnf(c_0_44,plain,
    ( r3_lattices(X1,k15_lattice3(X1,X2),k15_lattice3(X1,X3))
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ r1_tarski(X2,a_2_5_lattice3(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_45,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_46,plain,(
    ! [X6] : r1_tarski(k1_xboole_0,X6) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_47,plain,
    ( v13_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,esk3_2(X1,X2)) != X2
    | k2_lattices(X1,esk3_2(X1,X2),X2) != X2
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_48,plain,
    ( k2_lattices(X1,X2,X3) = k2_lattices(X1,X3,X2)
    | v2_struct_0(X1)
    | ~ v6_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_49,plain,
    ( m1_subset_1(esk3_2(X1,X2),u1_struct_0(X1))
    | v13_lattices(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_50,plain,
    ( k2_lattices(X1,X2,X3) = X2
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_51,plain,
    ( r1_lattices(X1,k16_lattice3(X1,X2),X3)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ r2_hidden(X3,a_2_6_lattice3(X1,X2))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41])).

cnf(c_0_52,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_53,plain,
    ( v9_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

fof(c_0_54,plain,(
    ! [X13] :
      ( ( l1_lattices(X13)
        | ~ l3_lattices(X13) )
      & ( l2_lattices(X13)
        | ~ l3_lattices(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).

cnf(c_0_55,plain,
    ( r2_hidden(k15_lattice3(X1,X2),a_2_6_lattice3(X1,X3))
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ r2_hidden(k15_lattice3(X1,X4),X3)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ r1_tarski(X4,a_2_5_lattice3(X1,X2)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45]),c_0_45])).

cnf(c_0_56,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

fof(c_0_57,plain,(
    ! [X64,X65] :
      ( ( k15_lattice3(X64,k6_domain_1(u1_struct_0(X64),X65)) = X65
        | ~ m1_subset_1(X65,u1_struct_0(X64))
        | v2_struct_0(X64)
        | ~ v10_lattices(X64)
        | ~ v4_lattice3(X64)
        | ~ l3_lattices(X64) )
      & ( k16_lattice3(X64,k6_domain_1(u1_struct_0(X64),X65)) = X65
        | ~ m1_subset_1(X65,u1_struct_0(X64))
        | v2_struct_0(X64)
        | ~ v10_lattices(X64)
        | ~ v4_lattice3(X64)
        | ~ l3_lattices(X64) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t43_lattice3])])])])])).

cnf(c_0_58,plain,
    ( v13_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,esk3_2(X1,X2)) != X2
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v6_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49])).

cnf(c_0_59,plain,
    ( k2_lattices(X1,k16_lattice3(X1,X2),X3) = k16_lattice3(X1,X2)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ r2_hidden(X3,a_2_6_lattice3(X1,X2))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52]),c_0_53]),c_0_41]),c_0_29])).

cnf(c_0_60,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_61,plain,
    ( l1_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_62,plain,
    ( r2_hidden(k15_lattice3(X1,X2),a_2_6_lattice3(X1,X3))
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ r2_hidden(k15_lattice3(X1,k1_xboole_0),X3)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_63,plain,
    ( k15_lattice3(X1,k6_domain_1(u1_struct_0(X1),X2)) = X2
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

fof(c_0_64,plain,(
    ! [X42,X43,X44,X46,X47] :
      ( ( m1_subset_1(esk8_3(X42,X43,X44),u1_struct_0(X43))
        | ~ r2_hidden(X42,a_2_2_lattice3(X43,X44))
        | v2_struct_0(X43)
        | ~ v10_lattices(X43)
        | ~ v4_lattice3(X43)
        | ~ l3_lattices(X43) )
      & ( X42 = esk8_3(X42,X43,X44)
        | ~ r2_hidden(X42,a_2_2_lattice3(X43,X44))
        | v2_struct_0(X43)
        | ~ v10_lattices(X43)
        | ~ v4_lattice3(X43)
        | ~ l3_lattices(X43) )
      & ( r4_lattice3(X43,esk8_3(X42,X43,X44),X44)
        | ~ r2_hidden(X42,a_2_2_lattice3(X43,X44))
        | v2_struct_0(X43)
        | ~ v10_lattices(X43)
        | ~ v4_lattice3(X43)
        | ~ l3_lattices(X43) )
      & ( ~ m1_subset_1(X47,u1_struct_0(X43))
        | X42 != X47
        | ~ r4_lattice3(X43,X47,X46)
        | r2_hidden(X42,a_2_2_lattice3(X43,X46))
        | v2_struct_0(X43)
        | ~ v10_lattices(X43)
        | ~ v4_lattice3(X43)
        | ~ l3_lattices(X43) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_2_lattice3])])])])])])])).

fof(c_0_65,plain,(
    ! [X28,X29,X30,X31] :
      ( ( r4_lattice3(X28,X30,X29)
        | X30 != k15_lattice3(X28,X29)
        | ~ m1_subset_1(X30,u1_struct_0(X28))
        | v2_struct_0(X28)
        | ~ v10_lattices(X28)
        | ~ v4_lattice3(X28)
        | ~ l3_lattices(X28)
        | v2_struct_0(X28)
        | ~ l3_lattices(X28) )
      & ( ~ m1_subset_1(X31,u1_struct_0(X28))
        | ~ r4_lattice3(X28,X31,X29)
        | r1_lattices(X28,X30,X31)
        | X30 != k15_lattice3(X28,X29)
        | ~ m1_subset_1(X30,u1_struct_0(X28))
        | v2_struct_0(X28)
        | ~ v10_lattices(X28)
        | ~ v4_lattice3(X28)
        | ~ l3_lattices(X28)
        | v2_struct_0(X28)
        | ~ l3_lattices(X28) )
      & ( m1_subset_1(esk5_3(X28,X29,X30),u1_struct_0(X28))
        | ~ r4_lattice3(X28,X30,X29)
        | X30 = k15_lattice3(X28,X29)
        | ~ m1_subset_1(X30,u1_struct_0(X28))
        | v2_struct_0(X28)
        | ~ v10_lattices(X28)
        | ~ v4_lattice3(X28)
        | ~ l3_lattices(X28)
        | v2_struct_0(X28)
        | ~ l3_lattices(X28) )
      & ( r4_lattice3(X28,esk5_3(X28,X29,X30),X29)
        | ~ r4_lattice3(X28,X30,X29)
        | X30 = k15_lattice3(X28,X29)
        | ~ m1_subset_1(X30,u1_struct_0(X28))
        | v2_struct_0(X28)
        | ~ v10_lattices(X28)
        | ~ v4_lattice3(X28)
        | ~ l3_lattices(X28)
        | v2_struct_0(X28)
        | ~ l3_lattices(X28) )
      & ( ~ r1_lattices(X28,X30,esk5_3(X28,X29,X30))
        | ~ r4_lattice3(X28,X30,X29)
        | X30 = k15_lattice3(X28,X29)
        | ~ m1_subset_1(X30,u1_struct_0(X28))
        | v2_struct_0(X28)
        | ~ v10_lattices(X28)
        | ~ v4_lattice3(X28)
        | ~ l3_lattices(X28)
        | v2_struct_0(X28)
        | ~ l3_lattices(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d21_lattice3])])])])])])).

cnf(c_0_66,plain,
    ( v13_lattices(X1)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ r2_hidden(esk3_2(X1,k16_lattice3(X1,X2)),a_2_6_lattice3(X1,X2))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_60]),c_0_61]),c_0_29])).

cnf(c_0_67,plain,
    ( r2_hidden(X1,a_2_6_lattice3(X2,X3))
    | v2_struct_0(X2)
    | ~ v4_lattice3(X2)
    | ~ r2_hidden(k15_lattice3(X2,k1_xboole_0),X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_68,plain,
    ( r2_hidden(X3,a_2_2_lattice3(X2,X4))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | X3 != X1
    | ~ r4_lattice3(X2,X1,X4)
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_69,plain,
    ( r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | v2_struct_0(X1)
    | X2 != k15_lattice3(X1,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_70,plain,
    ( v13_lattices(X1)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ r2_hidden(k15_lattice3(X1,k1_xboole_0),X2)
    | ~ m1_subset_1(esk3_2(X1,k16_lattice3(X1,X2)),u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_71,plain,
    ( r2_hidden(X1,a_2_2_lattice3(X2,X3))
    | v2_struct_0(X2)
    | ~ r4_lattice3(X2,X1,X3)
    | ~ v4_lattice3(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(er,[status(thm)],[c_0_68])).

cnf(c_0_72,plain,
    ( v2_struct_0(X1)
    | r4_lattice3(X1,X2,X3)
    | X2 != k15_lattice3(X1,X3)
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(cn,[status(thm)],[c_0_69])).

cnf(c_0_73,plain,
    ( v13_lattices(X1)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ r2_hidden(k15_lattice3(X1,k1_xboole_0),X2)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_49]),c_0_61]),c_0_29])).

cnf(c_0_74,plain,
    ( r2_hidden(X1,a_2_2_lattice3(X2,X3))
    | v2_struct_0(X2)
    | X1 != k15_lattice3(X2,X3)
    | ~ v4_lattice3(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_75,plain,
    ( v13_lattices(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | k15_lattice3(X1,k1_xboole_0) != k15_lattice3(X2,X3)
    | ~ v4_lattice3(X1)
    | ~ v4_lattice3(X2)
    | ~ m1_subset_1(k15_lattice3(X1,k1_xboole_0),u1_struct_0(X2))
    | ~ v10_lattices(X1)
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X1)
    | ~ l3_lattices(X2) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_76,plain,
    ( r2_hidden(k15_lattice3(X1,X2),a_2_6_lattice3(X1,X3))
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ r2_hidden(k15_lattice3(X1,X4),X3)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ r1_tarski(X4,X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_33]),c_0_45]),c_0_45])).

cnf(c_0_77,plain,
    ( v13_lattices(X1)
    | v2_struct_0(X1)
    | k15_lattice3(X1,k1_xboole_0) != k15_lattice3(X1,X2)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_75,c_0_45])).

cnf(c_0_78,plain,
    ( r2_hidden(k15_lattice3(X1,X2),a_2_6_lattice3(X1,a_2_6_lattice3(X1,X3)))
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ r2_hidden(k15_lattice3(X1,k1_xboole_0),X3)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ r1_tarski(X4,X2) ),
    inference(spm,[status(thm)],[c_0_76,c_0_62])).

fof(c_0_79,plain,(
    ! [X8,X9,X10] :
      ( ( k2_lattices(X8,X9,X10) = X9
        | ~ m1_subset_1(X10,u1_struct_0(X8))
        | X9 != k5_lattices(X8)
        | ~ m1_subset_1(X9,u1_struct_0(X8))
        | ~ v13_lattices(X8)
        | v2_struct_0(X8)
        | ~ l1_lattices(X8) )
      & ( k2_lattices(X8,X10,X9) = X9
        | ~ m1_subset_1(X10,u1_struct_0(X8))
        | X9 != k5_lattices(X8)
        | ~ m1_subset_1(X9,u1_struct_0(X8))
        | ~ v13_lattices(X8)
        | v2_struct_0(X8)
        | ~ l1_lattices(X8) )
      & ( m1_subset_1(esk1_2(X8,X9),u1_struct_0(X8))
        | X9 = k5_lattices(X8)
        | ~ m1_subset_1(X9,u1_struct_0(X8))
        | ~ v13_lattices(X8)
        | v2_struct_0(X8)
        | ~ l1_lattices(X8) )
      & ( k2_lattices(X8,X9,esk1_2(X8,X9)) != X9
        | k2_lattices(X8,esk1_2(X8,X9),X9) != X9
        | X9 = k5_lattices(X8)
        | ~ m1_subset_1(X9,u1_struct_0(X8))
        | ~ v13_lattices(X8)
        | v2_struct_0(X8)
        | ~ l1_lattices(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattices])])])])])])).

cnf(c_0_80,plain,
    ( k2_lattices(X1,X2,esk2_1(X1)) = esk2_1(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v13_lattices(X1)
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_81,plain,
    ( v13_lattices(X1)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(er,[status(thm)],[c_0_77])).

cnf(c_0_82,plain,
    ( r2_hidden(k15_lattice3(X1,X2),a_2_6_lattice3(X1,a_2_6_lattice3(X1,X3)))
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ r2_hidden(k15_lattice3(X1,k1_xboole_0),X3)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_78,c_0_56])).

cnf(c_0_83,plain,
    ( k2_lattices(X1,esk2_1(X1),X2) = esk2_1(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v13_lattices(X1)
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_84,plain,
    ( k2_lattices(X1,X2,X3) = X3
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | X3 != k5_lattices(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v13_lattices(X1)
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_85,plain,
    ( m1_subset_1(esk2_1(X1),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v13_lattices(X1)
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_86,plain,(
    ! [X12] :
      ( v2_struct_0(X12)
      | ~ l1_lattices(X12)
      | m1_subset_1(k5_lattices(X12),u1_struct_0(X12)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_lattices])])])).

cnf(c_0_87,plain,
    ( k16_lattice3(X1,X2) = esk2_1(X1)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ r2_hidden(esk2_1(X1),a_2_6_lattice3(X1,X2))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_59]),c_0_61]),c_0_81]),c_0_29])).

cnf(c_0_88,plain,
    ( r2_hidden(X1,a_2_6_lattice3(X2,a_2_6_lattice3(X2,X3)))
    | v2_struct_0(X2)
    | ~ v4_lattice3(X2)
    | ~ r2_hidden(k15_lattice3(X2,k1_xboole_0),X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(spm,[status(thm)],[c_0_82,c_0_63])).

cnf(c_0_89,plain,
    ( X1 = esk2_1(X2)
    | v2_struct_0(X2)
    | X1 != k5_lattices(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v13_lattices(X2)
    | ~ l1_lattices(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_85])).

cnf(c_0_90,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_86])).

cnf(c_0_91,plain,
    ( k16_lattice3(X1,a_2_6_lattice3(X1,X2)) = esk2_1(X1)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ r2_hidden(k15_lattice3(X1,k1_xboole_0),X2)
    | ~ m1_subset_1(esk2_1(X1),u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_92,plain,
    ( esk2_1(X1) = k5_lattices(X1)
    | v2_struct_0(X1)
    | ~ v13_lattices(X1)
    | ~ l1_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_93,plain,
    ( k16_lattice3(X1,a_2_6_lattice3(X1,X2)) = esk2_1(X1)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ r2_hidden(k15_lattice3(X1,k1_xboole_0),X2)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_85]),c_0_61]),c_0_81])).

cnf(c_0_94,plain,
    ( r2_hidden(k15_lattice3(X1,X2),a_2_6_lattice3(X1,a_2_2_lattice3(X3,X4)))
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | k15_lattice3(X1,X5) != k15_lattice3(X3,X4)
    | ~ v4_lattice3(X1)
    | ~ v4_lattice3(X3)
    | ~ m1_subset_1(k15_lattice3(X1,X5),u1_struct_0(X3))
    | ~ v10_lattices(X1)
    | ~ v10_lattices(X3)
    | ~ l3_lattices(X1)
    | ~ l3_lattices(X3)
    | ~ r1_tarski(X5,X2) ),
    inference(spm,[status(thm)],[c_0_76,c_0_74])).

cnf(c_0_95,plain,
    ( k16_lattice3(X1,a_2_6_lattice3(X1,X2)) = k5_lattices(X1)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ r2_hidden(k15_lattice3(X1,k1_xboole_0),X2)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_61]),c_0_81])).

cnf(c_0_96,plain,
    ( r2_hidden(k15_lattice3(X1,X2),a_2_6_lattice3(X1,a_2_2_lattice3(X1,X3)))
    | v2_struct_0(X1)
    | k15_lattice3(X1,X4) != k15_lattice3(X1,X3)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ r1_tarski(X4,X2) ),
    inference(spm,[status(thm)],[c_0_94,c_0_45])).

cnf(c_0_97,plain,
    ( k16_lattice3(X1,X2) = k5_lattices(X1)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ r2_hidden(k15_lattice3(X1,k1_xboole_0),X2)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_95])).

cnf(c_0_98,plain,
    ( r2_hidden(k15_lattice3(X1,X2),a_2_6_lattice3(X1,a_2_2_lattice3(X1,X3)))
    | v2_struct_0(X1)
    | k15_lattice3(X1,k1_xboole_0) != k15_lattice3(X1,X3)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_96,c_0_56])).

fof(c_0_99,negated_conjecture,(
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

fof(c_0_100,plain,(
    ! [X62,X63] :
      ( v2_struct_0(X62)
      | ~ v10_lattices(X62)
      | ~ v4_lattice3(X62)
      | ~ l3_lattices(X62)
      | k15_lattice3(X62,X63) = k16_lattice3(X62,a_2_2_lattice3(X62,X63)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t37_lattice3])])])])).

cnf(c_0_101,plain,
    ( k16_lattice3(X1,a_2_6_lattice3(X1,a_2_2_lattice3(X1,X2))) = k5_lattices(X1)
    | v2_struct_0(X1)
    | k15_lattice3(X1,k1_xboole_0) != k15_lattice3(X1,X2)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_97,c_0_98])).

fof(c_0_102,negated_conjecture,
    ( ~ v2_struct_0(esk13_0)
    & v10_lattices(esk13_0)
    & v4_lattice3(esk13_0)
    & l3_lattices(esk13_0)
    & ( v2_struct_0(esk13_0)
      | ~ v10_lattices(esk13_0)
      | ~ v13_lattices(esk13_0)
      | ~ l3_lattices(esk13_0)
      | k5_lattices(esk13_0) != k15_lattice3(esk13_0,k1_xboole_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_99])])])])).

cnf(c_0_103,plain,
    ( v2_struct_0(X1)
    | k15_lattice3(X1,X2) = k16_lattice3(X1,a_2_2_lattice3(X1,X2))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_100])).

cnf(c_0_104,plain,
    ( k16_lattice3(X1,a_2_2_lattice3(X1,X2)) = k5_lattices(X1)
    | v2_struct_0(X1)
    | k15_lattice3(X1,k1_xboole_0) != k15_lattice3(X1,X2)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_101])).

cnf(c_0_105,negated_conjecture,
    ( v2_struct_0(esk13_0)
    | ~ v10_lattices(esk13_0)
    | ~ v13_lattices(esk13_0)
    | ~ l3_lattices(esk13_0)
    | k5_lattices(esk13_0) != k15_lattice3(esk13_0,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_102])).

cnf(c_0_106,negated_conjecture,
    ( l3_lattices(esk13_0) ),
    inference(split_conjunct,[status(thm)],[c_0_102])).

cnf(c_0_107,negated_conjecture,
    ( v10_lattices(esk13_0) ),
    inference(split_conjunct,[status(thm)],[c_0_102])).

cnf(c_0_108,negated_conjecture,
    ( ~ v2_struct_0(esk13_0) ),
    inference(split_conjunct,[status(thm)],[c_0_102])).

cnf(c_0_109,plain,
    ( k15_lattice3(X1,X2) = k5_lattices(X1)
    | v2_struct_0(X1)
    | k15_lattice3(X1,k1_xboole_0) != k15_lattice3(X1,X2)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_103,c_0_104])).

cnf(c_0_110,negated_conjecture,
    ( k15_lattice3(esk13_0,k1_xboole_0) != k5_lattices(esk13_0)
    | ~ v13_lattices(esk13_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_105,c_0_106]),c_0_107])]),c_0_108])).

cnf(c_0_111,plain,
    ( k15_lattice3(X1,k1_xboole_0) = k5_lattices(X1)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(er,[status(thm)],[c_0_109])).

cnf(c_0_112,negated_conjecture,
    ( v4_lattice3(esk13_0) ),
    inference(split_conjunct,[status(thm)],[c_0_102])).

cnf(c_0_113,negated_conjecture,
    ( ~ v13_lattices(esk13_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_111]),c_0_112]),c_0_107]),c_0_106])]),c_0_108])).

cnf(c_0_114,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_81]),c_0_112]),c_0_107]),c_0_106])]),c_0_108]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:12:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.78/0.96  # AutoSched0-Mode selected heuristic G_E___208_B02_F1_AE_CS_SP_PS_S0Y
% 0.78/0.96  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.78/0.96  #
% 0.78/0.96  # Preprocessing time       : 0.032 s
% 0.78/0.96  # Presaturation interreduction done
% 0.78/0.96  
% 0.78/0.96  # Proof found!
% 0.78/0.96  # SZS status Theorem
% 0.78/0.96  # SZS output start CNFRefutation
% 0.78/0.96  fof(d16_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(r3_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X3)=>r1_lattices(X1,X2,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_lattice3)).
% 0.78/0.96  fof(t34_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(X2=k16_lattice3(X1,X3)<=>(r3_lattice3(X1,X2,X3)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r3_lattice3(X1,X4,X3)=>r3_lattices(X1,X4,X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_lattice3)).
% 0.78/0.96  fof(dt_k16_lattice3, axiom, ![X1, X2]:((~(v2_struct_0(X1))&l3_lattices(X1))=>m1_subset_1(k16_lattice3(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k16_lattice3)).
% 0.78/0.96  fof(fraenkel_a_2_6_lattice3, axiom, ![X1, X2, X3]:((((~(v2_struct_0(X2))&v10_lattices(X2))&v4_lattice3(X2))&l3_lattices(X2))=>(r2_hidden(X1,a_2_6_lattice3(X2,X3))<=>?[X4]:((m1_subset_1(X4,u1_struct_0(X2))&X1=X4)&?[X5]:((m1_subset_1(X5,u1_struct_0(X2))&r3_lattices(X2,X5,X4))&r2_hidden(X5,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_6_lattice3)).
% 0.78/0.96  fof(t46_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2, X3]:(r1_tarski(X2,X3)=>(r3_lattices(X1,k15_lattice3(X1,X2),k15_lattice3(X1,X3))&r3_lattices(X1,k16_lattice3(X1,X3),k16_lattice3(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_lattice3)).
% 0.78/0.96  fof(t47_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(k15_lattice3(X1,X2)=k15_lattice3(X1,a_2_5_lattice3(X1,X2))&k16_lattice3(X1,X2)=k16_lattice3(X1,a_2_6_lattice3(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_lattice3)).
% 0.78/0.96  fof(dt_k15_lattice3, axiom, ![X1, X2]:((~(v2_struct_0(X1))&l3_lattices(X1))=>m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k15_lattice3)).
% 0.78/0.96  fof(d13_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>(v13_lattices(X1)<=>?[X2]:(m1_subset_1(X2,u1_struct_0(X1))&![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(k2_lattices(X1,X2,X3)=X2&k2_lattices(X1,X3,X2)=X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_lattices)).
% 0.78/0.96  fof(d6_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>(v6_lattices(X1)<=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>k2_lattices(X1,X2,X3)=k2_lattices(X1,X3,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_lattices)).
% 0.78/0.96  fof(t21_lattices, axiom, ![X1]:((((~(v2_struct_0(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_lattices(X1,X2,X3)<=>k2_lattices(X1,X2,X3)=X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_lattices)).
% 0.78/0.96  fof(cc1_lattices, axiom, ![X1]:(l3_lattices(X1)=>((~(v2_struct_0(X1))&v10_lattices(X1))=>((((((~(v2_struct_0(X1))&v4_lattices(X1))&v5_lattices(X1))&v6_lattices(X1))&v7_lattices(X1))&v8_lattices(X1))&v9_lattices(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattices)).
% 0.78/0.96  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.78/0.96  fof(dt_l3_lattices, axiom, ![X1]:(l3_lattices(X1)=>(l1_lattices(X1)&l2_lattices(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l3_lattices)).
% 0.78/0.96  fof(t43_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(k15_lattice3(X1,k6_domain_1(u1_struct_0(X1),X2))=X2&k16_lattice3(X1,k6_domain_1(u1_struct_0(X1),X2))=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_lattice3)).
% 0.78/0.96  fof(fraenkel_a_2_2_lattice3, axiom, ![X1, X2, X3]:((((~(v2_struct_0(X2))&v10_lattices(X2))&v4_lattice3(X2))&l3_lattices(X2))=>(r2_hidden(X1,a_2_2_lattice3(X2,X3))<=>?[X4]:((m1_subset_1(X4,u1_struct_0(X2))&X1=X4)&r4_lattice3(X2,X4,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_2_lattice3)).
% 0.78/0.96  fof(d21_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(X3=k15_lattice3(X1,X2)<=>(r4_lattice3(X1,X3,X2)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r4_lattice3(X1,X4,X2)=>r1_lattices(X1,X3,X4)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d21_lattice3)).
% 0.78/0.96  fof(d16_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>(v13_lattices(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(X2=k5_lattices(X1)<=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(k2_lattices(X1,X2,X3)=X2&k2_lattices(X1,X3,X2)=X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_lattices)).
% 0.78/0.96  fof(dt_k5_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>m1_subset_1(k5_lattices(X1),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_lattices)).
% 0.78/0.96  fof(t50_lattice3, conjecture, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>((((~(v2_struct_0(X1))&v10_lattices(X1))&v13_lattices(X1))&l3_lattices(X1))&k5_lattices(X1)=k15_lattice3(X1,k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_lattice3)).
% 0.78/0.96  fof(t37_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:k15_lattice3(X1,X2)=k16_lattice3(X1,a_2_2_lattice3(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_lattice3)).
% 0.78/0.96  fof(c_0_20, plain, ![X22, X23, X24, X25, X26]:((~r3_lattice3(X22,X23,X24)|(~m1_subset_1(X25,u1_struct_0(X22))|(~r2_hidden(X25,X24)|r1_lattices(X22,X23,X25)))|~m1_subset_1(X23,u1_struct_0(X22))|(v2_struct_0(X22)|~l3_lattices(X22)))&((m1_subset_1(esk4_3(X22,X23,X26),u1_struct_0(X22))|r3_lattice3(X22,X23,X26)|~m1_subset_1(X23,u1_struct_0(X22))|(v2_struct_0(X22)|~l3_lattices(X22)))&((r2_hidden(esk4_3(X22,X23,X26),X26)|r3_lattice3(X22,X23,X26)|~m1_subset_1(X23,u1_struct_0(X22))|(v2_struct_0(X22)|~l3_lattices(X22)))&(~r1_lattices(X22,X23,esk4_3(X22,X23,X26))|r3_lattice3(X22,X23,X26)|~m1_subset_1(X23,u1_struct_0(X22))|(v2_struct_0(X22)|~l3_lattices(X22)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattice3])])])])])])])).
% 0.78/0.96  fof(c_0_21, plain, ![X56, X57, X58, X59, X60]:(((r3_lattice3(X56,X57,X58)|X57!=k16_lattice3(X56,X58)|~m1_subset_1(X57,u1_struct_0(X56))|(v2_struct_0(X56)|~v10_lattices(X56)|~v4_lattice3(X56)|~l3_lattices(X56)))&(~m1_subset_1(X59,u1_struct_0(X56))|(~r3_lattice3(X56,X59,X58)|r3_lattices(X56,X59,X57))|X57!=k16_lattice3(X56,X58)|~m1_subset_1(X57,u1_struct_0(X56))|(v2_struct_0(X56)|~v10_lattices(X56)|~v4_lattice3(X56)|~l3_lattices(X56))))&((m1_subset_1(esk11_3(X56,X57,X60),u1_struct_0(X56))|~r3_lattice3(X56,X57,X60)|X57=k16_lattice3(X56,X60)|~m1_subset_1(X57,u1_struct_0(X56))|(v2_struct_0(X56)|~v10_lattices(X56)|~v4_lattice3(X56)|~l3_lattices(X56)))&((r3_lattice3(X56,esk11_3(X56,X57,X60),X60)|~r3_lattice3(X56,X57,X60)|X57=k16_lattice3(X56,X60)|~m1_subset_1(X57,u1_struct_0(X56))|(v2_struct_0(X56)|~v10_lattices(X56)|~v4_lattice3(X56)|~l3_lattices(X56)))&(~r3_lattices(X56,esk11_3(X56,X57,X60),X57)|~r3_lattice3(X56,X57,X60)|X57=k16_lattice3(X56,X60)|~m1_subset_1(X57,u1_struct_0(X56))|(v2_struct_0(X56)|~v10_lattices(X56)|~v4_lattice3(X56)|~l3_lattices(X56)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_lattice3])])])])])])])).
% 0.78/0.96  cnf(c_0_22, plain, (r1_lattices(X1,X2,X4)|v2_struct_0(X1)|~r3_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X4,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.78/0.96  cnf(c_0_23, plain, (r3_lattice3(X1,X2,X3)|v2_struct_0(X1)|X2!=k16_lattice3(X1,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.78/0.96  fof(c_0_24, plain, ![X40, X41]:(v2_struct_0(X40)|~l3_lattices(X40)|m1_subset_1(k16_lattice3(X40,X41),u1_struct_0(X40))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k16_lattice3])])])).
% 0.78/0.96  fof(c_0_25, plain, ![X48, X49, X50, X53, X54, X55]:((((m1_subset_1(esk9_3(X48,X49,X50),u1_struct_0(X49))|~r2_hidden(X48,a_2_6_lattice3(X49,X50))|(v2_struct_0(X49)|~v10_lattices(X49)|~v4_lattice3(X49)|~l3_lattices(X49)))&(X48=esk9_3(X48,X49,X50)|~r2_hidden(X48,a_2_6_lattice3(X49,X50))|(v2_struct_0(X49)|~v10_lattices(X49)|~v4_lattice3(X49)|~l3_lattices(X49))))&(((m1_subset_1(esk10_3(X48,X49,X50),u1_struct_0(X49))|~r2_hidden(X48,a_2_6_lattice3(X49,X50))|(v2_struct_0(X49)|~v10_lattices(X49)|~v4_lattice3(X49)|~l3_lattices(X49)))&(r3_lattices(X49,esk10_3(X48,X49,X50),esk9_3(X48,X49,X50))|~r2_hidden(X48,a_2_6_lattice3(X49,X50))|(v2_struct_0(X49)|~v10_lattices(X49)|~v4_lattice3(X49)|~l3_lattices(X49))))&(r2_hidden(esk10_3(X48,X49,X50),X50)|~r2_hidden(X48,a_2_6_lattice3(X49,X50))|(v2_struct_0(X49)|~v10_lattices(X49)|~v4_lattice3(X49)|~l3_lattices(X49)))))&(~m1_subset_1(X54,u1_struct_0(X49))|X48!=X54|(~m1_subset_1(X55,u1_struct_0(X49))|~r3_lattices(X49,X55,X54)|~r2_hidden(X55,X53))|r2_hidden(X48,a_2_6_lattice3(X49,X53))|(v2_struct_0(X49)|~v10_lattices(X49)|~v4_lattice3(X49)|~l3_lattices(X49)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_6_lattice3])])])])])])])).
% 0.78/0.96  fof(c_0_26, plain, ![X66, X67, X68]:((r3_lattices(X66,k15_lattice3(X66,X67),k15_lattice3(X66,X68))|~r1_tarski(X67,X68)|(v2_struct_0(X66)|~v10_lattices(X66)|~v4_lattice3(X66)|~l3_lattices(X66)))&(r3_lattices(X66,k16_lattice3(X66,X68),k16_lattice3(X66,X67))|~r1_tarski(X67,X68)|(v2_struct_0(X66)|~v10_lattices(X66)|~v4_lattice3(X66)|~l3_lattices(X66)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t46_lattice3])])])])])).
% 0.78/0.96  fof(c_0_27, plain, ![X69, X70]:((k15_lattice3(X69,X70)=k15_lattice3(X69,a_2_5_lattice3(X69,X70))|(v2_struct_0(X69)|~v10_lattices(X69)|~v4_lattice3(X69)|~l3_lattices(X69)))&(k16_lattice3(X69,X70)=k16_lattice3(X69,a_2_6_lattice3(X69,X70))|(v2_struct_0(X69)|~v10_lattices(X69)|~v4_lattice3(X69)|~l3_lattices(X69)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t47_lattice3])])])])])).
% 0.78/0.96  cnf(c_0_28, plain, (r1_lattices(X1,X2,X3)|v2_struct_0(X1)|X2!=k16_lattice3(X1,X4)|~v4_lattice3(X1)|~r2_hidden(X3,X4)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.78/0.96  cnf(c_0_29, plain, (v2_struct_0(X1)|m1_subset_1(k16_lattice3(X1,X2),u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.78/0.96  cnf(c_0_30, plain, (m1_subset_1(esk9_3(X1,X2,X3),u1_struct_0(X2))|v2_struct_0(X2)|~r2_hidden(X1,a_2_6_lattice3(X2,X3))|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.78/0.96  cnf(c_0_31, plain, (X1=esk9_3(X1,X2,X3)|v2_struct_0(X2)|~r2_hidden(X1,a_2_6_lattice3(X2,X3))|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.78/0.96  cnf(c_0_32, plain, (r2_hidden(X3,a_2_6_lattice3(X2,X5))|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|X3!=X1|~m1_subset_1(X4,u1_struct_0(X2))|~r3_lattices(X2,X4,X1)|~r2_hidden(X4,X5)|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.78/0.96  cnf(c_0_33, plain, (r3_lattices(X1,k15_lattice3(X1,X2),k15_lattice3(X1,X3))|v2_struct_0(X1)|~r1_tarski(X2,X3)|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.78/0.96  cnf(c_0_34, plain, (k15_lattice3(X1,X2)=k15_lattice3(X1,a_2_5_lattice3(X1,X2))|v2_struct_0(X1)|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.78/0.96  fof(c_0_35, plain, ![X38, X39]:(v2_struct_0(X38)|~l3_lattices(X38)|m1_subset_1(k15_lattice3(X38,X39),u1_struct_0(X38))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k15_lattice3])])])).
% 0.78/0.96  fof(c_0_36, plain, ![X17, X19, X20]:(((m1_subset_1(esk2_1(X17),u1_struct_0(X17))|~v13_lattices(X17)|(v2_struct_0(X17)|~l1_lattices(X17)))&((k2_lattices(X17,esk2_1(X17),X19)=esk2_1(X17)|~m1_subset_1(X19,u1_struct_0(X17))|~v13_lattices(X17)|(v2_struct_0(X17)|~l1_lattices(X17)))&(k2_lattices(X17,X19,esk2_1(X17))=esk2_1(X17)|~m1_subset_1(X19,u1_struct_0(X17))|~v13_lattices(X17)|(v2_struct_0(X17)|~l1_lattices(X17)))))&((m1_subset_1(esk3_2(X17,X20),u1_struct_0(X17))|~m1_subset_1(X20,u1_struct_0(X17))|v13_lattices(X17)|(v2_struct_0(X17)|~l1_lattices(X17)))&(k2_lattices(X17,X20,esk3_2(X17,X20))!=X20|k2_lattices(X17,esk3_2(X17,X20),X20)!=X20|~m1_subset_1(X20,u1_struct_0(X17))|v13_lattices(X17)|(v2_struct_0(X17)|~l1_lattices(X17))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d13_lattices])])])])])])).
% 0.78/0.96  fof(c_0_37, plain, ![X33, X34, X35]:((~v6_lattices(X33)|(~m1_subset_1(X34,u1_struct_0(X33))|(~m1_subset_1(X35,u1_struct_0(X33))|k2_lattices(X33,X34,X35)=k2_lattices(X33,X35,X34)))|(v2_struct_0(X33)|~l1_lattices(X33)))&((m1_subset_1(esk6_1(X33),u1_struct_0(X33))|v6_lattices(X33)|(v2_struct_0(X33)|~l1_lattices(X33)))&((m1_subset_1(esk7_1(X33),u1_struct_0(X33))|v6_lattices(X33)|(v2_struct_0(X33)|~l1_lattices(X33)))&(k2_lattices(X33,esk6_1(X33),esk7_1(X33))!=k2_lattices(X33,esk7_1(X33),esk6_1(X33))|v6_lattices(X33)|(v2_struct_0(X33)|~l1_lattices(X33)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d6_lattices])])])])])])).
% 0.78/0.96  fof(c_0_38, plain, ![X14, X15, X16]:((~r1_lattices(X14,X15,X16)|k2_lattices(X14,X15,X16)=X15|~m1_subset_1(X16,u1_struct_0(X14))|~m1_subset_1(X15,u1_struct_0(X14))|(v2_struct_0(X14)|~v8_lattices(X14)|~v9_lattices(X14)|~l3_lattices(X14)))&(k2_lattices(X14,X15,X16)!=X15|r1_lattices(X14,X15,X16)|~m1_subset_1(X16,u1_struct_0(X14))|~m1_subset_1(X15,u1_struct_0(X14))|(v2_struct_0(X14)|~v8_lattices(X14)|~v9_lattices(X14)|~l3_lattices(X14)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t21_lattices])])])])])).
% 0.78/0.96  cnf(c_0_39, plain, (r1_lattices(X1,k16_lattice3(X1,X2),X3)|v2_struct_0(X1)|~v4_lattice3(X1)|~r2_hidden(X3,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_28]), c_0_29])).
% 0.78/0.96  cnf(c_0_40, plain, (k16_lattice3(X1,X2)=k16_lattice3(X1,a_2_6_lattice3(X1,X2))|v2_struct_0(X1)|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.78/0.96  cnf(c_0_41, plain, (m1_subset_1(X1,u1_struct_0(X2))|v2_struct_0(X2)|~v4_lattice3(X2)|~r2_hidden(X1,a_2_6_lattice3(X2,X3))|~v10_lattices(X2)|~l3_lattices(X2)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.78/0.96  fof(c_0_42, plain, ![X7]:(((((((~v2_struct_0(X7)|(v2_struct_0(X7)|~v10_lattices(X7))|~l3_lattices(X7))&(v4_lattices(X7)|(v2_struct_0(X7)|~v10_lattices(X7))|~l3_lattices(X7)))&(v5_lattices(X7)|(v2_struct_0(X7)|~v10_lattices(X7))|~l3_lattices(X7)))&(v6_lattices(X7)|(v2_struct_0(X7)|~v10_lattices(X7))|~l3_lattices(X7)))&(v7_lattices(X7)|(v2_struct_0(X7)|~v10_lattices(X7))|~l3_lattices(X7)))&(v8_lattices(X7)|(v2_struct_0(X7)|~v10_lattices(X7))|~l3_lattices(X7)))&(v9_lattices(X7)|(v2_struct_0(X7)|~v10_lattices(X7))|~l3_lattices(X7))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).
% 0.78/0.96  cnf(c_0_43, plain, (r2_hidden(X1,a_2_6_lattice3(X2,X3))|v2_struct_0(X2)|~r3_lattices(X2,X4,X1)|~v4_lattice3(X2)|~r2_hidden(X4,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))|~v10_lattices(X2)|~l3_lattices(X2)), inference(er,[status(thm)],[c_0_32])).
% 0.78/0.96  cnf(c_0_44, plain, (r3_lattices(X1,k15_lattice3(X1,X2),k15_lattice3(X1,X3))|v2_struct_0(X1)|~v4_lattice3(X1)|~v10_lattices(X1)|~l3_lattices(X1)|~r1_tarski(X2,a_2_5_lattice3(X1,X3))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.78/0.96  cnf(c_0_45, plain, (v2_struct_0(X1)|m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.78/0.96  fof(c_0_46, plain, ![X6]:r1_tarski(k1_xboole_0,X6), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.78/0.96  cnf(c_0_47, plain, (v13_lattices(X1)|v2_struct_0(X1)|k2_lattices(X1,X2,esk3_2(X1,X2))!=X2|k2_lattices(X1,esk3_2(X1,X2),X2)!=X2|~m1_subset_1(X2,u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.78/0.96  cnf(c_0_48, plain, (k2_lattices(X1,X2,X3)=k2_lattices(X1,X3,X2)|v2_struct_0(X1)|~v6_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.78/0.96  cnf(c_0_49, plain, (m1_subset_1(esk3_2(X1,X2),u1_struct_0(X1))|v13_lattices(X1)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.78/0.96  cnf(c_0_50, plain, (k2_lattices(X1,X2,X3)=X2|v2_struct_0(X1)|~r1_lattices(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.78/0.96  cnf(c_0_51, plain, (r1_lattices(X1,k16_lattice3(X1,X2),X3)|v2_struct_0(X1)|~v4_lattice3(X1)|~r2_hidden(X3,a_2_6_lattice3(X1,X2))|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41])).
% 0.78/0.96  cnf(c_0_52, plain, (v8_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.78/0.96  cnf(c_0_53, plain, (v9_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.78/0.96  fof(c_0_54, plain, ![X13]:((l1_lattices(X13)|~l3_lattices(X13))&(l2_lattices(X13)|~l3_lattices(X13))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).
% 0.78/0.96  cnf(c_0_55, plain, (r2_hidden(k15_lattice3(X1,X2),a_2_6_lattice3(X1,X3))|v2_struct_0(X1)|~v4_lattice3(X1)|~r2_hidden(k15_lattice3(X1,X4),X3)|~v10_lattices(X1)|~l3_lattices(X1)|~r1_tarski(X4,a_2_5_lattice3(X1,X2))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45]), c_0_45])).
% 0.78/0.96  cnf(c_0_56, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.78/0.96  fof(c_0_57, plain, ![X64, X65]:((k15_lattice3(X64,k6_domain_1(u1_struct_0(X64),X65))=X65|~m1_subset_1(X65,u1_struct_0(X64))|(v2_struct_0(X64)|~v10_lattices(X64)|~v4_lattice3(X64)|~l3_lattices(X64)))&(k16_lattice3(X64,k6_domain_1(u1_struct_0(X64),X65))=X65|~m1_subset_1(X65,u1_struct_0(X64))|(v2_struct_0(X64)|~v10_lattices(X64)|~v4_lattice3(X64)|~l3_lattices(X64)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t43_lattice3])])])])])).
% 0.78/0.96  cnf(c_0_58, plain, (v13_lattices(X1)|v2_struct_0(X1)|k2_lattices(X1,X2,esk3_2(X1,X2))!=X2|~m1_subset_1(X2,u1_struct_0(X1))|~l1_lattices(X1)|~v6_lattices(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49])).
% 0.78/0.96  cnf(c_0_59, plain, (k2_lattices(X1,k16_lattice3(X1,X2),X3)=k16_lattice3(X1,X2)|v2_struct_0(X1)|~v4_lattice3(X1)|~r2_hidden(X3,a_2_6_lattice3(X1,X2))|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52]), c_0_53]), c_0_41]), c_0_29])).
% 0.78/0.96  cnf(c_0_60, plain, (v6_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.78/0.96  cnf(c_0_61, plain, (l1_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.78/0.96  cnf(c_0_62, plain, (r2_hidden(k15_lattice3(X1,X2),a_2_6_lattice3(X1,X3))|v2_struct_0(X1)|~v4_lattice3(X1)|~r2_hidden(k15_lattice3(X1,k1_xboole_0),X3)|~v10_lattices(X1)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.78/0.96  cnf(c_0_63, plain, (k15_lattice3(X1,k6_domain_1(u1_struct_0(X1),X2))=X2|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.78/0.96  fof(c_0_64, plain, ![X42, X43, X44, X46, X47]:((((m1_subset_1(esk8_3(X42,X43,X44),u1_struct_0(X43))|~r2_hidden(X42,a_2_2_lattice3(X43,X44))|(v2_struct_0(X43)|~v10_lattices(X43)|~v4_lattice3(X43)|~l3_lattices(X43)))&(X42=esk8_3(X42,X43,X44)|~r2_hidden(X42,a_2_2_lattice3(X43,X44))|(v2_struct_0(X43)|~v10_lattices(X43)|~v4_lattice3(X43)|~l3_lattices(X43))))&(r4_lattice3(X43,esk8_3(X42,X43,X44),X44)|~r2_hidden(X42,a_2_2_lattice3(X43,X44))|(v2_struct_0(X43)|~v10_lattices(X43)|~v4_lattice3(X43)|~l3_lattices(X43))))&(~m1_subset_1(X47,u1_struct_0(X43))|X42!=X47|~r4_lattice3(X43,X47,X46)|r2_hidden(X42,a_2_2_lattice3(X43,X46))|(v2_struct_0(X43)|~v10_lattices(X43)|~v4_lattice3(X43)|~l3_lattices(X43)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_2_lattice3])])])])])])])).
% 0.78/0.96  fof(c_0_65, plain, ![X28, X29, X30, X31]:(((r4_lattice3(X28,X30,X29)|X30!=k15_lattice3(X28,X29)|~m1_subset_1(X30,u1_struct_0(X28))|(v2_struct_0(X28)|~v10_lattices(X28)|~v4_lattice3(X28)|~l3_lattices(X28))|(v2_struct_0(X28)|~l3_lattices(X28)))&(~m1_subset_1(X31,u1_struct_0(X28))|(~r4_lattice3(X28,X31,X29)|r1_lattices(X28,X30,X31))|X30!=k15_lattice3(X28,X29)|~m1_subset_1(X30,u1_struct_0(X28))|(v2_struct_0(X28)|~v10_lattices(X28)|~v4_lattice3(X28)|~l3_lattices(X28))|(v2_struct_0(X28)|~l3_lattices(X28))))&((m1_subset_1(esk5_3(X28,X29,X30),u1_struct_0(X28))|~r4_lattice3(X28,X30,X29)|X30=k15_lattice3(X28,X29)|~m1_subset_1(X30,u1_struct_0(X28))|(v2_struct_0(X28)|~v10_lattices(X28)|~v4_lattice3(X28)|~l3_lattices(X28))|(v2_struct_0(X28)|~l3_lattices(X28)))&((r4_lattice3(X28,esk5_3(X28,X29,X30),X29)|~r4_lattice3(X28,X30,X29)|X30=k15_lattice3(X28,X29)|~m1_subset_1(X30,u1_struct_0(X28))|(v2_struct_0(X28)|~v10_lattices(X28)|~v4_lattice3(X28)|~l3_lattices(X28))|(v2_struct_0(X28)|~l3_lattices(X28)))&(~r1_lattices(X28,X30,esk5_3(X28,X29,X30))|~r4_lattice3(X28,X30,X29)|X30=k15_lattice3(X28,X29)|~m1_subset_1(X30,u1_struct_0(X28))|(v2_struct_0(X28)|~v10_lattices(X28)|~v4_lattice3(X28)|~l3_lattices(X28))|(v2_struct_0(X28)|~l3_lattices(X28)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d21_lattice3])])])])])])).
% 0.78/0.96  cnf(c_0_66, plain, (v13_lattices(X1)|v2_struct_0(X1)|~v4_lattice3(X1)|~r2_hidden(esk3_2(X1,k16_lattice3(X1,X2)),a_2_6_lattice3(X1,X2))|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_60]), c_0_61]), c_0_29])).
% 0.78/0.96  cnf(c_0_67, plain, (r2_hidden(X1,a_2_6_lattice3(X2,X3))|v2_struct_0(X2)|~v4_lattice3(X2)|~r2_hidden(k15_lattice3(X2,k1_xboole_0),X3)|~m1_subset_1(X1,u1_struct_0(X2))|~v10_lattices(X2)|~l3_lattices(X2)), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.78/0.96  cnf(c_0_68, plain, (r2_hidden(X3,a_2_2_lattice3(X2,X4))|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|X3!=X1|~r4_lattice3(X2,X1,X4)|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.78/0.96  cnf(c_0_69, plain, (r4_lattice3(X1,X2,X3)|v2_struct_0(X1)|v2_struct_0(X1)|X2!=k15_lattice3(X1,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.78/0.96  cnf(c_0_70, plain, (v13_lattices(X1)|v2_struct_0(X1)|~v4_lattice3(X1)|~r2_hidden(k15_lattice3(X1,k1_xboole_0),X2)|~m1_subset_1(esk3_2(X1,k16_lattice3(X1,X2)),u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.78/0.96  cnf(c_0_71, plain, (r2_hidden(X1,a_2_2_lattice3(X2,X3))|v2_struct_0(X2)|~r4_lattice3(X2,X1,X3)|~v4_lattice3(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~v10_lattices(X2)|~l3_lattices(X2)), inference(er,[status(thm)],[c_0_68])).
% 0.78/0.96  cnf(c_0_72, plain, (v2_struct_0(X1)|r4_lattice3(X1,X2,X3)|X2!=k15_lattice3(X1,X3)|~l3_lattices(X1)|~v10_lattices(X1)|~v4_lattice3(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(cn,[status(thm)],[c_0_69])).
% 0.78/0.96  cnf(c_0_73, plain, (v13_lattices(X1)|v2_struct_0(X1)|~v4_lattice3(X1)|~r2_hidden(k15_lattice3(X1,k1_xboole_0),X2)|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_49]), c_0_61]), c_0_29])).
% 0.78/0.96  cnf(c_0_74, plain, (r2_hidden(X1,a_2_2_lattice3(X2,X3))|v2_struct_0(X2)|X1!=k15_lattice3(X2,X3)|~v4_lattice3(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~v10_lattices(X2)|~l3_lattices(X2)), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.78/0.96  cnf(c_0_75, plain, (v13_lattices(X1)|v2_struct_0(X2)|v2_struct_0(X1)|k15_lattice3(X1,k1_xboole_0)!=k15_lattice3(X2,X3)|~v4_lattice3(X1)|~v4_lattice3(X2)|~m1_subset_1(k15_lattice3(X1,k1_xboole_0),u1_struct_0(X2))|~v10_lattices(X1)|~v10_lattices(X2)|~l3_lattices(X1)|~l3_lattices(X2)), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.78/0.96  cnf(c_0_76, plain, (r2_hidden(k15_lattice3(X1,X2),a_2_6_lattice3(X1,X3))|v2_struct_0(X1)|~v4_lattice3(X1)|~r2_hidden(k15_lattice3(X1,X4),X3)|~v10_lattices(X1)|~l3_lattices(X1)|~r1_tarski(X4,X2)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_33]), c_0_45]), c_0_45])).
% 0.78/0.96  cnf(c_0_77, plain, (v13_lattices(X1)|v2_struct_0(X1)|k15_lattice3(X1,k1_xboole_0)!=k15_lattice3(X1,X2)|~v4_lattice3(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_75, c_0_45])).
% 0.78/0.96  cnf(c_0_78, plain, (r2_hidden(k15_lattice3(X1,X2),a_2_6_lattice3(X1,a_2_6_lattice3(X1,X3)))|v2_struct_0(X1)|~v4_lattice3(X1)|~r2_hidden(k15_lattice3(X1,k1_xboole_0),X3)|~v10_lattices(X1)|~l3_lattices(X1)|~r1_tarski(X4,X2)), inference(spm,[status(thm)],[c_0_76, c_0_62])).
% 0.78/0.96  fof(c_0_79, plain, ![X8, X9, X10]:(((k2_lattices(X8,X9,X10)=X9|~m1_subset_1(X10,u1_struct_0(X8))|X9!=k5_lattices(X8)|~m1_subset_1(X9,u1_struct_0(X8))|~v13_lattices(X8)|(v2_struct_0(X8)|~l1_lattices(X8)))&(k2_lattices(X8,X10,X9)=X9|~m1_subset_1(X10,u1_struct_0(X8))|X9!=k5_lattices(X8)|~m1_subset_1(X9,u1_struct_0(X8))|~v13_lattices(X8)|(v2_struct_0(X8)|~l1_lattices(X8))))&((m1_subset_1(esk1_2(X8,X9),u1_struct_0(X8))|X9=k5_lattices(X8)|~m1_subset_1(X9,u1_struct_0(X8))|~v13_lattices(X8)|(v2_struct_0(X8)|~l1_lattices(X8)))&(k2_lattices(X8,X9,esk1_2(X8,X9))!=X9|k2_lattices(X8,esk1_2(X8,X9),X9)!=X9|X9=k5_lattices(X8)|~m1_subset_1(X9,u1_struct_0(X8))|~v13_lattices(X8)|(v2_struct_0(X8)|~l1_lattices(X8))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattices])])])])])])).
% 0.78/0.96  cnf(c_0_80, plain, (k2_lattices(X1,X2,esk2_1(X1))=esk2_1(X1)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v13_lattices(X1)|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.78/0.96  cnf(c_0_81, plain, (v13_lattices(X1)|v2_struct_0(X1)|~v4_lattice3(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(er,[status(thm)],[c_0_77])).
% 0.78/0.96  cnf(c_0_82, plain, (r2_hidden(k15_lattice3(X1,X2),a_2_6_lattice3(X1,a_2_6_lattice3(X1,X3)))|v2_struct_0(X1)|~v4_lattice3(X1)|~r2_hidden(k15_lattice3(X1,k1_xboole_0),X3)|~v10_lattices(X1)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_78, c_0_56])).
% 0.78/0.96  cnf(c_0_83, plain, (k2_lattices(X1,esk2_1(X1),X2)=esk2_1(X1)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v13_lattices(X1)|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.78/0.96  cnf(c_0_84, plain, (k2_lattices(X1,X2,X3)=X3|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|X3!=k5_lattices(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~v13_lattices(X1)|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_79])).
% 0.78/0.96  cnf(c_0_85, plain, (m1_subset_1(esk2_1(X1),u1_struct_0(X1))|v2_struct_0(X1)|~v13_lattices(X1)|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.78/0.96  fof(c_0_86, plain, ![X12]:(v2_struct_0(X12)|~l1_lattices(X12)|m1_subset_1(k5_lattices(X12),u1_struct_0(X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_lattices])])])).
% 0.78/0.96  cnf(c_0_87, plain, (k16_lattice3(X1,X2)=esk2_1(X1)|v2_struct_0(X1)|~v4_lattice3(X1)|~r2_hidden(esk2_1(X1),a_2_6_lattice3(X1,X2))|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_59]), c_0_61]), c_0_81]), c_0_29])).
% 0.78/0.96  cnf(c_0_88, plain, (r2_hidden(X1,a_2_6_lattice3(X2,a_2_6_lattice3(X2,X3)))|v2_struct_0(X2)|~v4_lattice3(X2)|~r2_hidden(k15_lattice3(X2,k1_xboole_0),X3)|~m1_subset_1(X1,u1_struct_0(X2))|~v10_lattices(X2)|~l3_lattices(X2)), inference(spm,[status(thm)],[c_0_82, c_0_63])).
% 0.78/0.96  cnf(c_0_89, plain, (X1=esk2_1(X2)|v2_struct_0(X2)|X1!=k5_lattices(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~v13_lattices(X2)|~l1_lattices(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_85])).
% 0.78/0.96  cnf(c_0_90, plain, (v2_struct_0(X1)|m1_subset_1(k5_lattices(X1),u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_86])).
% 0.78/0.96  cnf(c_0_91, plain, (k16_lattice3(X1,a_2_6_lattice3(X1,X2))=esk2_1(X1)|v2_struct_0(X1)|~v4_lattice3(X1)|~r2_hidden(k15_lattice3(X1,k1_xboole_0),X2)|~m1_subset_1(esk2_1(X1),u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_87, c_0_88])).
% 0.78/0.96  cnf(c_0_92, plain, (esk2_1(X1)=k5_lattices(X1)|v2_struct_0(X1)|~v13_lattices(X1)|~l1_lattices(X1)), inference(spm,[status(thm)],[c_0_89, c_0_90])).
% 0.78/0.96  cnf(c_0_93, plain, (k16_lattice3(X1,a_2_6_lattice3(X1,X2))=esk2_1(X1)|v2_struct_0(X1)|~v4_lattice3(X1)|~r2_hidden(k15_lattice3(X1,k1_xboole_0),X2)|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_85]), c_0_61]), c_0_81])).
% 0.78/0.96  cnf(c_0_94, plain, (r2_hidden(k15_lattice3(X1,X2),a_2_6_lattice3(X1,a_2_2_lattice3(X3,X4)))|v2_struct_0(X3)|v2_struct_0(X1)|k15_lattice3(X1,X5)!=k15_lattice3(X3,X4)|~v4_lattice3(X1)|~v4_lattice3(X3)|~m1_subset_1(k15_lattice3(X1,X5),u1_struct_0(X3))|~v10_lattices(X1)|~v10_lattices(X3)|~l3_lattices(X1)|~l3_lattices(X3)|~r1_tarski(X5,X2)), inference(spm,[status(thm)],[c_0_76, c_0_74])).
% 0.78/0.96  cnf(c_0_95, plain, (k16_lattice3(X1,a_2_6_lattice3(X1,X2))=k5_lattices(X1)|v2_struct_0(X1)|~v4_lattice3(X1)|~r2_hidden(k15_lattice3(X1,k1_xboole_0),X2)|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_61]), c_0_81])).
% 0.78/0.96  cnf(c_0_96, plain, (r2_hidden(k15_lattice3(X1,X2),a_2_6_lattice3(X1,a_2_2_lattice3(X1,X3)))|v2_struct_0(X1)|k15_lattice3(X1,X4)!=k15_lattice3(X1,X3)|~v4_lattice3(X1)|~v10_lattices(X1)|~l3_lattices(X1)|~r1_tarski(X4,X2)), inference(spm,[status(thm)],[c_0_94, c_0_45])).
% 0.78/0.96  cnf(c_0_97, plain, (k16_lattice3(X1,X2)=k5_lattices(X1)|v2_struct_0(X1)|~v4_lattice3(X1)|~r2_hidden(k15_lattice3(X1,k1_xboole_0),X2)|~v10_lattices(X1)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_40, c_0_95])).
% 0.78/0.96  cnf(c_0_98, plain, (r2_hidden(k15_lattice3(X1,X2),a_2_6_lattice3(X1,a_2_2_lattice3(X1,X3)))|v2_struct_0(X1)|k15_lattice3(X1,k1_xboole_0)!=k15_lattice3(X1,X3)|~v4_lattice3(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_96, c_0_56])).
% 0.78/0.96  fof(c_0_99, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>((((~(v2_struct_0(X1))&v10_lattices(X1))&v13_lattices(X1))&l3_lattices(X1))&k5_lattices(X1)=k15_lattice3(X1,k1_xboole_0)))), inference(assume_negation,[status(cth)],[t50_lattice3])).
% 0.78/0.96  fof(c_0_100, plain, ![X62, X63]:(v2_struct_0(X62)|~v10_lattices(X62)|~v4_lattice3(X62)|~l3_lattices(X62)|k15_lattice3(X62,X63)=k16_lattice3(X62,a_2_2_lattice3(X62,X63))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t37_lattice3])])])])).
% 0.78/0.96  cnf(c_0_101, plain, (k16_lattice3(X1,a_2_6_lattice3(X1,a_2_2_lattice3(X1,X2)))=k5_lattices(X1)|v2_struct_0(X1)|k15_lattice3(X1,k1_xboole_0)!=k15_lattice3(X1,X2)|~v4_lattice3(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_97, c_0_98])).
% 0.78/0.96  fof(c_0_102, negated_conjecture, ((((~v2_struct_0(esk13_0)&v10_lattices(esk13_0))&v4_lattice3(esk13_0))&l3_lattices(esk13_0))&(v2_struct_0(esk13_0)|~v10_lattices(esk13_0)|~v13_lattices(esk13_0)|~l3_lattices(esk13_0)|k5_lattices(esk13_0)!=k15_lattice3(esk13_0,k1_xboole_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_99])])])])).
% 0.78/0.96  cnf(c_0_103, plain, (v2_struct_0(X1)|k15_lattice3(X1,X2)=k16_lattice3(X1,a_2_2_lattice3(X1,X2))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_100])).
% 0.78/0.96  cnf(c_0_104, plain, (k16_lattice3(X1,a_2_2_lattice3(X1,X2))=k5_lattices(X1)|v2_struct_0(X1)|k15_lattice3(X1,k1_xboole_0)!=k15_lattice3(X1,X2)|~v4_lattice3(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_40, c_0_101])).
% 0.78/0.96  cnf(c_0_105, negated_conjecture, (v2_struct_0(esk13_0)|~v10_lattices(esk13_0)|~v13_lattices(esk13_0)|~l3_lattices(esk13_0)|k5_lattices(esk13_0)!=k15_lattice3(esk13_0,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_102])).
% 0.78/0.96  cnf(c_0_106, negated_conjecture, (l3_lattices(esk13_0)), inference(split_conjunct,[status(thm)],[c_0_102])).
% 0.78/0.96  cnf(c_0_107, negated_conjecture, (v10_lattices(esk13_0)), inference(split_conjunct,[status(thm)],[c_0_102])).
% 0.78/0.96  cnf(c_0_108, negated_conjecture, (~v2_struct_0(esk13_0)), inference(split_conjunct,[status(thm)],[c_0_102])).
% 0.78/0.96  cnf(c_0_109, plain, (k15_lattice3(X1,X2)=k5_lattices(X1)|v2_struct_0(X1)|k15_lattice3(X1,k1_xboole_0)!=k15_lattice3(X1,X2)|~v4_lattice3(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_103, c_0_104])).
% 0.78/0.96  cnf(c_0_110, negated_conjecture, (k15_lattice3(esk13_0,k1_xboole_0)!=k5_lattices(esk13_0)|~v13_lattices(esk13_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_105, c_0_106]), c_0_107])]), c_0_108])).
% 0.78/0.96  cnf(c_0_111, plain, (k15_lattice3(X1,k1_xboole_0)=k5_lattices(X1)|v2_struct_0(X1)|~v4_lattice3(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(er,[status(thm)],[c_0_109])).
% 0.78/0.96  cnf(c_0_112, negated_conjecture, (v4_lattice3(esk13_0)), inference(split_conjunct,[status(thm)],[c_0_102])).
% 0.78/0.96  cnf(c_0_113, negated_conjecture, (~v13_lattices(esk13_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_111]), c_0_112]), c_0_107]), c_0_106])]), c_0_108])).
% 0.78/0.96  cnf(c_0_114, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_81]), c_0_112]), c_0_107]), c_0_106])]), c_0_108]), ['proof']).
% 0.78/0.96  # SZS output end CNFRefutation
% 0.78/0.96  # Proof object total steps             : 115
% 0.78/0.96  # Proof object clause steps            : 74
% 0.78/0.96  # Proof object formula steps           : 41
% 0.78/0.96  # Proof object conjectures             : 11
% 0.78/0.96  # Proof object clause conjectures      : 8
% 0.78/0.96  # Proof object formula conjectures     : 3
% 0.78/0.96  # Proof object initial clauses used    : 33
% 0.78/0.96  # Proof object initial formulas used   : 20
% 0.78/0.96  # Proof object generating inferences   : 37
% 0.78/0.96  # Proof object simplifying inferences  : 41
% 0.78/0.96  # Training examples: 0 positive, 0 negative
% 0.78/0.96  # Parsed axioms                        : 21
% 0.78/0.96  # Removed by relevancy pruning/SinE    : 0
% 0.78/0.96  # Initial clauses                      : 67
% 0.78/0.96  # Removed in clause preprocessing      : 1
% 0.78/0.96  # Initial clauses in saturation        : 66
% 0.78/0.96  # Processed clauses                    : 5999
% 0.78/0.96  # ...of these trivial                  : 97
% 0.78/0.96  # ...subsumed                          : 4166
% 0.78/0.96  # ...remaining for further processing  : 1736
% 0.78/0.96  # Other redundant clauses eliminated   : 34
% 0.78/0.96  # Clauses deleted for lack of memory   : 0
% 0.78/0.96  # Backward-subsumed                    : 325
% 0.78/0.96  # Backward-rewritten                   : 0
% 0.78/0.96  # Generated clauses                    : 20131
% 0.78/0.96  # ...of the previous two non-trivial   : 19769
% 0.78/0.96  # Contextual simplify-reflections      : 532
% 0.78/0.96  # Paramodulations                      : 20048
% 0.78/0.96  # Factorizations                       : 0
% 0.78/0.96  # Equation resolutions                 : 83
% 0.78/0.96  # Propositional unsat checks           : 0
% 0.78/0.96  #    Propositional check models        : 0
% 0.78/0.96  #    Propositional check unsatisfiable : 0
% 0.78/0.96  #    Propositional clauses             : 0
% 0.78/0.96  #    Propositional clauses after purity: 0
% 0.78/0.96  #    Propositional unsat core size     : 0
% 0.78/0.96  #    Propositional preprocessing time  : 0.000
% 0.78/0.96  #    Propositional encoding time       : 0.000
% 0.78/0.96  #    Propositional solver time         : 0.000
% 0.78/0.96  #    Success case prop preproc time    : 0.000
% 0.78/0.96  #    Success case prop encoding time   : 0.000
% 0.78/0.96  #    Success case prop solver time     : 0.000
% 0.78/0.96  # Current number of processed clauses  : 1343
% 0.78/0.96  #    Positive orientable unit clauses  : 4
% 0.78/0.96  #    Positive unorientable unit clauses: 0
% 0.78/0.96  #    Negative unit clauses             : 2
% 0.78/0.96  #    Non-unit-clauses                  : 1337
% 0.78/0.96  # Current number of unprocessed clauses: 13401
% 0.78/0.96  # ...number of literals in the above   : 127349
% 0.78/0.96  # Current number of archived formulas  : 0
% 0.78/0.96  # Current number of archived clauses   : 391
% 0.78/0.96  # Clause-clause subsumption calls (NU) : 510891
% 0.78/0.96  # Rec. Clause-clause subsumption calls : 10079
% 0.78/0.96  # Non-unit clause-clause subsumptions  : 5023
% 0.78/0.96  # Unit Clause-clause subsumption calls : 446
% 0.78/0.96  # Rewrite failures with RHS unbound    : 0
% 0.78/0.96  # BW rewrite match attempts            : 0
% 0.78/0.96  # BW rewrite match successes           : 0
% 0.78/0.96  # Condensation attempts                : 0
% 0.78/0.96  # Condensation successes               : 0
% 0.78/0.96  # Termbank termtop insertions          : 617934
% 0.78/0.96  
% 0.78/0.96  # -------------------------------------------------
% 0.78/0.96  # User time                : 0.592 s
% 0.78/0.96  # System time              : 0.022 s
% 0.78/0.96  # Total time               : 0.614 s
% 0.78/0.96  # Maximum resident set size: 1608 pages
%------------------------------------------------------------------------------
