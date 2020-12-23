%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:06 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  141 (2413 expanded)
%              Number of clauses        :   96 ( 850 expanded)
%              Number of leaves         :   22 ( 582 expanded)
%              Depth                    :   19
%              Number of atoms          :  808 (15697 expanded)
%              Number of equality atoms :   93 (1629 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_lattice3)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_2_lattice3)).

fof(dt_k16_lattice3,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => m1_subset_1(k16_lattice3(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k16_lattice3)).

fof(dt_k15_lattice3,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k15_lattice3)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d21_lattice3)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_6_lattice3)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_lattice3)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_lattice3)).

fof(dt_k5_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_lattices(X1) )
     => m1_subset_1(k5_lattices(X1),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_lattices)).

fof(dt_l3_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( l1_lattices(X1)
        & l2_lattices(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_lattice3)).

fof(t47_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v4_lattice3(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( k15_lattice3(X1,X2) = k15_lattice3(X1,a_2_5_lattice3(X1,X2))
          & k16_lattice3(X1,X2) = k16_lattice3(X1,a_2_6_lattice3(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_lattice3)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_lattice3)).

fof(t37_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v4_lattice3(X1)
        & l3_lattices(X1) )
     => ! [X2] : k15_lattice3(X1,X2) = k16_lattice3(X1,a_2_2_lattice3(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_lattice3)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_lattices)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_lattices)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_lattices)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_lattices)).

fof(c_0_22,negated_conjecture,(
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

fof(c_0_23,plain,(
    ! [X53,X54,X55,X57,X58] :
      ( ( m1_subset_1(esk9_3(X53,X54,X55),u1_struct_0(X54))
        | ~ r2_hidden(X53,a_2_2_lattice3(X54,X55))
        | v2_struct_0(X54)
        | ~ v10_lattices(X54)
        | ~ v4_lattice3(X54)
        | ~ l3_lattices(X54) )
      & ( X53 = esk9_3(X53,X54,X55)
        | ~ r2_hidden(X53,a_2_2_lattice3(X54,X55))
        | v2_struct_0(X54)
        | ~ v10_lattices(X54)
        | ~ v4_lattice3(X54)
        | ~ l3_lattices(X54) )
      & ( r4_lattice3(X54,esk9_3(X53,X54,X55),X55)
        | ~ r2_hidden(X53,a_2_2_lattice3(X54,X55))
        | v2_struct_0(X54)
        | ~ v10_lattices(X54)
        | ~ v4_lattice3(X54)
        | ~ l3_lattices(X54) )
      & ( ~ m1_subset_1(X58,u1_struct_0(X54))
        | X53 != X58
        | ~ r4_lattice3(X54,X58,X57)
        | r2_hidden(X53,a_2_2_lattice3(X54,X57))
        | v2_struct_0(X54)
        | ~ v10_lattices(X54)
        | ~ v4_lattice3(X54)
        | ~ l3_lattices(X54) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_2_lattice3])])])])])])])).

fof(c_0_24,plain,(
    ! [X51,X52] :
      ( v2_struct_0(X51)
      | ~ l3_lattices(X51)
      | m1_subset_1(k16_lattice3(X51,X52),u1_struct_0(X51)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k16_lattice3])])])).

fof(c_0_25,negated_conjecture,
    ( ~ v2_struct_0(esk16_0)
    & v10_lattices(esk16_0)
    & v4_lattice3(esk16_0)
    & l3_lattices(esk16_0)
    & ( v2_struct_0(esk16_0)
      | ~ v10_lattices(esk16_0)
      | ~ v13_lattices(esk16_0)
      | ~ l3_lattices(esk16_0)
      | k5_lattices(esk16_0) != k15_lattice3(esk16_0,k1_xboole_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_22])])])])).

cnf(c_0_26,plain,
    ( r2_hidden(X3,a_2_2_lattice3(X2,X4))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | X3 != X1
    | ~ r4_lattice3(X2,X1,X4)
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_27,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k16_lattice3(X1,X2),u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_28,negated_conjecture,
    ( l3_lattices(esk16_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_29,negated_conjecture,
    ( ~ v2_struct_0(esk16_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_30,plain,(
    ! [X49,X50] :
      ( v2_struct_0(X49)
      | ~ l3_lattices(X49)
      | m1_subset_1(k15_lattice3(X49,X50),u1_struct_0(X49)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k15_lattice3])])])).

fof(c_0_31,plain,(
    ! [X39,X40,X41,X42] :
      ( ( r4_lattice3(X39,X41,X40)
        | X41 != k15_lattice3(X39,X40)
        | ~ m1_subset_1(X41,u1_struct_0(X39))
        | v2_struct_0(X39)
        | ~ v10_lattices(X39)
        | ~ v4_lattice3(X39)
        | ~ l3_lattices(X39)
        | v2_struct_0(X39)
        | ~ l3_lattices(X39) )
      & ( ~ m1_subset_1(X42,u1_struct_0(X39))
        | ~ r4_lattice3(X39,X42,X40)
        | r1_lattices(X39,X41,X42)
        | X41 != k15_lattice3(X39,X40)
        | ~ m1_subset_1(X41,u1_struct_0(X39))
        | v2_struct_0(X39)
        | ~ v10_lattices(X39)
        | ~ v4_lattice3(X39)
        | ~ l3_lattices(X39)
        | v2_struct_0(X39)
        | ~ l3_lattices(X39) )
      & ( m1_subset_1(esk6_3(X39,X40,X41),u1_struct_0(X39))
        | ~ r4_lattice3(X39,X41,X40)
        | X41 = k15_lattice3(X39,X40)
        | ~ m1_subset_1(X41,u1_struct_0(X39))
        | v2_struct_0(X39)
        | ~ v10_lattices(X39)
        | ~ v4_lattice3(X39)
        | ~ l3_lattices(X39)
        | v2_struct_0(X39)
        | ~ l3_lattices(X39) )
      & ( r4_lattice3(X39,esk6_3(X39,X40,X41),X40)
        | ~ r4_lattice3(X39,X41,X40)
        | X41 = k15_lattice3(X39,X40)
        | ~ m1_subset_1(X41,u1_struct_0(X39))
        | v2_struct_0(X39)
        | ~ v10_lattices(X39)
        | ~ v4_lattice3(X39)
        | ~ l3_lattices(X39)
        | v2_struct_0(X39)
        | ~ l3_lattices(X39) )
      & ( ~ r1_lattices(X39,X41,esk6_3(X39,X40,X41))
        | ~ r4_lattice3(X39,X41,X40)
        | X41 = k15_lattice3(X39,X40)
        | ~ m1_subset_1(X41,u1_struct_0(X39))
        | v2_struct_0(X39)
        | ~ v10_lattices(X39)
        | ~ v4_lattice3(X39)
        | ~ l3_lattices(X39)
        | v2_struct_0(X39)
        | ~ l3_lattices(X39) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d21_lattice3])])])])])])).

fof(c_0_32,plain,(
    ! [X67,X68,X69,X72,X73,X74] :
      ( ( m1_subset_1(esk12_3(X67,X68,X69),u1_struct_0(X68))
        | ~ r2_hidden(X67,a_2_6_lattice3(X68,X69))
        | v2_struct_0(X68)
        | ~ v10_lattices(X68)
        | ~ v4_lattice3(X68)
        | ~ l3_lattices(X68) )
      & ( X67 = esk12_3(X67,X68,X69)
        | ~ r2_hidden(X67,a_2_6_lattice3(X68,X69))
        | v2_struct_0(X68)
        | ~ v10_lattices(X68)
        | ~ v4_lattice3(X68)
        | ~ l3_lattices(X68) )
      & ( m1_subset_1(esk13_3(X67,X68,X69),u1_struct_0(X68))
        | ~ r2_hidden(X67,a_2_6_lattice3(X68,X69))
        | v2_struct_0(X68)
        | ~ v10_lattices(X68)
        | ~ v4_lattice3(X68)
        | ~ l3_lattices(X68) )
      & ( r3_lattices(X68,esk13_3(X67,X68,X69),esk12_3(X67,X68,X69))
        | ~ r2_hidden(X67,a_2_6_lattice3(X68,X69))
        | v2_struct_0(X68)
        | ~ v10_lattices(X68)
        | ~ v4_lattice3(X68)
        | ~ l3_lattices(X68) )
      & ( r2_hidden(esk13_3(X67,X68,X69),X69)
        | ~ r2_hidden(X67,a_2_6_lattice3(X68,X69))
        | v2_struct_0(X68)
        | ~ v10_lattices(X68)
        | ~ v4_lattice3(X68)
        | ~ l3_lattices(X68) )
      & ( ~ m1_subset_1(X73,u1_struct_0(X68))
        | X67 != X73
        | ~ m1_subset_1(X74,u1_struct_0(X68))
        | ~ r3_lattices(X68,X74,X73)
        | ~ r2_hidden(X74,X72)
        | r2_hidden(X67,a_2_6_lattice3(X68,X72))
        | v2_struct_0(X68)
        | ~ v10_lattices(X68)
        | ~ v4_lattice3(X68)
        | ~ l3_lattices(X68) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_6_lattice3])])])])])])])).

fof(c_0_33,plain,(
    ! [X85,X86,X87] :
      ( ( r3_lattices(X85,k15_lattice3(X85,X86),k15_lattice3(X85,X87))
        | ~ r1_tarski(X86,X87)
        | v2_struct_0(X85)
        | ~ v10_lattices(X85)
        | ~ v4_lattice3(X85)
        | ~ l3_lattices(X85) )
      & ( r3_lattices(X85,k16_lattice3(X85,X87),k16_lattice3(X85,X86))
        | ~ r1_tarski(X86,X87)
        | v2_struct_0(X85)
        | ~ v10_lattices(X85)
        | ~ v4_lattice3(X85)
        | ~ l3_lattices(X85) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t46_lattice3])])])])])).

fof(c_0_34,plain,(
    ! [X14] : r1_tarski(k1_xboole_0,X14) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_35,plain,(
    ! [X6,X7,X8,X9,X10] :
      ( ( ~ r1_tarski(X6,X7)
        | ~ r2_hidden(X8,X6)
        | r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_2(X9,X10),X9)
        | r1_tarski(X9,X10) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | r1_tarski(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_36,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,a_2_2_lattice3(X1,X3))
    | ~ r4_lattice3(X1,X2,X3)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(er,[status(thm)],[c_0_26])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(k16_lattice3(esk16_0,X1),u1_struct_0(esk16_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])).

cnf(c_0_38,negated_conjecture,
    ( v4_lattice3(esk16_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_39,negated_conjecture,
    ( v10_lattices(esk16_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_40,plain,(
    ! [X83,X84] :
      ( ( X84 = k15_lattice3(X83,a_2_3_lattice3(X83,X84))
        | ~ m1_subset_1(X84,u1_struct_0(X83))
        | v2_struct_0(X83)
        | ~ v10_lattices(X83)
        | ~ v4_lattice3(X83)
        | ~ l3_lattices(X83) )
      & ( X84 = k16_lattice3(X83,a_2_4_lattice3(X83,X84))
        | ~ m1_subset_1(X84,u1_struct_0(X83))
        | v2_struct_0(X83)
        | ~ v10_lattices(X83)
        | ~ v4_lattice3(X83)
        | ~ l3_lattices(X83) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t45_lattice3])])])])])).

cnf(c_0_41,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_42,plain,
    ( r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | v2_struct_0(X1)
    | X2 != k15_lattice3(X1,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_43,plain,(
    ! [X23] :
      ( v2_struct_0(X23)
      | ~ l1_lattices(X23)
      | m1_subset_1(k5_lattices(X23),u1_struct_0(X23)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_lattices])])])).

fof(c_0_44,plain,(
    ! [X24] :
      ( ( l1_lattices(X24)
        | ~ l3_lattices(X24) )
      & ( l2_lattices(X24)
        | ~ l3_lattices(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).

fof(c_0_45,plain,(
    ! [X75,X76,X77,X78,X79] :
      ( ( r3_lattice3(X75,X76,X77)
        | X76 != k16_lattice3(X75,X77)
        | ~ m1_subset_1(X76,u1_struct_0(X75))
        | v2_struct_0(X75)
        | ~ v10_lattices(X75)
        | ~ v4_lattice3(X75)
        | ~ l3_lattices(X75) )
      & ( ~ m1_subset_1(X78,u1_struct_0(X75))
        | ~ r3_lattice3(X75,X78,X77)
        | r3_lattices(X75,X78,X76)
        | X76 != k16_lattice3(X75,X77)
        | ~ m1_subset_1(X76,u1_struct_0(X75))
        | v2_struct_0(X75)
        | ~ v10_lattices(X75)
        | ~ v4_lattice3(X75)
        | ~ l3_lattices(X75) )
      & ( m1_subset_1(esk14_3(X75,X76,X79),u1_struct_0(X75))
        | ~ r3_lattice3(X75,X76,X79)
        | X76 = k16_lattice3(X75,X79)
        | ~ m1_subset_1(X76,u1_struct_0(X75))
        | v2_struct_0(X75)
        | ~ v10_lattices(X75)
        | ~ v4_lattice3(X75)
        | ~ l3_lattices(X75) )
      & ( r3_lattice3(X75,esk14_3(X75,X76,X79),X79)
        | ~ r3_lattice3(X75,X76,X79)
        | X76 = k16_lattice3(X75,X79)
        | ~ m1_subset_1(X76,u1_struct_0(X75))
        | v2_struct_0(X75)
        | ~ v10_lattices(X75)
        | ~ v4_lattice3(X75)
        | ~ l3_lattices(X75) )
      & ( ~ r3_lattices(X75,esk14_3(X75,X76,X79),X76)
        | ~ r3_lattice3(X75,X76,X79)
        | X76 = k16_lattice3(X75,X79)
        | ~ m1_subset_1(X76,u1_struct_0(X75))
        | v2_struct_0(X75)
        | ~ v10_lattices(X75)
        | ~ v4_lattice3(X75)
        | ~ l3_lattices(X75) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_lattice3])])])])])])])).

cnf(c_0_46,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_47,plain,
    ( r3_lattices(X1,k15_lattice3(X1,X2),k15_lattice3(X1,X3))
    | v2_struct_0(X1)
    | ~ r1_tarski(X2,X3)
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_48,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_49,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(k16_lattice3(esk16_0,X1),a_2_2_lattice3(esk16_0,X2))
    | ~ r4_lattice3(esk16_0,k16_lattice3(esk16_0,X1),X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38]),c_0_39]),c_0_28])]),c_0_29])).

cnf(c_0_51,plain,
    ( X1 = k16_lattice3(X2,a_2_4_lattice3(X2,X1))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(k15_lattice3(esk16_0,X1),u1_struct_0(esk16_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_28]),c_0_29])).

cnf(c_0_53,plain,
    ( v2_struct_0(X1)
    | r4_lattice3(X1,X2,X3)
    | X2 != k15_lattice3(X1,X3)
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(cn,[status(thm)],[c_0_42])).

cnf(c_0_54,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_55,plain,
    ( l1_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_56,plain,
    ( r3_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | X2 != k16_lattice3(X1,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

fof(c_0_57,plain,(
    ! [X88,X89] :
      ( ( k15_lattice3(X88,X89) = k15_lattice3(X88,a_2_5_lattice3(X88,X89))
        | v2_struct_0(X88)
        | ~ v10_lattices(X88)
        | ~ v4_lattice3(X88)
        | ~ l3_lattices(X88) )
      & ( k16_lattice3(X88,X89) = k16_lattice3(X88,a_2_6_lattice3(X88,X89))
        | v2_struct_0(X88)
        | ~ v10_lattices(X88)
        | ~ v4_lattice3(X88)
        | ~ l3_lattices(X88) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t47_lattice3])])])])])).

cnf(c_0_58,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,a_2_6_lattice3(X1,X3))
    | ~ r3_lattices(X1,X4,X2)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ r2_hidden(X4,X3) ),
    inference(er,[status(thm)],[c_0_46])).

cnf(c_0_59,plain,
    ( r3_lattices(X1,k15_lattice3(X1,k1_xboole_0),k15_lattice3(X1,X2))
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(k16_lattice3(esk16_0,X1),X2)
    | ~ r4_lattice3(esk16_0,k16_lattice3(esk16_0,X1),X3)
    | ~ r1_tarski(a_2_2_lattice3(esk16_0,X3),X2) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_61,negated_conjecture,
    ( k16_lattice3(esk16_0,a_2_4_lattice3(esk16_0,k15_lattice3(esk16_0,X1))) = k15_lattice3(esk16_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_38]),c_0_39]),c_0_28])]),c_0_29])).

cnf(c_0_62,plain,
    ( r4_lattice3(X1,k15_lattice3(X1,X2),X2)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_53]),c_0_41])).

fof(c_0_63,plain,(
    ! [X12,X13] :
      ( ( r1_tarski(X12,X13)
        | X12 != X13 )
      & ( r1_tarski(X13,X12)
        | X12 != X13 )
      & ( ~ r1_tarski(X12,X13)
        | ~ r1_tarski(X13,X12)
        | X12 = X13 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_64,plain,(
    ! [X33,X34,X35,X36,X37] :
      ( ( ~ r3_lattice3(X33,X34,X35)
        | ~ m1_subset_1(X36,u1_struct_0(X33))
        | ~ r2_hidden(X36,X35)
        | r1_lattices(X33,X34,X36)
        | ~ m1_subset_1(X34,u1_struct_0(X33))
        | v2_struct_0(X33)
        | ~ l3_lattices(X33) )
      & ( m1_subset_1(esk5_3(X33,X34,X37),u1_struct_0(X33))
        | r3_lattice3(X33,X34,X37)
        | ~ m1_subset_1(X34,u1_struct_0(X33))
        | v2_struct_0(X33)
        | ~ l3_lattices(X33) )
      & ( r2_hidden(esk5_3(X33,X34,X37),X37)
        | r3_lattice3(X33,X34,X37)
        | ~ m1_subset_1(X34,u1_struct_0(X33))
        | v2_struct_0(X33)
        | ~ l3_lattices(X33) )
      & ( ~ r1_lattices(X33,X34,esk5_3(X33,X34,X37))
        | r3_lattice3(X33,X34,X37)
        | ~ m1_subset_1(X34,u1_struct_0(X33))
        | v2_struct_0(X33)
        | ~ l3_lattices(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattice3])])])])])])])).

cnf(c_0_65,plain,
    ( m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_66,plain,
    ( r3_lattice3(X1,k16_lattice3(X1,X2),X2)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_56]),c_0_27])).

cnf(c_0_67,plain,
    ( k16_lattice3(X1,X2) = k16_lattice3(X1,a_2_6_lattice3(X1,X2))
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

fof(c_0_68,plain,(
    ! [X81,X82] :
      ( v2_struct_0(X81)
      | ~ v10_lattices(X81)
      | ~ v4_lattice3(X81)
      | ~ l3_lattices(X81)
      | k15_lattice3(X81,X82) = k16_lattice3(X81,a_2_2_lattice3(X81,X82)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t37_lattice3])])])])).

cnf(c_0_69,negated_conjecture,
    ( r2_hidden(X1,a_2_6_lattice3(esk16_0,X2))
    | ~ r3_lattices(esk16_0,k15_lattice3(esk16_0,X3),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk16_0))
    | ~ r2_hidden(k15_lattice3(esk16_0,X3),X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_52]),c_0_38]),c_0_39]),c_0_28])]),c_0_29])).

cnf(c_0_70,negated_conjecture,
    ( r3_lattices(esk16_0,k15_lattice3(esk16_0,k1_xboole_0),k15_lattice3(esk16_0,X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_38]),c_0_39]),c_0_28])]),c_0_29])).

cnf(c_0_71,negated_conjecture,
    ( r2_hidden(k15_lattice3(esk16_0,X1),X2)
    | ~ r4_lattice3(esk16_0,k15_lattice3(esk16_0,X1),X3)
    | ~ r1_tarski(a_2_2_lattice3(esk16_0,X3),X2) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_72,negated_conjecture,
    ( r4_lattice3(esk16_0,k15_lattice3(esk16_0,X1),X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_38]),c_0_39]),c_0_28])]),c_0_29])).

cnf(c_0_73,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_74,plain,
    ( r1_lattices(X1,X2,X4)
    | v2_struct_0(X1)
    | ~ r3_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_75,negated_conjecture,
    ( m1_subset_1(k5_lattices(esk16_0),u1_struct_0(esk16_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_28]),c_0_29])).

cnf(c_0_76,negated_conjecture,
    ( r3_lattice3(esk16_0,k16_lattice3(esk16_0,X1),X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_38]),c_0_39]),c_0_28])]),c_0_29])).

cnf(c_0_77,negated_conjecture,
    ( k16_lattice3(esk16_0,a_2_6_lattice3(esk16_0,X1)) = k16_lattice3(esk16_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_38]),c_0_39]),c_0_28])]),c_0_29])).

cnf(c_0_78,plain,
    ( v2_struct_0(X1)
    | k15_lattice3(X1,X2) = k16_lattice3(X1,a_2_2_lattice3(X1,X2))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_79,plain,
    ( X1 = k15_lattice3(X2,a_2_3_lattice3(X2,X1))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_80,negated_conjecture,
    ( r2_hidden(k15_lattice3(esk16_0,X1),a_2_6_lattice3(esk16_0,X2))
    | ~ r2_hidden(k15_lattice3(esk16_0,k1_xboole_0),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_52])])).

cnf(c_0_81,negated_conjecture,
    ( r2_hidden(k15_lattice3(esk16_0,X1),X2)
    | ~ r1_tarski(a_2_2_lattice3(esk16_0,X1),X2) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_82,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_73])).

cnf(c_0_83,negated_conjecture,
    ( r1_lattices(esk16_0,X1,k5_lattices(esk16_0))
    | ~ r3_lattice3(esk16_0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk16_0))
    | ~ r2_hidden(k5_lattices(esk16_0),X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_28])]),c_0_29])).

cnf(c_0_84,negated_conjecture,
    ( r3_lattice3(esk16_0,k16_lattice3(esk16_0,X1),a_2_6_lattice3(esk16_0,X1)) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_85,negated_conjecture,
    ( k16_lattice3(esk16_0,a_2_2_lattice3(esk16_0,X1)) = k15_lattice3(esk16_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_38]),c_0_39]),c_0_28])]),c_0_29])).

cnf(c_0_86,negated_conjecture,
    ( k15_lattice3(esk16_0,a_2_3_lattice3(esk16_0,k5_lattices(esk16_0))) = k5_lattices(esk16_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_75]),c_0_38]),c_0_39]),c_0_28])]),c_0_29])).

cnf(c_0_87,plain,
    ( k15_lattice3(X1,X2) = k15_lattice3(X1,a_2_5_lattice3(X1,X2))
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_88,negated_conjecture,
    ( r2_hidden(k15_lattice3(esk16_0,X1),X2)
    | ~ r2_hidden(k15_lattice3(esk16_0,k1_xboole_0),X3)
    | ~ r1_tarski(a_2_6_lattice3(esk16_0,X3),X2) ),
    inference(spm,[status(thm)],[c_0_49,c_0_80])).

cnf(c_0_89,negated_conjecture,
    ( r2_hidden(k15_lattice3(esk16_0,X1),a_2_2_lattice3(esk16_0,X1)) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_90,negated_conjecture,
    ( r1_lattices(esk16_0,k15_lattice3(esk16_0,X1),k5_lattices(esk16_0))
    | ~ r3_lattice3(esk16_0,k15_lattice3(esk16_0,X1),X2)
    | ~ r2_hidden(k5_lattices(esk16_0),X2) ),
    inference(spm,[status(thm)],[c_0_83,c_0_52])).

cnf(c_0_91,negated_conjecture,
    ( r3_lattice3(esk16_0,k15_lattice3(esk16_0,X1),a_2_6_lattice3(esk16_0,a_2_2_lattice3(esk16_0,X1))) ),
    inference(spm,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_92,negated_conjecture,
    ( r3_lattices(esk16_0,k15_lattice3(esk16_0,k1_xboole_0),k5_lattices(esk16_0)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_86])).

cnf(c_0_93,negated_conjecture,
    ( k15_lattice3(esk16_0,a_2_5_lattice3(esk16_0,X1)) = k15_lattice3(esk16_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_38]),c_0_39]),c_0_28])]),c_0_29])).

fof(c_0_94,plain,(
    ! [X18] :
      ( ( ~ v2_struct_0(X18)
        | v2_struct_0(X18)
        | ~ v10_lattices(X18)
        | ~ l3_lattices(X18) )
      & ( v4_lattices(X18)
        | v2_struct_0(X18)
        | ~ v10_lattices(X18)
        | ~ l3_lattices(X18) )
      & ( v5_lattices(X18)
        | v2_struct_0(X18)
        | ~ v10_lattices(X18)
        | ~ l3_lattices(X18) )
      & ( v6_lattices(X18)
        | v2_struct_0(X18)
        | ~ v10_lattices(X18)
        | ~ l3_lattices(X18) )
      & ( v7_lattices(X18)
        | v2_struct_0(X18)
        | ~ v10_lattices(X18)
        | ~ l3_lattices(X18) )
      & ( v8_lattices(X18)
        | v2_struct_0(X18)
        | ~ v10_lattices(X18)
        | ~ l3_lattices(X18) )
      & ( v9_lattices(X18)
        | v2_struct_0(X18)
        | ~ v10_lattices(X18)
        | ~ l3_lattices(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).

cnf(c_0_95,negated_conjecture,
    ( r2_hidden(k15_lattice3(esk16_0,X1),X2)
    | ~ r1_tarski(a_2_6_lattice3(esk16_0,a_2_2_lattice3(esk16_0,k1_xboole_0)),X2) ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

fof(c_0_96,plain,(
    ! [X28,X30,X31] :
      ( ( m1_subset_1(esk3_1(X28),u1_struct_0(X28))
        | ~ v13_lattices(X28)
        | v2_struct_0(X28)
        | ~ l1_lattices(X28) )
      & ( k2_lattices(X28,esk3_1(X28),X30) = esk3_1(X28)
        | ~ m1_subset_1(X30,u1_struct_0(X28))
        | ~ v13_lattices(X28)
        | v2_struct_0(X28)
        | ~ l1_lattices(X28) )
      & ( k2_lattices(X28,X30,esk3_1(X28)) = esk3_1(X28)
        | ~ m1_subset_1(X30,u1_struct_0(X28))
        | ~ v13_lattices(X28)
        | v2_struct_0(X28)
        | ~ l1_lattices(X28) )
      & ( m1_subset_1(esk4_2(X28,X31),u1_struct_0(X28))
        | ~ m1_subset_1(X31,u1_struct_0(X28))
        | v13_lattices(X28)
        | v2_struct_0(X28)
        | ~ l1_lattices(X28) )
      & ( k2_lattices(X28,X31,esk4_2(X28,X31)) != X31
        | k2_lattices(X28,esk4_2(X28,X31),X31) != X31
        | ~ m1_subset_1(X31,u1_struct_0(X28))
        | v13_lattices(X28)
        | v2_struct_0(X28)
        | ~ l1_lattices(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d13_lattices])])])])])])).

cnf(c_0_97,negated_conjecture,
    ( r1_lattices(esk16_0,k15_lattice3(esk16_0,X1),k5_lattices(esk16_0))
    | ~ r2_hidden(k5_lattices(esk16_0),a_2_6_lattice3(esk16_0,a_2_2_lattice3(esk16_0,X1))) ),
    inference(spm,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_98,negated_conjecture,
    ( r2_hidden(k5_lattices(esk16_0),a_2_6_lattice3(esk16_0,X1))
    | ~ r2_hidden(k15_lattice3(esk16_0,k1_xboole_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_92]),c_0_75])])).

cnf(c_0_99,negated_conjecture,
    ( r4_lattice3(esk16_0,k15_lattice3(esk16_0,X1),a_2_5_lattice3(esk16_0,X1)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_93])).

fof(c_0_100,plain,(
    ! [X25,X26,X27] :
      ( ( ~ r1_lattices(X25,X26,X27)
        | k2_lattices(X25,X26,X27) = X26
        | ~ m1_subset_1(X27,u1_struct_0(X25))
        | ~ m1_subset_1(X26,u1_struct_0(X25))
        | v2_struct_0(X25)
        | ~ v8_lattices(X25)
        | ~ v9_lattices(X25)
        | ~ l3_lattices(X25) )
      & ( k2_lattices(X25,X26,X27) != X26
        | r1_lattices(X25,X26,X27)
        | ~ m1_subset_1(X27,u1_struct_0(X25))
        | ~ m1_subset_1(X26,u1_struct_0(X25))
        | v2_struct_0(X25)
        | ~ v8_lattices(X25)
        | ~ v9_lattices(X25)
        | ~ l3_lattices(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t21_lattices])])])])])).

cnf(c_0_101,plain,
    ( v9_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_94])).

cnf(c_0_102,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_94])).

cnf(c_0_103,negated_conjecture,
    ( r1_lattices(esk16_0,X1,k15_lattice3(esk16_0,X2))
    | ~ r3_lattice3(esk16_0,X1,X3)
    | ~ m1_subset_1(X1,u1_struct_0(esk16_0))
    | ~ r2_hidden(k15_lattice3(esk16_0,X2),X3) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_52]),c_0_28])]),c_0_29])).

cnf(c_0_104,negated_conjecture,
    ( r2_hidden(k15_lattice3(esk16_0,X1),a_2_6_lattice3(esk16_0,a_2_2_lattice3(esk16_0,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_95,c_0_82])).

cnf(c_0_105,plain,
    ( m1_subset_1(esk4_2(X1,X2),u1_struct_0(X1))
    | v13_lattices(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_96])).

fof(c_0_106,plain,(
    ! [X19,X20,X21] :
      ( ( k2_lattices(X19,X20,X21) = X20
        | ~ m1_subset_1(X21,u1_struct_0(X19))
        | X20 != k5_lattices(X19)
        | ~ m1_subset_1(X20,u1_struct_0(X19))
        | ~ v13_lattices(X19)
        | v2_struct_0(X19)
        | ~ l1_lattices(X19) )
      & ( k2_lattices(X19,X21,X20) = X20
        | ~ m1_subset_1(X21,u1_struct_0(X19))
        | X20 != k5_lattices(X19)
        | ~ m1_subset_1(X20,u1_struct_0(X19))
        | ~ v13_lattices(X19)
        | v2_struct_0(X19)
        | ~ l1_lattices(X19) )
      & ( m1_subset_1(esk2_2(X19,X20),u1_struct_0(X19))
        | X20 = k5_lattices(X19)
        | ~ m1_subset_1(X20,u1_struct_0(X19))
        | ~ v13_lattices(X19)
        | v2_struct_0(X19)
        | ~ l1_lattices(X19) )
      & ( k2_lattices(X19,X20,esk2_2(X19,X20)) != X20
        | k2_lattices(X19,esk2_2(X19,X20),X20) != X20
        | X20 = k5_lattices(X19)
        | ~ m1_subset_1(X20,u1_struct_0(X19))
        | ~ v13_lattices(X19)
        | v2_struct_0(X19)
        | ~ l1_lattices(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattices])])])])])])).

cnf(c_0_107,negated_conjecture,
    ( r1_lattices(esk16_0,k15_lattice3(esk16_0,X1),k5_lattices(esk16_0))
    | ~ r2_hidden(k15_lattice3(esk16_0,k1_xboole_0),a_2_2_lattice3(esk16_0,X1)) ),
    inference(spm,[status(thm)],[c_0_97,c_0_98])).

cnf(c_0_108,negated_conjecture,
    ( r2_hidden(k15_lattice3(esk16_0,X1),X2)
    | ~ r1_tarski(a_2_2_lattice3(esk16_0,a_2_5_lattice3(esk16_0,X1)),X2) ),
    inference(spm,[status(thm)],[c_0_71,c_0_99])).

cnf(c_0_109,plain,
    ( k2_lattices(X1,X2,X3) = X2
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_100])).

cnf(c_0_110,negated_conjecture,
    ( v9_lattices(esk16_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_39]),c_0_28])]),c_0_29])).

cnf(c_0_111,negated_conjecture,
    ( v8_lattices(esk16_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_39]),c_0_28])]),c_0_29])).

cnf(c_0_112,negated_conjecture,
    ( r1_lattices(esk16_0,X1,k15_lattice3(esk16_0,X2))
    | ~ r3_lattice3(esk16_0,X1,a_2_6_lattice3(esk16_0,a_2_2_lattice3(esk16_0,k1_xboole_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk16_0)) ),
    inference(spm,[status(thm)],[c_0_103,c_0_104])).

cnf(c_0_113,negated_conjecture,
    ( m1_subset_1(esk4_2(esk16_0,k15_lattice3(esk16_0,X1)),u1_struct_0(esk16_0))
    | v13_lattices(esk16_0)
    | ~ l1_lattices(esk16_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_52]),c_0_29])).

cnf(c_0_114,plain,
    ( k2_lattices(X1,X2,X3) = X3
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | X3 != k5_lattices(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v13_lattices(X1)
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_106])).

cnf(c_0_115,negated_conjecture,
    ( r1_lattices(esk16_0,k15_lattice3(esk16_0,X1),k5_lattices(esk16_0))
    | ~ r2_hidden(k15_lattice3(esk16_0,k1_xboole_0),a_2_2_lattice3(esk16_0,a_2_5_lattice3(esk16_0,X1))) ),
    inference(spm,[status(thm)],[c_0_107,c_0_93])).

cnf(c_0_116,negated_conjecture,
    ( r2_hidden(k15_lattice3(esk16_0,X1),a_2_2_lattice3(esk16_0,a_2_5_lattice3(esk16_0,X1))) ),
    inference(spm,[status(thm)],[c_0_108,c_0_82])).

cnf(c_0_117,negated_conjecture,
    ( k2_lattices(esk16_0,X1,k15_lattice3(esk16_0,X2)) = X1
    | ~ r1_lattices(esk16_0,X1,k15_lattice3(esk16_0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(esk16_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_52]),c_0_110]),c_0_111]),c_0_28])]),c_0_29])).

cnf(c_0_118,negated_conjecture,
    ( r1_lattices(esk16_0,k15_lattice3(esk16_0,k1_xboole_0),k15_lattice3(esk16_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_76]),c_0_77]),c_0_85]),c_0_77]),c_0_85]),c_0_52])])).

cnf(c_0_119,negated_conjecture,
    ( m1_subset_1(esk4_2(esk16_0,k15_lattice3(esk16_0,X1)),u1_struct_0(esk16_0))
    | v13_lattices(esk16_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_55]),c_0_28])])).

cnf(c_0_120,plain,
    ( k2_lattices(X1,X2,k5_lattices(X1)) = k5_lattices(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v13_lattices(X1)
    | ~ l1_lattices(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_114]),c_0_54])).

cnf(c_0_121,negated_conjecture,
    ( k2_lattices(esk16_0,X1,k5_lattices(esk16_0)) = X1
    | ~ r1_lattices(esk16_0,X1,k5_lattices(esk16_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk16_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_75]),c_0_110]),c_0_111]),c_0_28])]),c_0_29])).

cnf(c_0_122,negated_conjecture,
    ( r1_lattices(esk16_0,k15_lattice3(esk16_0,k1_xboole_0),k5_lattices(esk16_0)) ),
    inference(spm,[status(thm)],[c_0_115,c_0_116])).

cnf(c_0_123,negated_conjecture,
    ( v2_struct_0(esk16_0)
    | ~ v10_lattices(esk16_0)
    | ~ v13_lattices(esk16_0)
    | ~ l3_lattices(esk16_0)
    | k5_lattices(esk16_0) != k15_lattice3(esk16_0,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_124,negated_conjecture,
    ( k2_lattices(esk16_0,k15_lattice3(esk16_0,k1_xboole_0),k15_lattice3(esk16_0,X1)) = k15_lattice3(esk16_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_118]),c_0_52])])).

cnf(c_0_125,negated_conjecture,
    ( k15_lattice3(esk16_0,a_2_3_lattice3(esk16_0,esk4_2(esk16_0,k15_lattice3(esk16_0,X1)))) = esk4_2(esk16_0,k15_lattice3(esk16_0,X1))
    | v13_lattices(esk16_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_119]),c_0_38]),c_0_39]),c_0_28])]),c_0_29])).

cnf(c_0_126,negated_conjecture,
    ( k2_lattices(esk16_0,k15_lattice3(esk16_0,X1),k5_lattices(esk16_0)) = k5_lattices(esk16_0)
    | ~ v13_lattices(esk16_0)
    | ~ l1_lattices(esk16_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_52]),c_0_29])).

cnf(c_0_127,negated_conjecture,
    ( k2_lattices(esk16_0,k15_lattice3(esk16_0,k1_xboole_0),k5_lattices(esk16_0)) = k15_lattice3(esk16_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_122]),c_0_52])])).

cnf(c_0_128,negated_conjecture,
    ( k5_lattices(esk16_0) != k15_lattice3(esk16_0,k1_xboole_0)
    | ~ v13_lattices(esk16_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_123,c_0_28]),c_0_39])]),c_0_29])).

fof(c_0_129,plain,(
    ! [X44,X45,X46] :
      ( ( ~ v6_lattices(X44)
        | ~ m1_subset_1(X45,u1_struct_0(X44))
        | ~ m1_subset_1(X46,u1_struct_0(X44))
        | k2_lattices(X44,X45,X46) = k2_lattices(X44,X46,X45)
        | v2_struct_0(X44)
        | ~ l1_lattices(X44) )
      & ( m1_subset_1(esk7_1(X44),u1_struct_0(X44))
        | v6_lattices(X44)
        | v2_struct_0(X44)
        | ~ l1_lattices(X44) )
      & ( m1_subset_1(esk8_1(X44),u1_struct_0(X44))
        | v6_lattices(X44)
        | v2_struct_0(X44)
        | ~ l1_lattices(X44) )
      & ( k2_lattices(X44,esk7_1(X44),esk8_1(X44)) != k2_lattices(X44,esk8_1(X44),esk7_1(X44))
        | v6_lattices(X44)
        | v2_struct_0(X44)
        | ~ l1_lattices(X44) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d6_lattices])])])])])])).

cnf(c_0_130,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_94])).

cnf(c_0_131,plain,
    ( v13_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,esk4_2(X1,X2)) != X2
    | k2_lattices(X1,esk4_2(X1,X2),X2) != X2
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_96])).

cnf(c_0_132,negated_conjecture,
    ( k2_lattices(esk16_0,k15_lattice3(esk16_0,k1_xboole_0),esk4_2(esk16_0,k15_lattice3(esk16_0,X1))) = k15_lattice3(esk16_0,k1_xboole_0)
    | v13_lattices(esk16_0) ),
    inference(spm,[status(thm)],[c_0_124,c_0_125])).

cnf(c_0_133,negated_conjecture,
    ( ~ v13_lattices(esk16_0)
    | ~ l1_lattices(esk16_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_126,c_0_127]),c_0_128])).

cnf(c_0_134,plain,
    ( k2_lattices(X1,X2,X3) = k2_lattices(X1,X3,X2)
    | v2_struct_0(X1)
    | ~ v6_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_129])).

cnf(c_0_135,negated_conjecture,
    ( v6_lattices(esk16_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_130,c_0_39]),c_0_28])]),c_0_29])).

cnf(c_0_136,negated_conjecture,
    ( k2_lattices(esk16_0,esk4_2(esk16_0,k15_lattice3(esk16_0,k1_xboole_0)),k15_lattice3(esk16_0,k1_xboole_0)) != k15_lattice3(esk16_0,k1_xboole_0)
    | ~ l1_lattices(esk16_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131,c_0_132]),c_0_52])]),c_0_29]),c_0_133])).

cnf(c_0_137,negated_conjecture,
    ( k2_lattices(esk16_0,X1,esk4_2(esk16_0,k15_lattice3(esk16_0,X2))) = k2_lattices(esk16_0,esk4_2(esk16_0,k15_lattice3(esk16_0,X2)),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk16_0))
    | ~ l1_lattices(esk16_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134,c_0_119]),c_0_135])]),c_0_29]),c_0_133])).

cnf(c_0_138,negated_conjecture,
    ( k2_lattices(esk16_0,k15_lattice3(esk16_0,k1_xboole_0),esk4_2(esk16_0,k15_lattice3(esk16_0,k1_xboole_0))) != k15_lattice3(esk16_0,k1_xboole_0)
    | ~ l1_lattices(esk16_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_136,c_0_137]),c_0_52])])).

cnf(c_0_139,negated_conjecture,
    ( ~ l1_lattices(esk16_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_132]),c_0_133])).

cnf(c_0_140,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_139,c_0_55]),c_0_28])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:03:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.52  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.52  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.52  #
% 0.19/0.52  # Preprocessing time       : 0.033 s
% 0.19/0.52  # Presaturation interreduction done
% 0.19/0.52  
% 0.19/0.52  # Proof found!
% 0.19/0.52  # SZS status Theorem
% 0.19/0.52  # SZS output start CNFRefutation
% 0.19/0.52  fof(t50_lattice3, conjecture, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>((((~(v2_struct_0(X1))&v10_lattices(X1))&v13_lattices(X1))&l3_lattices(X1))&k5_lattices(X1)=k15_lattice3(X1,k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_lattice3)).
% 0.19/0.52  fof(fraenkel_a_2_2_lattice3, axiom, ![X1, X2, X3]:((((~(v2_struct_0(X2))&v10_lattices(X2))&v4_lattice3(X2))&l3_lattices(X2))=>(r2_hidden(X1,a_2_2_lattice3(X2,X3))<=>?[X4]:((m1_subset_1(X4,u1_struct_0(X2))&X1=X4)&r4_lattice3(X2,X4,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fraenkel_a_2_2_lattice3)).
% 0.19/0.52  fof(dt_k16_lattice3, axiom, ![X1, X2]:((~(v2_struct_0(X1))&l3_lattices(X1))=>m1_subset_1(k16_lattice3(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k16_lattice3)).
% 0.19/0.52  fof(dt_k15_lattice3, axiom, ![X1, X2]:((~(v2_struct_0(X1))&l3_lattices(X1))=>m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k15_lattice3)).
% 0.19/0.52  fof(d21_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(X3=k15_lattice3(X1,X2)<=>(r4_lattice3(X1,X3,X2)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r4_lattice3(X1,X4,X2)=>r1_lattices(X1,X3,X4)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d21_lattice3)).
% 0.19/0.52  fof(fraenkel_a_2_6_lattice3, axiom, ![X1, X2, X3]:((((~(v2_struct_0(X2))&v10_lattices(X2))&v4_lattice3(X2))&l3_lattices(X2))=>(r2_hidden(X1,a_2_6_lattice3(X2,X3))<=>?[X4]:((m1_subset_1(X4,u1_struct_0(X2))&X1=X4)&?[X5]:((m1_subset_1(X5,u1_struct_0(X2))&r3_lattices(X2,X5,X4))&r2_hidden(X5,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fraenkel_a_2_6_lattice3)).
% 0.19/0.52  fof(t46_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2, X3]:(r1_tarski(X2,X3)=>(r3_lattices(X1,k15_lattice3(X1,X2),k15_lattice3(X1,X3))&r3_lattices(X1,k16_lattice3(X1,X3),k16_lattice3(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_lattice3)).
% 0.19/0.52  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.19/0.52  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.52  fof(t45_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(X2=k15_lattice3(X1,a_2_3_lattice3(X1,X2))&X2=k16_lattice3(X1,a_2_4_lattice3(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_lattice3)).
% 0.19/0.52  fof(dt_k5_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>m1_subset_1(k5_lattices(X1),u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_lattices)).
% 0.19/0.52  fof(dt_l3_lattices, axiom, ![X1]:(l3_lattices(X1)=>(l1_lattices(X1)&l2_lattices(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l3_lattices)).
% 0.19/0.52  fof(t34_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(X2=k16_lattice3(X1,X3)<=>(r3_lattice3(X1,X2,X3)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r3_lattice3(X1,X4,X3)=>r3_lattices(X1,X4,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_lattice3)).
% 0.19/0.52  fof(t47_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(k15_lattice3(X1,X2)=k15_lattice3(X1,a_2_5_lattice3(X1,X2))&k16_lattice3(X1,X2)=k16_lattice3(X1,a_2_6_lattice3(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_lattice3)).
% 0.19/0.52  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.52  fof(d16_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(r3_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X3)=>r1_lattices(X1,X2,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_lattice3)).
% 0.19/0.52  fof(t37_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:k15_lattice3(X1,X2)=k16_lattice3(X1,a_2_2_lattice3(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_lattice3)).
% 0.19/0.52  fof(cc1_lattices, axiom, ![X1]:(l3_lattices(X1)=>((~(v2_struct_0(X1))&v10_lattices(X1))=>((((((~(v2_struct_0(X1))&v4_lattices(X1))&v5_lattices(X1))&v6_lattices(X1))&v7_lattices(X1))&v8_lattices(X1))&v9_lattices(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattices)).
% 0.19/0.52  fof(d13_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>(v13_lattices(X1)<=>?[X2]:(m1_subset_1(X2,u1_struct_0(X1))&![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(k2_lattices(X1,X2,X3)=X2&k2_lattices(X1,X3,X2)=X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_lattices)).
% 0.19/0.52  fof(t21_lattices, axiom, ![X1]:((((~(v2_struct_0(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_lattices(X1,X2,X3)<=>k2_lattices(X1,X2,X3)=X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_lattices)).
% 0.19/0.52  fof(d16_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>(v13_lattices(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(X2=k5_lattices(X1)<=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(k2_lattices(X1,X2,X3)=X2&k2_lattices(X1,X3,X2)=X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_lattices)).
% 0.19/0.52  fof(d6_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>(v6_lattices(X1)<=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>k2_lattices(X1,X2,X3)=k2_lattices(X1,X3,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_lattices)).
% 0.19/0.52  fof(c_0_22, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>((((~(v2_struct_0(X1))&v10_lattices(X1))&v13_lattices(X1))&l3_lattices(X1))&k5_lattices(X1)=k15_lattice3(X1,k1_xboole_0)))), inference(assume_negation,[status(cth)],[t50_lattice3])).
% 0.19/0.52  fof(c_0_23, plain, ![X53, X54, X55, X57, X58]:((((m1_subset_1(esk9_3(X53,X54,X55),u1_struct_0(X54))|~r2_hidden(X53,a_2_2_lattice3(X54,X55))|(v2_struct_0(X54)|~v10_lattices(X54)|~v4_lattice3(X54)|~l3_lattices(X54)))&(X53=esk9_3(X53,X54,X55)|~r2_hidden(X53,a_2_2_lattice3(X54,X55))|(v2_struct_0(X54)|~v10_lattices(X54)|~v4_lattice3(X54)|~l3_lattices(X54))))&(r4_lattice3(X54,esk9_3(X53,X54,X55),X55)|~r2_hidden(X53,a_2_2_lattice3(X54,X55))|(v2_struct_0(X54)|~v10_lattices(X54)|~v4_lattice3(X54)|~l3_lattices(X54))))&(~m1_subset_1(X58,u1_struct_0(X54))|X53!=X58|~r4_lattice3(X54,X58,X57)|r2_hidden(X53,a_2_2_lattice3(X54,X57))|(v2_struct_0(X54)|~v10_lattices(X54)|~v4_lattice3(X54)|~l3_lattices(X54)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_2_lattice3])])])])])])])).
% 0.19/0.52  fof(c_0_24, plain, ![X51, X52]:(v2_struct_0(X51)|~l3_lattices(X51)|m1_subset_1(k16_lattice3(X51,X52),u1_struct_0(X51))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k16_lattice3])])])).
% 0.19/0.52  fof(c_0_25, negated_conjecture, ((((~v2_struct_0(esk16_0)&v10_lattices(esk16_0))&v4_lattice3(esk16_0))&l3_lattices(esk16_0))&(v2_struct_0(esk16_0)|~v10_lattices(esk16_0)|~v13_lattices(esk16_0)|~l3_lattices(esk16_0)|k5_lattices(esk16_0)!=k15_lattice3(esk16_0,k1_xboole_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_22])])])])).
% 0.19/0.52  cnf(c_0_26, plain, (r2_hidden(X3,a_2_2_lattice3(X2,X4))|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|X3!=X1|~r4_lattice3(X2,X1,X4)|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.52  cnf(c_0_27, plain, (v2_struct_0(X1)|m1_subset_1(k16_lattice3(X1,X2),u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.52  cnf(c_0_28, negated_conjecture, (l3_lattices(esk16_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.52  cnf(c_0_29, negated_conjecture, (~v2_struct_0(esk16_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.52  fof(c_0_30, plain, ![X49, X50]:(v2_struct_0(X49)|~l3_lattices(X49)|m1_subset_1(k15_lattice3(X49,X50),u1_struct_0(X49))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k15_lattice3])])])).
% 0.19/0.52  fof(c_0_31, plain, ![X39, X40, X41, X42]:(((r4_lattice3(X39,X41,X40)|X41!=k15_lattice3(X39,X40)|~m1_subset_1(X41,u1_struct_0(X39))|(v2_struct_0(X39)|~v10_lattices(X39)|~v4_lattice3(X39)|~l3_lattices(X39))|(v2_struct_0(X39)|~l3_lattices(X39)))&(~m1_subset_1(X42,u1_struct_0(X39))|(~r4_lattice3(X39,X42,X40)|r1_lattices(X39,X41,X42))|X41!=k15_lattice3(X39,X40)|~m1_subset_1(X41,u1_struct_0(X39))|(v2_struct_0(X39)|~v10_lattices(X39)|~v4_lattice3(X39)|~l3_lattices(X39))|(v2_struct_0(X39)|~l3_lattices(X39))))&((m1_subset_1(esk6_3(X39,X40,X41),u1_struct_0(X39))|~r4_lattice3(X39,X41,X40)|X41=k15_lattice3(X39,X40)|~m1_subset_1(X41,u1_struct_0(X39))|(v2_struct_0(X39)|~v10_lattices(X39)|~v4_lattice3(X39)|~l3_lattices(X39))|(v2_struct_0(X39)|~l3_lattices(X39)))&((r4_lattice3(X39,esk6_3(X39,X40,X41),X40)|~r4_lattice3(X39,X41,X40)|X41=k15_lattice3(X39,X40)|~m1_subset_1(X41,u1_struct_0(X39))|(v2_struct_0(X39)|~v10_lattices(X39)|~v4_lattice3(X39)|~l3_lattices(X39))|(v2_struct_0(X39)|~l3_lattices(X39)))&(~r1_lattices(X39,X41,esk6_3(X39,X40,X41))|~r4_lattice3(X39,X41,X40)|X41=k15_lattice3(X39,X40)|~m1_subset_1(X41,u1_struct_0(X39))|(v2_struct_0(X39)|~v10_lattices(X39)|~v4_lattice3(X39)|~l3_lattices(X39))|(v2_struct_0(X39)|~l3_lattices(X39)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d21_lattice3])])])])])])).
% 0.19/0.52  fof(c_0_32, plain, ![X67, X68, X69, X72, X73, X74]:((((m1_subset_1(esk12_3(X67,X68,X69),u1_struct_0(X68))|~r2_hidden(X67,a_2_6_lattice3(X68,X69))|(v2_struct_0(X68)|~v10_lattices(X68)|~v4_lattice3(X68)|~l3_lattices(X68)))&(X67=esk12_3(X67,X68,X69)|~r2_hidden(X67,a_2_6_lattice3(X68,X69))|(v2_struct_0(X68)|~v10_lattices(X68)|~v4_lattice3(X68)|~l3_lattices(X68))))&(((m1_subset_1(esk13_3(X67,X68,X69),u1_struct_0(X68))|~r2_hidden(X67,a_2_6_lattice3(X68,X69))|(v2_struct_0(X68)|~v10_lattices(X68)|~v4_lattice3(X68)|~l3_lattices(X68)))&(r3_lattices(X68,esk13_3(X67,X68,X69),esk12_3(X67,X68,X69))|~r2_hidden(X67,a_2_6_lattice3(X68,X69))|(v2_struct_0(X68)|~v10_lattices(X68)|~v4_lattice3(X68)|~l3_lattices(X68))))&(r2_hidden(esk13_3(X67,X68,X69),X69)|~r2_hidden(X67,a_2_6_lattice3(X68,X69))|(v2_struct_0(X68)|~v10_lattices(X68)|~v4_lattice3(X68)|~l3_lattices(X68)))))&(~m1_subset_1(X73,u1_struct_0(X68))|X67!=X73|(~m1_subset_1(X74,u1_struct_0(X68))|~r3_lattices(X68,X74,X73)|~r2_hidden(X74,X72))|r2_hidden(X67,a_2_6_lattice3(X68,X72))|(v2_struct_0(X68)|~v10_lattices(X68)|~v4_lattice3(X68)|~l3_lattices(X68)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_6_lattice3])])])])])])])).
% 0.19/0.52  fof(c_0_33, plain, ![X85, X86, X87]:((r3_lattices(X85,k15_lattice3(X85,X86),k15_lattice3(X85,X87))|~r1_tarski(X86,X87)|(v2_struct_0(X85)|~v10_lattices(X85)|~v4_lattice3(X85)|~l3_lattices(X85)))&(r3_lattices(X85,k16_lattice3(X85,X87),k16_lattice3(X85,X86))|~r1_tarski(X86,X87)|(v2_struct_0(X85)|~v10_lattices(X85)|~v4_lattice3(X85)|~l3_lattices(X85)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t46_lattice3])])])])])).
% 0.19/0.52  fof(c_0_34, plain, ![X14]:r1_tarski(k1_xboole_0,X14), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.19/0.52  fof(c_0_35, plain, ![X6, X7, X8, X9, X10]:((~r1_tarski(X6,X7)|(~r2_hidden(X8,X6)|r2_hidden(X8,X7)))&((r2_hidden(esk1_2(X9,X10),X9)|r1_tarski(X9,X10))&(~r2_hidden(esk1_2(X9,X10),X10)|r1_tarski(X9,X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.52  cnf(c_0_36, plain, (v2_struct_0(X1)|r2_hidden(X2,a_2_2_lattice3(X1,X3))|~r4_lattice3(X1,X2,X3)|~v4_lattice3(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(er,[status(thm)],[c_0_26])).
% 0.19/0.52  cnf(c_0_37, negated_conjecture, (m1_subset_1(k16_lattice3(esk16_0,X1),u1_struct_0(esk16_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29])).
% 0.19/0.52  cnf(c_0_38, negated_conjecture, (v4_lattice3(esk16_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.52  cnf(c_0_39, negated_conjecture, (v10_lattices(esk16_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.52  fof(c_0_40, plain, ![X83, X84]:((X84=k15_lattice3(X83,a_2_3_lattice3(X83,X84))|~m1_subset_1(X84,u1_struct_0(X83))|(v2_struct_0(X83)|~v10_lattices(X83)|~v4_lattice3(X83)|~l3_lattices(X83)))&(X84=k16_lattice3(X83,a_2_4_lattice3(X83,X84))|~m1_subset_1(X84,u1_struct_0(X83))|(v2_struct_0(X83)|~v10_lattices(X83)|~v4_lattice3(X83)|~l3_lattices(X83)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t45_lattice3])])])])])).
% 0.19/0.52  cnf(c_0_41, plain, (v2_struct_0(X1)|m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.52  cnf(c_0_42, plain, (r4_lattice3(X1,X2,X3)|v2_struct_0(X1)|v2_struct_0(X1)|X2!=k15_lattice3(X1,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.52  fof(c_0_43, plain, ![X23]:(v2_struct_0(X23)|~l1_lattices(X23)|m1_subset_1(k5_lattices(X23),u1_struct_0(X23))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_lattices])])])).
% 0.19/0.52  fof(c_0_44, plain, ![X24]:((l1_lattices(X24)|~l3_lattices(X24))&(l2_lattices(X24)|~l3_lattices(X24))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).
% 0.19/0.52  fof(c_0_45, plain, ![X75, X76, X77, X78, X79]:(((r3_lattice3(X75,X76,X77)|X76!=k16_lattice3(X75,X77)|~m1_subset_1(X76,u1_struct_0(X75))|(v2_struct_0(X75)|~v10_lattices(X75)|~v4_lattice3(X75)|~l3_lattices(X75)))&(~m1_subset_1(X78,u1_struct_0(X75))|(~r3_lattice3(X75,X78,X77)|r3_lattices(X75,X78,X76))|X76!=k16_lattice3(X75,X77)|~m1_subset_1(X76,u1_struct_0(X75))|(v2_struct_0(X75)|~v10_lattices(X75)|~v4_lattice3(X75)|~l3_lattices(X75))))&((m1_subset_1(esk14_3(X75,X76,X79),u1_struct_0(X75))|~r3_lattice3(X75,X76,X79)|X76=k16_lattice3(X75,X79)|~m1_subset_1(X76,u1_struct_0(X75))|(v2_struct_0(X75)|~v10_lattices(X75)|~v4_lattice3(X75)|~l3_lattices(X75)))&((r3_lattice3(X75,esk14_3(X75,X76,X79),X79)|~r3_lattice3(X75,X76,X79)|X76=k16_lattice3(X75,X79)|~m1_subset_1(X76,u1_struct_0(X75))|(v2_struct_0(X75)|~v10_lattices(X75)|~v4_lattice3(X75)|~l3_lattices(X75)))&(~r3_lattices(X75,esk14_3(X75,X76,X79),X76)|~r3_lattice3(X75,X76,X79)|X76=k16_lattice3(X75,X79)|~m1_subset_1(X76,u1_struct_0(X75))|(v2_struct_0(X75)|~v10_lattices(X75)|~v4_lattice3(X75)|~l3_lattices(X75)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_lattice3])])])])])])])).
% 0.19/0.52  cnf(c_0_46, plain, (r2_hidden(X3,a_2_6_lattice3(X2,X5))|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|X3!=X1|~m1_subset_1(X4,u1_struct_0(X2))|~r3_lattices(X2,X4,X1)|~r2_hidden(X4,X5)|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.52  cnf(c_0_47, plain, (r3_lattices(X1,k15_lattice3(X1,X2),k15_lattice3(X1,X3))|v2_struct_0(X1)|~r1_tarski(X2,X3)|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.52  cnf(c_0_48, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.52  cnf(c_0_49, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.52  cnf(c_0_50, negated_conjecture, (r2_hidden(k16_lattice3(esk16_0,X1),a_2_2_lattice3(esk16_0,X2))|~r4_lattice3(esk16_0,k16_lattice3(esk16_0,X1),X2)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38]), c_0_39]), c_0_28])]), c_0_29])).
% 0.19/0.52  cnf(c_0_51, plain, (X1=k16_lattice3(X2,a_2_4_lattice3(X2,X1))|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.52  cnf(c_0_52, negated_conjecture, (m1_subset_1(k15_lattice3(esk16_0,X1),u1_struct_0(esk16_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_28]), c_0_29])).
% 0.19/0.52  cnf(c_0_53, plain, (v2_struct_0(X1)|r4_lattice3(X1,X2,X3)|X2!=k15_lattice3(X1,X3)|~l3_lattices(X1)|~v10_lattices(X1)|~v4_lattice3(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(cn,[status(thm)],[c_0_42])).
% 0.19/0.52  cnf(c_0_54, plain, (v2_struct_0(X1)|m1_subset_1(k5_lattices(X1),u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.52  cnf(c_0_55, plain, (l1_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.19/0.52  cnf(c_0_56, plain, (r3_lattice3(X1,X2,X3)|v2_struct_0(X1)|X2!=k16_lattice3(X1,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.19/0.52  fof(c_0_57, plain, ![X88, X89]:((k15_lattice3(X88,X89)=k15_lattice3(X88,a_2_5_lattice3(X88,X89))|(v2_struct_0(X88)|~v10_lattices(X88)|~v4_lattice3(X88)|~l3_lattices(X88)))&(k16_lattice3(X88,X89)=k16_lattice3(X88,a_2_6_lattice3(X88,X89))|(v2_struct_0(X88)|~v10_lattices(X88)|~v4_lattice3(X88)|~l3_lattices(X88)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t47_lattice3])])])])])).
% 0.19/0.52  cnf(c_0_58, plain, (v2_struct_0(X1)|r2_hidden(X2,a_2_6_lattice3(X1,X3))|~r3_lattices(X1,X4,X2)|~v4_lattice3(X1)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)|~r2_hidden(X4,X3)), inference(er,[status(thm)],[c_0_46])).
% 0.19/0.52  cnf(c_0_59, plain, (r3_lattices(X1,k15_lattice3(X1,k1_xboole_0),k15_lattice3(X1,X2))|v2_struct_0(X1)|~v4_lattice3(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.19/0.52  cnf(c_0_60, negated_conjecture, (r2_hidden(k16_lattice3(esk16_0,X1),X2)|~r4_lattice3(esk16_0,k16_lattice3(esk16_0,X1),X3)|~r1_tarski(a_2_2_lattice3(esk16_0,X3),X2)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.19/0.52  cnf(c_0_61, negated_conjecture, (k16_lattice3(esk16_0,a_2_4_lattice3(esk16_0,k15_lattice3(esk16_0,X1)))=k15_lattice3(esk16_0,X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_38]), c_0_39]), c_0_28])]), c_0_29])).
% 0.19/0.52  cnf(c_0_62, plain, (r4_lattice3(X1,k15_lattice3(X1,X2),X2)|v2_struct_0(X1)|~v4_lattice3(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_53]), c_0_41])).
% 0.19/0.52  fof(c_0_63, plain, ![X12, X13]:(((r1_tarski(X12,X13)|X12!=X13)&(r1_tarski(X13,X12)|X12!=X13))&(~r1_tarski(X12,X13)|~r1_tarski(X13,X12)|X12=X13)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.52  fof(c_0_64, plain, ![X33, X34, X35, X36, X37]:((~r3_lattice3(X33,X34,X35)|(~m1_subset_1(X36,u1_struct_0(X33))|(~r2_hidden(X36,X35)|r1_lattices(X33,X34,X36)))|~m1_subset_1(X34,u1_struct_0(X33))|(v2_struct_0(X33)|~l3_lattices(X33)))&((m1_subset_1(esk5_3(X33,X34,X37),u1_struct_0(X33))|r3_lattice3(X33,X34,X37)|~m1_subset_1(X34,u1_struct_0(X33))|(v2_struct_0(X33)|~l3_lattices(X33)))&((r2_hidden(esk5_3(X33,X34,X37),X37)|r3_lattice3(X33,X34,X37)|~m1_subset_1(X34,u1_struct_0(X33))|(v2_struct_0(X33)|~l3_lattices(X33)))&(~r1_lattices(X33,X34,esk5_3(X33,X34,X37))|r3_lattice3(X33,X34,X37)|~m1_subset_1(X34,u1_struct_0(X33))|(v2_struct_0(X33)|~l3_lattices(X33)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattice3])])])])])])])).
% 0.19/0.52  cnf(c_0_65, plain, (m1_subset_1(k5_lattices(X1),u1_struct_0(X1))|v2_struct_0(X1)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.19/0.52  cnf(c_0_66, plain, (r3_lattice3(X1,k16_lattice3(X1,X2),X2)|v2_struct_0(X1)|~v4_lattice3(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_56]), c_0_27])).
% 0.19/0.52  cnf(c_0_67, plain, (k16_lattice3(X1,X2)=k16_lattice3(X1,a_2_6_lattice3(X1,X2))|v2_struct_0(X1)|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.19/0.52  fof(c_0_68, plain, ![X81, X82]:(v2_struct_0(X81)|~v10_lattices(X81)|~v4_lattice3(X81)|~l3_lattices(X81)|k15_lattice3(X81,X82)=k16_lattice3(X81,a_2_2_lattice3(X81,X82))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t37_lattice3])])])])).
% 0.19/0.52  cnf(c_0_69, negated_conjecture, (r2_hidden(X1,a_2_6_lattice3(esk16_0,X2))|~r3_lattices(esk16_0,k15_lattice3(esk16_0,X3),X1)|~m1_subset_1(X1,u1_struct_0(esk16_0))|~r2_hidden(k15_lattice3(esk16_0,X3),X2)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_52]), c_0_38]), c_0_39]), c_0_28])]), c_0_29])).
% 0.19/0.52  cnf(c_0_70, negated_conjecture, (r3_lattices(esk16_0,k15_lattice3(esk16_0,k1_xboole_0),k15_lattice3(esk16_0,X1))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_38]), c_0_39]), c_0_28])]), c_0_29])).
% 0.19/0.52  cnf(c_0_71, negated_conjecture, (r2_hidden(k15_lattice3(esk16_0,X1),X2)|~r4_lattice3(esk16_0,k15_lattice3(esk16_0,X1),X3)|~r1_tarski(a_2_2_lattice3(esk16_0,X3),X2)), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.19/0.52  cnf(c_0_72, negated_conjecture, (r4_lattice3(esk16_0,k15_lattice3(esk16_0,X1),X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_38]), c_0_39]), c_0_28])]), c_0_29])).
% 0.19/0.52  cnf(c_0_73, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.19/0.52  cnf(c_0_74, plain, (r1_lattices(X1,X2,X4)|v2_struct_0(X1)|~r3_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X4,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.19/0.52  cnf(c_0_75, negated_conjecture, (m1_subset_1(k5_lattices(esk16_0),u1_struct_0(esk16_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_28]), c_0_29])).
% 0.19/0.52  cnf(c_0_76, negated_conjecture, (r3_lattice3(esk16_0,k16_lattice3(esk16_0,X1),X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_38]), c_0_39]), c_0_28])]), c_0_29])).
% 0.19/0.52  cnf(c_0_77, negated_conjecture, (k16_lattice3(esk16_0,a_2_6_lattice3(esk16_0,X1))=k16_lattice3(esk16_0,X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_38]), c_0_39]), c_0_28])]), c_0_29])).
% 0.19/0.52  cnf(c_0_78, plain, (v2_struct_0(X1)|k15_lattice3(X1,X2)=k16_lattice3(X1,a_2_2_lattice3(X1,X2))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.19/0.52  cnf(c_0_79, plain, (X1=k15_lattice3(X2,a_2_3_lattice3(X2,X1))|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.52  cnf(c_0_80, negated_conjecture, (r2_hidden(k15_lattice3(esk16_0,X1),a_2_6_lattice3(esk16_0,X2))|~r2_hidden(k15_lattice3(esk16_0,k1_xboole_0),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_52])])).
% 0.19/0.52  cnf(c_0_81, negated_conjecture, (r2_hidden(k15_lattice3(esk16_0,X1),X2)|~r1_tarski(a_2_2_lattice3(esk16_0,X1),X2)), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.19/0.52  cnf(c_0_82, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_73])).
% 0.19/0.52  cnf(c_0_83, negated_conjecture, (r1_lattices(esk16_0,X1,k5_lattices(esk16_0))|~r3_lattice3(esk16_0,X1,X2)|~m1_subset_1(X1,u1_struct_0(esk16_0))|~r2_hidden(k5_lattices(esk16_0),X2)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_28])]), c_0_29])).
% 0.19/0.52  cnf(c_0_84, negated_conjecture, (r3_lattice3(esk16_0,k16_lattice3(esk16_0,X1),a_2_6_lattice3(esk16_0,X1))), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 0.19/0.52  cnf(c_0_85, negated_conjecture, (k16_lattice3(esk16_0,a_2_2_lattice3(esk16_0,X1))=k15_lattice3(esk16_0,X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_38]), c_0_39]), c_0_28])]), c_0_29])).
% 0.19/0.52  cnf(c_0_86, negated_conjecture, (k15_lattice3(esk16_0,a_2_3_lattice3(esk16_0,k5_lattices(esk16_0)))=k5_lattices(esk16_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_75]), c_0_38]), c_0_39]), c_0_28])]), c_0_29])).
% 0.19/0.52  cnf(c_0_87, plain, (k15_lattice3(X1,X2)=k15_lattice3(X1,a_2_5_lattice3(X1,X2))|v2_struct_0(X1)|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.19/0.52  cnf(c_0_88, negated_conjecture, (r2_hidden(k15_lattice3(esk16_0,X1),X2)|~r2_hidden(k15_lattice3(esk16_0,k1_xboole_0),X3)|~r1_tarski(a_2_6_lattice3(esk16_0,X3),X2)), inference(spm,[status(thm)],[c_0_49, c_0_80])).
% 0.19/0.52  cnf(c_0_89, negated_conjecture, (r2_hidden(k15_lattice3(esk16_0,X1),a_2_2_lattice3(esk16_0,X1))), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 0.19/0.52  cnf(c_0_90, negated_conjecture, (r1_lattices(esk16_0,k15_lattice3(esk16_0,X1),k5_lattices(esk16_0))|~r3_lattice3(esk16_0,k15_lattice3(esk16_0,X1),X2)|~r2_hidden(k5_lattices(esk16_0),X2)), inference(spm,[status(thm)],[c_0_83, c_0_52])).
% 0.19/0.52  cnf(c_0_91, negated_conjecture, (r3_lattice3(esk16_0,k15_lattice3(esk16_0,X1),a_2_6_lattice3(esk16_0,a_2_2_lattice3(esk16_0,X1)))), inference(spm,[status(thm)],[c_0_84, c_0_85])).
% 0.19/0.52  cnf(c_0_92, negated_conjecture, (r3_lattices(esk16_0,k15_lattice3(esk16_0,k1_xboole_0),k5_lattices(esk16_0))), inference(spm,[status(thm)],[c_0_70, c_0_86])).
% 0.19/0.52  cnf(c_0_93, negated_conjecture, (k15_lattice3(esk16_0,a_2_5_lattice3(esk16_0,X1))=k15_lattice3(esk16_0,X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_38]), c_0_39]), c_0_28])]), c_0_29])).
% 0.19/0.52  fof(c_0_94, plain, ![X18]:(((((((~v2_struct_0(X18)|(v2_struct_0(X18)|~v10_lattices(X18))|~l3_lattices(X18))&(v4_lattices(X18)|(v2_struct_0(X18)|~v10_lattices(X18))|~l3_lattices(X18)))&(v5_lattices(X18)|(v2_struct_0(X18)|~v10_lattices(X18))|~l3_lattices(X18)))&(v6_lattices(X18)|(v2_struct_0(X18)|~v10_lattices(X18))|~l3_lattices(X18)))&(v7_lattices(X18)|(v2_struct_0(X18)|~v10_lattices(X18))|~l3_lattices(X18)))&(v8_lattices(X18)|(v2_struct_0(X18)|~v10_lattices(X18))|~l3_lattices(X18)))&(v9_lattices(X18)|(v2_struct_0(X18)|~v10_lattices(X18))|~l3_lattices(X18))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).
% 0.19/0.52  cnf(c_0_95, negated_conjecture, (r2_hidden(k15_lattice3(esk16_0,X1),X2)|~r1_tarski(a_2_6_lattice3(esk16_0,a_2_2_lattice3(esk16_0,k1_xboole_0)),X2)), inference(spm,[status(thm)],[c_0_88, c_0_89])).
% 0.19/0.52  fof(c_0_96, plain, ![X28, X30, X31]:(((m1_subset_1(esk3_1(X28),u1_struct_0(X28))|~v13_lattices(X28)|(v2_struct_0(X28)|~l1_lattices(X28)))&((k2_lattices(X28,esk3_1(X28),X30)=esk3_1(X28)|~m1_subset_1(X30,u1_struct_0(X28))|~v13_lattices(X28)|(v2_struct_0(X28)|~l1_lattices(X28)))&(k2_lattices(X28,X30,esk3_1(X28))=esk3_1(X28)|~m1_subset_1(X30,u1_struct_0(X28))|~v13_lattices(X28)|(v2_struct_0(X28)|~l1_lattices(X28)))))&((m1_subset_1(esk4_2(X28,X31),u1_struct_0(X28))|~m1_subset_1(X31,u1_struct_0(X28))|v13_lattices(X28)|(v2_struct_0(X28)|~l1_lattices(X28)))&(k2_lattices(X28,X31,esk4_2(X28,X31))!=X31|k2_lattices(X28,esk4_2(X28,X31),X31)!=X31|~m1_subset_1(X31,u1_struct_0(X28))|v13_lattices(X28)|(v2_struct_0(X28)|~l1_lattices(X28))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d13_lattices])])])])])])).
% 0.19/0.52  cnf(c_0_97, negated_conjecture, (r1_lattices(esk16_0,k15_lattice3(esk16_0,X1),k5_lattices(esk16_0))|~r2_hidden(k5_lattices(esk16_0),a_2_6_lattice3(esk16_0,a_2_2_lattice3(esk16_0,X1)))), inference(spm,[status(thm)],[c_0_90, c_0_91])).
% 0.19/0.52  cnf(c_0_98, negated_conjecture, (r2_hidden(k5_lattices(esk16_0),a_2_6_lattice3(esk16_0,X1))|~r2_hidden(k15_lattice3(esk16_0,k1_xboole_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_92]), c_0_75])])).
% 0.19/0.52  cnf(c_0_99, negated_conjecture, (r4_lattice3(esk16_0,k15_lattice3(esk16_0,X1),a_2_5_lattice3(esk16_0,X1))), inference(spm,[status(thm)],[c_0_72, c_0_93])).
% 0.19/0.52  fof(c_0_100, plain, ![X25, X26, X27]:((~r1_lattices(X25,X26,X27)|k2_lattices(X25,X26,X27)=X26|~m1_subset_1(X27,u1_struct_0(X25))|~m1_subset_1(X26,u1_struct_0(X25))|(v2_struct_0(X25)|~v8_lattices(X25)|~v9_lattices(X25)|~l3_lattices(X25)))&(k2_lattices(X25,X26,X27)!=X26|r1_lattices(X25,X26,X27)|~m1_subset_1(X27,u1_struct_0(X25))|~m1_subset_1(X26,u1_struct_0(X25))|(v2_struct_0(X25)|~v8_lattices(X25)|~v9_lattices(X25)|~l3_lattices(X25)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t21_lattices])])])])])).
% 0.19/0.52  cnf(c_0_101, plain, (v9_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_94])).
% 0.19/0.52  cnf(c_0_102, plain, (v8_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_94])).
% 0.19/0.52  cnf(c_0_103, negated_conjecture, (r1_lattices(esk16_0,X1,k15_lattice3(esk16_0,X2))|~r3_lattice3(esk16_0,X1,X3)|~m1_subset_1(X1,u1_struct_0(esk16_0))|~r2_hidden(k15_lattice3(esk16_0,X2),X3)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_52]), c_0_28])]), c_0_29])).
% 0.19/0.52  cnf(c_0_104, negated_conjecture, (r2_hidden(k15_lattice3(esk16_0,X1),a_2_6_lattice3(esk16_0,a_2_2_lattice3(esk16_0,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_95, c_0_82])).
% 0.19/0.52  cnf(c_0_105, plain, (m1_subset_1(esk4_2(X1,X2),u1_struct_0(X1))|v13_lattices(X1)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_96])).
% 0.19/0.52  fof(c_0_106, plain, ![X19, X20, X21]:(((k2_lattices(X19,X20,X21)=X20|~m1_subset_1(X21,u1_struct_0(X19))|X20!=k5_lattices(X19)|~m1_subset_1(X20,u1_struct_0(X19))|~v13_lattices(X19)|(v2_struct_0(X19)|~l1_lattices(X19)))&(k2_lattices(X19,X21,X20)=X20|~m1_subset_1(X21,u1_struct_0(X19))|X20!=k5_lattices(X19)|~m1_subset_1(X20,u1_struct_0(X19))|~v13_lattices(X19)|(v2_struct_0(X19)|~l1_lattices(X19))))&((m1_subset_1(esk2_2(X19,X20),u1_struct_0(X19))|X20=k5_lattices(X19)|~m1_subset_1(X20,u1_struct_0(X19))|~v13_lattices(X19)|(v2_struct_0(X19)|~l1_lattices(X19)))&(k2_lattices(X19,X20,esk2_2(X19,X20))!=X20|k2_lattices(X19,esk2_2(X19,X20),X20)!=X20|X20=k5_lattices(X19)|~m1_subset_1(X20,u1_struct_0(X19))|~v13_lattices(X19)|(v2_struct_0(X19)|~l1_lattices(X19))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattices])])])])])])).
% 0.19/0.52  cnf(c_0_107, negated_conjecture, (r1_lattices(esk16_0,k15_lattice3(esk16_0,X1),k5_lattices(esk16_0))|~r2_hidden(k15_lattice3(esk16_0,k1_xboole_0),a_2_2_lattice3(esk16_0,X1))), inference(spm,[status(thm)],[c_0_97, c_0_98])).
% 0.19/0.52  cnf(c_0_108, negated_conjecture, (r2_hidden(k15_lattice3(esk16_0,X1),X2)|~r1_tarski(a_2_2_lattice3(esk16_0,a_2_5_lattice3(esk16_0,X1)),X2)), inference(spm,[status(thm)],[c_0_71, c_0_99])).
% 0.19/0.52  cnf(c_0_109, plain, (k2_lattices(X1,X2,X3)=X2|v2_struct_0(X1)|~r1_lattices(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_100])).
% 0.19/0.52  cnf(c_0_110, negated_conjecture, (v9_lattices(esk16_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_39]), c_0_28])]), c_0_29])).
% 0.19/0.52  cnf(c_0_111, negated_conjecture, (v8_lattices(esk16_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_39]), c_0_28])]), c_0_29])).
% 0.19/0.52  cnf(c_0_112, negated_conjecture, (r1_lattices(esk16_0,X1,k15_lattice3(esk16_0,X2))|~r3_lattice3(esk16_0,X1,a_2_6_lattice3(esk16_0,a_2_2_lattice3(esk16_0,k1_xboole_0)))|~m1_subset_1(X1,u1_struct_0(esk16_0))), inference(spm,[status(thm)],[c_0_103, c_0_104])).
% 0.19/0.52  cnf(c_0_113, negated_conjecture, (m1_subset_1(esk4_2(esk16_0,k15_lattice3(esk16_0,X1)),u1_struct_0(esk16_0))|v13_lattices(esk16_0)|~l1_lattices(esk16_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_52]), c_0_29])).
% 0.19/0.52  cnf(c_0_114, plain, (k2_lattices(X1,X2,X3)=X3|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|X3!=k5_lattices(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~v13_lattices(X1)|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_106])).
% 0.19/0.52  cnf(c_0_115, negated_conjecture, (r1_lattices(esk16_0,k15_lattice3(esk16_0,X1),k5_lattices(esk16_0))|~r2_hidden(k15_lattice3(esk16_0,k1_xboole_0),a_2_2_lattice3(esk16_0,a_2_5_lattice3(esk16_0,X1)))), inference(spm,[status(thm)],[c_0_107, c_0_93])).
% 0.19/0.52  cnf(c_0_116, negated_conjecture, (r2_hidden(k15_lattice3(esk16_0,X1),a_2_2_lattice3(esk16_0,a_2_5_lattice3(esk16_0,X1)))), inference(spm,[status(thm)],[c_0_108, c_0_82])).
% 0.19/0.52  cnf(c_0_117, negated_conjecture, (k2_lattices(esk16_0,X1,k15_lattice3(esk16_0,X2))=X1|~r1_lattices(esk16_0,X1,k15_lattice3(esk16_0,X2))|~m1_subset_1(X1,u1_struct_0(esk16_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_52]), c_0_110]), c_0_111]), c_0_28])]), c_0_29])).
% 0.19/0.52  cnf(c_0_118, negated_conjecture, (r1_lattices(esk16_0,k15_lattice3(esk16_0,k1_xboole_0),k15_lattice3(esk16_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112, c_0_76]), c_0_77]), c_0_85]), c_0_77]), c_0_85]), c_0_52])])).
% 0.19/0.52  cnf(c_0_119, negated_conjecture, (m1_subset_1(esk4_2(esk16_0,k15_lattice3(esk16_0,X1)),u1_struct_0(esk16_0))|v13_lattices(esk16_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_55]), c_0_28])])).
% 0.19/0.52  cnf(c_0_120, plain, (k2_lattices(X1,X2,k5_lattices(X1))=k5_lattices(X1)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v13_lattices(X1)|~l1_lattices(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_114]), c_0_54])).
% 0.19/0.52  cnf(c_0_121, negated_conjecture, (k2_lattices(esk16_0,X1,k5_lattices(esk16_0))=X1|~r1_lattices(esk16_0,X1,k5_lattices(esk16_0))|~m1_subset_1(X1,u1_struct_0(esk16_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_75]), c_0_110]), c_0_111]), c_0_28])]), c_0_29])).
% 0.19/0.52  cnf(c_0_122, negated_conjecture, (r1_lattices(esk16_0,k15_lattice3(esk16_0,k1_xboole_0),k5_lattices(esk16_0))), inference(spm,[status(thm)],[c_0_115, c_0_116])).
% 0.19/0.52  cnf(c_0_123, negated_conjecture, (v2_struct_0(esk16_0)|~v10_lattices(esk16_0)|~v13_lattices(esk16_0)|~l3_lattices(esk16_0)|k5_lattices(esk16_0)!=k15_lattice3(esk16_0,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.52  cnf(c_0_124, negated_conjecture, (k2_lattices(esk16_0,k15_lattice3(esk16_0,k1_xboole_0),k15_lattice3(esk16_0,X1))=k15_lattice3(esk16_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_118]), c_0_52])])).
% 0.19/0.52  cnf(c_0_125, negated_conjecture, (k15_lattice3(esk16_0,a_2_3_lattice3(esk16_0,esk4_2(esk16_0,k15_lattice3(esk16_0,X1))))=esk4_2(esk16_0,k15_lattice3(esk16_0,X1))|v13_lattices(esk16_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_119]), c_0_38]), c_0_39]), c_0_28])]), c_0_29])).
% 0.19/0.52  cnf(c_0_126, negated_conjecture, (k2_lattices(esk16_0,k15_lattice3(esk16_0,X1),k5_lattices(esk16_0))=k5_lattices(esk16_0)|~v13_lattices(esk16_0)|~l1_lattices(esk16_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_120, c_0_52]), c_0_29])).
% 0.19/0.52  cnf(c_0_127, negated_conjecture, (k2_lattices(esk16_0,k15_lattice3(esk16_0,k1_xboole_0),k5_lattices(esk16_0))=k15_lattice3(esk16_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121, c_0_122]), c_0_52])])).
% 0.19/0.52  cnf(c_0_128, negated_conjecture, (k5_lattices(esk16_0)!=k15_lattice3(esk16_0,k1_xboole_0)|~v13_lattices(esk16_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_123, c_0_28]), c_0_39])]), c_0_29])).
% 0.19/0.52  fof(c_0_129, plain, ![X44, X45, X46]:((~v6_lattices(X44)|(~m1_subset_1(X45,u1_struct_0(X44))|(~m1_subset_1(X46,u1_struct_0(X44))|k2_lattices(X44,X45,X46)=k2_lattices(X44,X46,X45)))|(v2_struct_0(X44)|~l1_lattices(X44)))&((m1_subset_1(esk7_1(X44),u1_struct_0(X44))|v6_lattices(X44)|(v2_struct_0(X44)|~l1_lattices(X44)))&((m1_subset_1(esk8_1(X44),u1_struct_0(X44))|v6_lattices(X44)|(v2_struct_0(X44)|~l1_lattices(X44)))&(k2_lattices(X44,esk7_1(X44),esk8_1(X44))!=k2_lattices(X44,esk8_1(X44),esk7_1(X44))|v6_lattices(X44)|(v2_struct_0(X44)|~l1_lattices(X44)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d6_lattices])])])])])])).
% 0.19/0.52  cnf(c_0_130, plain, (v6_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_94])).
% 0.19/0.52  cnf(c_0_131, plain, (v13_lattices(X1)|v2_struct_0(X1)|k2_lattices(X1,X2,esk4_2(X1,X2))!=X2|k2_lattices(X1,esk4_2(X1,X2),X2)!=X2|~m1_subset_1(X2,u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_96])).
% 0.19/0.52  cnf(c_0_132, negated_conjecture, (k2_lattices(esk16_0,k15_lattice3(esk16_0,k1_xboole_0),esk4_2(esk16_0,k15_lattice3(esk16_0,X1)))=k15_lattice3(esk16_0,k1_xboole_0)|v13_lattices(esk16_0)), inference(spm,[status(thm)],[c_0_124, c_0_125])).
% 0.19/0.52  cnf(c_0_133, negated_conjecture, (~v13_lattices(esk16_0)|~l1_lattices(esk16_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_126, c_0_127]), c_0_128])).
% 0.19/0.52  cnf(c_0_134, plain, (k2_lattices(X1,X2,X3)=k2_lattices(X1,X3,X2)|v2_struct_0(X1)|~v6_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_129])).
% 0.19/0.52  cnf(c_0_135, negated_conjecture, (v6_lattices(esk16_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_130, c_0_39]), c_0_28])]), c_0_29])).
% 0.19/0.52  cnf(c_0_136, negated_conjecture, (k2_lattices(esk16_0,esk4_2(esk16_0,k15_lattice3(esk16_0,k1_xboole_0)),k15_lattice3(esk16_0,k1_xboole_0))!=k15_lattice3(esk16_0,k1_xboole_0)|~l1_lattices(esk16_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131, c_0_132]), c_0_52])]), c_0_29]), c_0_133])).
% 0.19/0.52  cnf(c_0_137, negated_conjecture, (k2_lattices(esk16_0,X1,esk4_2(esk16_0,k15_lattice3(esk16_0,X2)))=k2_lattices(esk16_0,esk4_2(esk16_0,k15_lattice3(esk16_0,X2)),X1)|~m1_subset_1(X1,u1_struct_0(esk16_0))|~l1_lattices(esk16_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134, c_0_119]), c_0_135])]), c_0_29]), c_0_133])).
% 0.19/0.52  cnf(c_0_138, negated_conjecture, (k2_lattices(esk16_0,k15_lattice3(esk16_0,k1_xboole_0),esk4_2(esk16_0,k15_lattice3(esk16_0,k1_xboole_0)))!=k15_lattice3(esk16_0,k1_xboole_0)|~l1_lattices(esk16_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_136, c_0_137]), c_0_52])])).
% 0.19/0.52  cnf(c_0_139, negated_conjecture, (~l1_lattices(esk16_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_138, c_0_132]), c_0_133])).
% 0.19/0.52  cnf(c_0_140, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_139, c_0_55]), c_0_28])]), ['proof']).
% 0.19/0.52  # SZS output end CNFRefutation
% 0.19/0.52  # Proof object total steps             : 141
% 0.19/0.52  # Proof object clause steps            : 96
% 0.19/0.52  # Proof object formula steps           : 45
% 0.19/0.52  # Proof object conjectures             : 64
% 0.19/0.52  # Proof object clause conjectures      : 61
% 0.19/0.52  # Proof object formula conjectures     : 3
% 0.19/0.52  # Proof object initial clauses used    : 31
% 0.19/0.52  # Proof object initial formulas used   : 22
% 0.19/0.52  # Proof object generating inferences   : 57
% 0.19/0.52  # Proof object simplifying inferences  : 123
% 0.19/0.52  # Training examples: 0 positive, 0 negative
% 0.19/0.52  # Parsed axioms                        : 26
% 0.19/0.52  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.52  # Initial clauses                      : 81
% 0.19/0.52  # Removed in clause preprocessing      : 1
% 0.19/0.52  # Initial clauses in saturation        : 80
% 0.19/0.52  # Processed clauses                    : 1945
% 0.19/0.52  # ...of these trivial                  : 74
% 0.19/0.52  # ...subsumed                          : 916
% 0.19/0.52  # ...remaining for further processing  : 955
% 0.19/0.52  # Other redundant clauses eliminated   : 11
% 0.19/0.52  # Clauses deleted for lack of memory   : 0
% 0.19/0.52  # Backward-subsumed                    : 39
% 0.19/0.52  # Backward-rewritten                   : 15
% 0.19/0.52  # Generated clauses                    : 6412
% 0.19/0.52  # ...of the previous two non-trivial   : 5663
% 0.19/0.52  # Contextual simplify-reflections      : 22
% 0.19/0.52  # Paramodulations                      : 6401
% 0.19/0.52  # Factorizations                       : 0
% 0.19/0.52  # Equation resolutions                 : 11
% 0.19/0.52  # Propositional unsat checks           : 0
% 0.19/0.52  #    Propositional check models        : 0
% 0.19/0.52  #    Propositional check unsatisfiable : 0
% 0.19/0.52  #    Propositional clauses             : 0
% 0.19/0.52  #    Propositional clauses after purity: 0
% 0.19/0.52  #    Propositional unsat core size     : 0
% 0.19/0.52  #    Propositional preprocessing time  : 0.000
% 0.19/0.52  #    Propositional encoding time       : 0.000
% 0.19/0.52  #    Propositional solver time         : 0.000
% 0.19/0.52  #    Success case prop preproc time    : 0.000
% 0.19/0.52  #    Success case prop encoding time   : 0.000
% 0.19/0.52  #    Success case prop solver time     : 0.000
% 0.19/0.52  # Current number of processed clauses  : 811
% 0.19/0.52  #    Positive orientable unit clauses  : 188
% 0.19/0.52  #    Positive unorientable unit clauses: 0
% 0.19/0.52  #    Negative unit clauses             : 28
% 0.19/0.52  #    Non-unit-clauses                  : 595
% 0.19/0.52  # Current number of unprocessed clauses: 3864
% 0.19/0.52  # ...number of literals in the above   : 11399
% 0.19/0.52  # Current number of archived formulas  : 0
% 0.19/0.52  # Current number of archived clauses   : 133
% 0.19/0.52  # Clause-clause subsumption calls (NU) : 27541
% 0.19/0.52  # Rec. Clause-clause subsumption calls : 17985
% 0.19/0.52  # Non-unit clause-clause subsumptions  : 932
% 0.19/0.52  # Unit Clause-clause subsumption calls : 8161
% 0.19/0.52  # Rewrite failures with RHS unbound    : 0
% 0.19/0.52  # BW rewrite match attempts            : 520
% 0.19/0.52  # BW rewrite match successes           : 15
% 0.19/0.52  # Condensation attempts                : 0
% 0.19/0.52  # Condensation successes               : 0
% 0.19/0.52  # Termbank termtop insertions          : 147452
% 0.19/0.52  
% 0.19/0.52  # -------------------------------------------------
% 0.19/0.52  # User time                : 0.174 s
% 0.19/0.52  # System time              : 0.010 s
% 0.19/0.52  # Total time               : 0.184 s
% 0.19/0.52  # Maximum resident set size: 1616 pages
%------------------------------------------------------------------------------
