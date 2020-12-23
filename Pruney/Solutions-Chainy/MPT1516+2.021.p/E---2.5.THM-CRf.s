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
% DateTime   : Thu Dec  3 11:15:09 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 510 expanded)
%              Number of clauses        :   52 ( 185 expanded)
%              Number of leaves         :   18 ( 128 expanded)
%              Depth                    :   20
%              Number of atoms          :  569 (3456 expanded)
%              Number of equality atoms :   57 ( 348 expanded)
%              Maximal formula depth    :   22 (   6 average)
%              Maximal clause size      :   40 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(fraenkel_a_2_5_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X2)
        & v10_lattices(X2)
        & v4_lattice3(X2)
        & l3_lattices(X2) )
     => ( r2_hidden(X1,a_2_5_lattice3(X2,X3))
      <=> ? [X4] :
            ( m1_subset_1(X4,u1_struct_0(X2))
            & X1 = X4
            & ? [X5] :
                ( m1_subset_1(X5,u1_struct_0(X2))
                & r3_lattices(X2,X4,X5)
                & r2_hidden(X5,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_5_lattice3)).

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

fof(t3_xboole_1,axiom,(
    ! [X1] :
      ( r1_tarski(X1,k1_xboole_0)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

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

fof(redefinition_r3_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & v8_lattices(X1)
        & v9_lattices(X1)
        & l3_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( r3_lattices(X1,X2,X3)
      <=> r1_lattices(X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_lattices)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

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

fof(dt_l3_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( l1_lattices(X1)
        & l2_lattices(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(c_0_18,plain,(
    ! [X6,X7,X8] :
      ( ( ~ v1_xboole_0(X6)
        | ~ r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_1(X8),X8)
        | v1_xboole_0(X8) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_19,plain,(
    ! [X10,X11,X12,X13,X14] :
      ( ( ~ r1_tarski(X10,X11)
        | ~ r2_hidden(X12,X10)
        | r2_hidden(X12,X11) )
      & ( r2_hidden(esk2_2(X13,X14),X13)
        | r1_tarski(X13,X14) )
      & ( ~ r2_hidden(esk2_2(X13,X14),X14)
        | r1_tarski(X13,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_20,plain,(
    ! [X42,X43,X44,X47,X48,X49] :
      ( ( m1_subset_1(esk8_3(X42,X43,X44),u1_struct_0(X43))
        | ~ r2_hidden(X42,a_2_5_lattice3(X43,X44))
        | v2_struct_0(X43)
        | ~ v10_lattices(X43)
        | ~ v4_lattice3(X43)
        | ~ l3_lattices(X43) )
      & ( X42 = esk8_3(X42,X43,X44)
        | ~ r2_hidden(X42,a_2_5_lattice3(X43,X44))
        | v2_struct_0(X43)
        | ~ v10_lattices(X43)
        | ~ v4_lattice3(X43)
        | ~ l3_lattices(X43) )
      & ( m1_subset_1(esk9_3(X42,X43,X44),u1_struct_0(X43))
        | ~ r2_hidden(X42,a_2_5_lattice3(X43,X44))
        | v2_struct_0(X43)
        | ~ v10_lattices(X43)
        | ~ v4_lattice3(X43)
        | ~ l3_lattices(X43) )
      & ( r3_lattices(X43,esk8_3(X42,X43,X44),esk9_3(X42,X43,X44))
        | ~ r2_hidden(X42,a_2_5_lattice3(X43,X44))
        | v2_struct_0(X43)
        | ~ v10_lattices(X43)
        | ~ v4_lattice3(X43)
        | ~ l3_lattices(X43) )
      & ( r2_hidden(esk9_3(X42,X43,X44),X44)
        | ~ r2_hidden(X42,a_2_5_lattice3(X43,X44))
        | v2_struct_0(X43)
        | ~ v10_lattices(X43)
        | ~ v4_lattice3(X43)
        | ~ l3_lattices(X43) )
      & ( ~ m1_subset_1(X48,u1_struct_0(X43))
        | X42 != X48
        | ~ m1_subset_1(X49,u1_struct_0(X43))
        | ~ r3_lattices(X43,X48,X49)
        | ~ r2_hidden(X49,X47)
        | r2_hidden(X42,a_2_5_lattice3(X43,X47))
        | v2_struct_0(X43)
        | ~ v10_lattices(X43)
        | ~ v4_lattice3(X43)
        | ~ l3_lattices(X43) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_5_lattice3])])])])])])])).

fof(c_0_21,negated_conjecture,(
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

fof(c_0_22,plain,(
    ! [X16] :
      ( ~ r1_tarski(X16,k1_xboole_0)
      | X16 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).

cnf(c_0_23,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( r2_hidden(esk9_3(X1,X2,X3),X3)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_5_lattice3(X2,X3))
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_26,plain,(
    ! [X54,X55,X56,X58] :
      ( ( m1_subset_1(esk10_3(X54,X55,X56),u1_struct_0(X54))
        | r3_lattices(X54,k15_lattice3(X54,X55),k15_lattice3(X54,X56))
        | v2_struct_0(X54)
        | ~ v10_lattices(X54)
        | ~ v4_lattice3(X54)
        | ~ l3_lattices(X54) )
      & ( r2_hidden(esk10_3(X54,X55,X56),X55)
        | r3_lattices(X54,k15_lattice3(X54,X55),k15_lattice3(X54,X56))
        | v2_struct_0(X54)
        | ~ v10_lattices(X54)
        | ~ v4_lattice3(X54)
        | ~ l3_lattices(X54) )
      & ( ~ m1_subset_1(X58,u1_struct_0(X54))
        | ~ r3_lattices(X54,esk10_3(X54,X55,X56),X58)
        | ~ r2_hidden(X58,X56)
        | r3_lattices(X54,k15_lattice3(X54,X55),k15_lattice3(X54,X56))
        | v2_struct_0(X54)
        | ~ v10_lattices(X54)
        | ~ v4_lattice3(X54)
        | ~ l3_lattices(X54) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t48_lattice3])])])])])])).

fof(c_0_27,negated_conjecture,
    ( ~ v2_struct_0(esk11_0)
    & v10_lattices(esk11_0)
    & v4_lattice3(esk11_0)
    & l3_lattices(esk11_0)
    & ( v2_struct_0(esk11_0)
      | ~ v10_lattices(esk11_0)
      | ~ v13_lattices(esk11_0)
      | ~ l3_lattices(esk11_0)
      | k5_lattices(esk11_0) != k15_lattice3(esk11_0,k1_xboole_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_21])])])])).

cnf(c_0_28,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_30,plain,
    ( v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ r2_hidden(X2,a_2_5_lattice3(X1,X3))
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_23,c_0_25])).

cnf(c_0_31,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_32,plain,
    ( r2_hidden(esk10_3(X1,X2,X3),X2)
    | r3_lattices(X1,k15_lattice3(X1,X2),k15_lattice3(X1,X3))
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,negated_conjecture,
    ( v4_lattice3(esk11_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( v10_lattices(esk11_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,negated_conjecture,
    ( l3_lattices(esk11_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,negated_conjecture,
    ( ~ v2_struct_0(esk11_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_37,plain,(
    ! [X52,X53] :
      ( ( k15_lattice3(X52,X53) = k15_lattice3(X52,a_2_5_lattice3(X52,X53))
        | v2_struct_0(X52)
        | ~ v10_lattices(X52)
        | ~ v4_lattice3(X52)
        | ~ l3_lattices(X52) )
      & ( k16_lattice3(X52,X53) = k16_lattice3(X52,a_2_6_lattice3(X52,X53))
        | v2_struct_0(X52)
        | ~ v10_lattices(X52)
        | ~ v4_lattice3(X52)
        | ~ l3_lattices(X52) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t47_lattice3])])])])])).

cnf(c_0_38,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_39,plain,
    ( v2_struct_0(X1)
    | v1_xboole_0(a_2_5_lattice3(X1,X2))
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_40,negated_conjecture,
    ( r3_lattices(esk11_0,k15_lattice3(esk11_0,X1),k15_lattice3(esk11_0,X2))
    | r2_hidden(esk10_3(esk11_0,X1,X2),X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_41,plain,
    ( k15_lattice3(X1,X2) = k15_lattice3(X1,a_2_5_lattice3(X1,X2))
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_42,plain,
    ( a_2_5_lattice3(X1,X2) = k1_xboole_0
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_43,negated_conjecture,
    ( r3_lattices(esk11_0,k15_lattice3(esk11_0,X1),k15_lattice3(esk11_0,X2))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_40])).

cnf(c_0_44,plain,
    ( k15_lattice3(X1,k1_xboole_0) = k15_lattice3(X1,X2)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

fof(c_0_45,plain,(
    ! [X27,X28,X29] :
      ( ( ~ r1_lattices(X27,X28,X29)
        | k2_lattices(X27,X28,X29) = X28
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | ~ m1_subset_1(X28,u1_struct_0(X27))
        | v2_struct_0(X27)
        | ~ v8_lattices(X27)
        | ~ v9_lattices(X27)
        | ~ l3_lattices(X27) )
      & ( k2_lattices(X27,X28,X29) != X28
        | r1_lattices(X27,X28,X29)
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | ~ m1_subset_1(X28,u1_struct_0(X27))
        | v2_struct_0(X27)
        | ~ v8_lattices(X27)
        | ~ v9_lattices(X27)
        | ~ l3_lattices(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t21_lattices])])])])])).

fof(c_0_46,plain,(
    ! [X24,X25,X26] :
      ( ( ~ r3_lattices(X24,X25,X26)
        | r1_lattices(X24,X25,X26)
        | v2_struct_0(X24)
        | ~ v6_lattices(X24)
        | ~ v8_lattices(X24)
        | ~ v9_lattices(X24)
        | ~ l3_lattices(X24)
        | ~ m1_subset_1(X25,u1_struct_0(X24))
        | ~ m1_subset_1(X26,u1_struct_0(X24)) )
      & ( ~ r1_lattices(X24,X25,X26)
        | r3_lattices(X24,X25,X26)
        | v2_struct_0(X24)
        | ~ v6_lattices(X24)
        | ~ v8_lattices(X24)
        | ~ v9_lattices(X24)
        | ~ l3_lattices(X24)
        | ~ m1_subset_1(X25,u1_struct_0(X24))
        | ~ m1_subset_1(X26,u1_struct_0(X24)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).

cnf(c_0_47,negated_conjecture,
    ( r3_lattices(esk11_0,k15_lattice3(esk11_0,k1_xboole_0),k15_lattice3(esk11_0,X1))
    | ~ v1_xboole_0(X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_33]),c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_48,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

fof(c_0_49,plain,(
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

fof(c_0_50,plain,(
    ! [X18,X19,X20] :
      ( ( k2_lattices(X18,X19,X20) = X19
        | ~ m1_subset_1(X20,u1_struct_0(X18))
        | X19 != k5_lattices(X18)
        | ~ m1_subset_1(X19,u1_struct_0(X18))
        | ~ v13_lattices(X18)
        | v2_struct_0(X18)
        | ~ l1_lattices(X18) )
      & ( k2_lattices(X18,X20,X19) = X19
        | ~ m1_subset_1(X20,u1_struct_0(X18))
        | X19 != k5_lattices(X18)
        | ~ m1_subset_1(X19,u1_struct_0(X18))
        | ~ v13_lattices(X18)
        | v2_struct_0(X18)
        | ~ l1_lattices(X18) )
      & ( m1_subset_1(esk3_2(X18,X19),u1_struct_0(X18))
        | X19 = k5_lattices(X18)
        | ~ m1_subset_1(X19,u1_struct_0(X18))
        | ~ v13_lattices(X18)
        | v2_struct_0(X18)
        | ~ l1_lattices(X18) )
      & ( k2_lattices(X18,X19,esk3_2(X18,X19)) != X19
        | k2_lattices(X18,esk3_2(X18,X19),X19) != X19
        | X19 = k5_lattices(X18)
        | ~ m1_subset_1(X19,u1_struct_0(X18))
        | ~ v13_lattices(X18)
        | v2_struct_0(X18)
        | ~ l1_lattices(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattices])])])])])])).

fof(c_0_51,plain,(
    ! [X22] :
      ( v2_struct_0(X22)
      | ~ l1_lattices(X22)
      | m1_subset_1(k5_lattices(X22),u1_struct_0(X22)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_lattices])])])).

cnf(c_0_52,plain,
    ( k2_lattices(X1,X2,X3) = X2
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_53,plain,
    ( r1_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_54,negated_conjecture,
    ( r3_lattices(esk11_0,k15_lattice3(esk11_0,k1_xboole_0),k15_lattice3(esk11_0,X1)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_55,plain,
    ( X1 = k15_lattice3(X2,a_2_3_lattice3(X2,X1))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_56,plain,
    ( k2_lattices(X1,X2,X3) = X3
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | X3 != k5_lattices(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v13_lattices(X1)
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_57,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_58,plain,
    ( k2_lattices(X1,X2,X3) = X2
    | v2_struct_0(X1)
    | ~ r3_lattices(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v9_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v6_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_59,negated_conjecture,
    ( r3_lattices(esk11_0,k15_lattice3(esk11_0,k1_xboole_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk11_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_33]),c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_60,negated_conjecture,
    ( v2_struct_0(esk11_0)
    | ~ v10_lattices(esk11_0)
    | ~ v13_lattices(esk11_0)
    | ~ l3_lattices(esk11_0)
    | k5_lattices(esk11_0) != k15_lattice3(esk11_0,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_61,plain,
    ( k2_lattices(X1,X2,k5_lattices(X1)) = k5_lattices(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v13_lattices(X1)
    | ~ l1_lattices(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_56]),c_0_57])).

cnf(c_0_62,negated_conjecture,
    ( k2_lattices(esk11_0,k15_lattice3(esk11_0,k1_xboole_0),X1) = k15_lattice3(esk11_0,k1_xboole_0)
    | ~ m1_subset_1(k15_lattice3(esk11_0,k1_xboole_0),u1_struct_0(esk11_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk11_0))
    | ~ v9_lattices(esk11_0)
    | ~ v8_lattices(esk11_0)
    | ~ v6_lattices(esk11_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_35])]),c_0_36])).

cnf(c_0_63,negated_conjecture,
    ( k15_lattice3(esk11_0,k1_xboole_0) != k5_lattices(esk11_0)
    | ~ v13_lattices(esk11_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_35]),c_0_34])]),c_0_36])).

fof(c_0_64,plain,(
    ! [X40,X41] :
      ( v2_struct_0(X40)
      | ~ l3_lattices(X40)
      | m1_subset_1(k15_lattice3(X40,X41),u1_struct_0(X40)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k15_lattice3])])])).

fof(c_0_65,plain,(
    ! [X30,X32,X33] :
      ( ( m1_subset_1(esk4_1(X30),u1_struct_0(X30))
        | ~ v13_lattices(X30)
        | v2_struct_0(X30)
        | ~ l1_lattices(X30) )
      & ( k2_lattices(X30,esk4_1(X30),X32) = esk4_1(X30)
        | ~ m1_subset_1(X32,u1_struct_0(X30))
        | ~ v13_lattices(X30)
        | v2_struct_0(X30)
        | ~ l1_lattices(X30) )
      & ( k2_lattices(X30,X32,esk4_1(X30)) = esk4_1(X30)
        | ~ m1_subset_1(X32,u1_struct_0(X30))
        | ~ v13_lattices(X30)
        | v2_struct_0(X30)
        | ~ l1_lattices(X30) )
      & ( m1_subset_1(esk5_2(X30,X33),u1_struct_0(X30))
        | ~ m1_subset_1(X33,u1_struct_0(X30))
        | v13_lattices(X30)
        | v2_struct_0(X30)
        | ~ l1_lattices(X30) )
      & ( k2_lattices(X30,X33,esk5_2(X30,X33)) != X33
        | k2_lattices(X30,esk5_2(X30,X33),X33) != X33
        | ~ m1_subset_1(X33,u1_struct_0(X30))
        | v13_lattices(X30)
        | v2_struct_0(X30)
        | ~ l1_lattices(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d13_lattices])])])])])])).

fof(c_0_66,plain,(
    ! [X35,X36,X37] :
      ( ( ~ v6_lattices(X35)
        | ~ m1_subset_1(X36,u1_struct_0(X35))
        | ~ m1_subset_1(X37,u1_struct_0(X35))
        | k2_lattices(X35,X36,X37) = k2_lattices(X35,X37,X36)
        | v2_struct_0(X35)
        | ~ l1_lattices(X35) )
      & ( m1_subset_1(esk6_1(X35),u1_struct_0(X35))
        | v6_lattices(X35)
        | v2_struct_0(X35)
        | ~ l1_lattices(X35) )
      & ( m1_subset_1(esk7_1(X35),u1_struct_0(X35))
        | v6_lattices(X35)
        | v2_struct_0(X35)
        | ~ l1_lattices(X35) )
      & ( k2_lattices(X35,esk6_1(X35),esk7_1(X35)) != k2_lattices(X35,esk7_1(X35),esk6_1(X35))
        | v6_lattices(X35)
        | v2_struct_0(X35)
        | ~ l1_lattices(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d6_lattices])])])])])])).

cnf(c_0_67,negated_conjecture,
    ( ~ m1_subset_1(k15_lattice3(esk11_0,k1_xboole_0),u1_struct_0(esk11_0))
    | ~ m1_subset_1(k5_lattices(esk11_0),u1_struct_0(esk11_0))
    | ~ v13_lattices(esk11_0)
    | ~ l1_lattices(esk11_0)
    | ~ v9_lattices(esk11_0)
    | ~ v8_lattices(esk11_0)
    | ~ v6_lattices(esk11_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_36]),c_0_63])).

cnf(c_0_68,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_69,plain,
    ( v13_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,esk5_2(X1,X2)) != X2
    | k2_lattices(X1,esk5_2(X1,X2),X2) != X2
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_70,plain,
    ( k2_lattices(X1,X2,X3) = k2_lattices(X1,X3,X2)
    | v2_struct_0(X1)
    | ~ v6_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_71,plain,
    ( m1_subset_1(esk5_2(X1,X2),u1_struct_0(X1))
    | v13_lattices(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_72,negated_conjecture,
    ( ~ m1_subset_1(k5_lattices(esk11_0),u1_struct_0(esk11_0))
    | ~ v13_lattices(esk11_0)
    | ~ l1_lattices(esk11_0)
    | ~ v9_lattices(esk11_0)
    | ~ v8_lattices(esk11_0)
    | ~ v6_lattices(esk11_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_35])]),c_0_36])).

cnf(c_0_73,plain,
    ( v13_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,esk5_2(X1,X2)) != X2
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v6_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71])).

cnf(c_0_74,negated_conjecture,
    ( ~ v13_lattices(esk11_0)
    | ~ l1_lattices(esk11_0)
    | ~ v9_lattices(esk11_0)
    | ~ v8_lattices(esk11_0)
    | ~ v6_lattices(esk11_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_57]),c_0_36])).

cnf(c_0_75,negated_conjecture,
    ( ~ m1_subset_1(esk5_2(esk11_0,k15_lattice3(esk11_0,k1_xboole_0)),u1_struct_0(esk11_0))
    | ~ m1_subset_1(k15_lattice3(esk11_0,k1_xboole_0),u1_struct_0(esk11_0))
    | ~ l1_lattices(esk11_0)
    | ~ v9_lattices(esk11_0)
    | ~ v8_lattices(esk11_0)
    | ~ v6_lattices(esk11_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_62]),c_0_36]),c_0_74])).

cnf(c_0_76,negated_conjecture,
    ( ~ m1_subset_1(k15_lattice3(esk11_0,k1_xboole_0),u1_struct_0(esk11_0))
    | ~ l1_lattices(esk11_0)
    | ~ v9_lattices(esk11_0)
    | ~ v8_lattices(esk11_0)
    | ~ v6_lattices(esk11_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_71]),c_0_36]),c_0_74])).

fof(c_0_77,plain,(
    ! [X17] :
      ( ( ~ v2_struct_0(X17)
        | v2_struct_0(X17)
        | ~ v10_lattices(X17)
        | ~ l3_lattices(X17) )
      & ( v4_lattices(X17)
        | v2_struct_0(X17)
        | ~ v10_lattices(X17)
        | ~ l3_lattices(X17) )
      & ( v5_lattices(X17)
        | v2_struct_0(X17)
        | ~ v10_lattices(X17)
        | ~ l3_lattices(X17) )
      & ( v6_lattices(X17)
        | v2_struct_0(X17)
        | ~ v10_lattices(X17)
        | ~ l3_lattices(X17) )
      & ( v7_lattices(X17)
        | v2_struct_0(X17)
        | ~ v10_lattices(X17)
        | ~ l3_lattices(X17) )
      & ( v8_lattices(X17)
        | v2_struct_0(X17)
        | ~ v10_lattices(X17)
        | ~ l3_lattices(X17) )
      & ( v9_lattices(X17)
        | v2_struct_0(X17)
        | ~ v10_lattices(X17)
        | ~ l3_lattices(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).

cnf(c_0_78,negated_conjecture,
    ( ~ l1_lattices(esk11_0)
    | ~ v9_lattices(esk11_0)
    | ~ v8_lattices(esk11_0)
    | ~ v6_lattices(esk11_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_68]),c_0_35])]),c_0_36])).

cnf(c_0_79,plain,
    ( v9_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_80,negated_conjecture,
    ( ~ l1_lattices(esk11_0)
    | ~ v8_lattices(esk11_0)
    | ~ v6_lattices(esk11_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_81,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_82,negated_conjecture,
    ( ~ l1_lattices(esk11_0)
    | ~ v6_lattices(esk11_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_83,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

fof(c_0_84,plain,(
    ! [X23] :
      ( ( l1_lattices(X23)
        | ~ l3_lattices(X23) )
      & ( l2_lattices(X23)
        | ~ l3_lattices(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).

cnf(c_0_85,negated_conjecture,
    ( ~ l1_lattices(esk11_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_86,plain,
    ( l1_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_87,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_35])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:53:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.37  # AutoSched0-Mode selected heuristic G_E___207_C01_F1_SE_CS_SP_PI_S5PRR_S0Y
% 0.20/0.37  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.37  #
% 0.20/0.37  # Preprocessing time       : 0.018 s
% 0.20/0.37  
% 0.20/0.37  # Proof found!
% 0.20/0.37  # SZS status Theorem
% 0.20/0.37  # SZS output start CNFRefutation
% 0.20/0.37  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.20/0.37  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.37  fof(fraenkel_a_2_5_lattice3, axiom, ![X1, X2, X3]:((((~(v2_struct_0(X2))&v10_lattices(X2))&v4_lattice3(X2))&l3_lattices(X2))=>(r2_hidden(X1,a_2_5_lattice3(X2,X3))<=>?[X4]:((m1_subset_1(X4,u1_struct_0(X2))&X1=X4)&?[X5]:((m1_subset_1(X5,u1_struct_0(X2))&r3_lattices(X2,X4,X5))&r2_hidden(X5,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_5_lattice3)).
% 0.20/0.37  fof(t50_lattice3, conjecture, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>((((~(v2_struct_0(X1))&v10_lattices(X1))&v13_lattices(X1))&l3_lattices(X1))&k5_lattices(X1)=k15_lattice3(X1,k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_lattice3)).
% 0.20/0.37  fof(t3_xboole_1, axiom, ![X1]:(r1_tarski(X1,k1_xboole_0)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 0.20/0.37  fof(t48_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2, X3]:(![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>~((r2_hidden(X4,X2)&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>~((r3_lattices(X1,X4,X5)&r2_hidden(X5,X3)))))))=>r3_lattices(X1,k15_lattice3(X1,X2),k15_lattice3(X1,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_lattice3)).
% 0.20/0.37  fof(t47_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(k15_lattice3(X1,X2)=k15_lattice3(X1,a_2_5_lattice3(X1,X2))&k16_lattice3(X1,X2)=k16_lattice3(X1,a_2_6_lattice3(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_lattice3)).
% 0.20/0.37  fof(t21_lattices, axiom, ![X1]:((((~(v2_struct_0(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_lattices(X1,X2,X3)<=>k2_lattices(X1,X2,X3)=X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_lattices)).
% 0.20/0.37  fof(redefinition_r3_lattices, axiom, ![X1, X2, X3]:(((((((~(v2_struct_0(X1))&v6_lattices(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>(r3_lattices(X1,X2,X3)<=>r1_lattices(X1,X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 0.20/0.37  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.20/0.37  fof(t45_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(X2=k15_lattice3(X1,a_2_3_lattice3(X1,X2))&X2=k16_lattice3(X1,a_2_4_lattice3(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_lattice3)).
% 0.20/0.37  fof(d16_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>(v13_lattices(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(X2=k5_lattices(X1)<=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(k2_lattices(X1,X2,X3)=X2&k2_lattices(X1,X3,X2)=X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_lattices)).
% 0.20/0.37  fof(dt_k5_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>m1_subset_1(k5_lattices(X1),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_lattices)).
% 0.20/0.37  fof(dt_k15_lattice3, axiom, ![X1, X2]:((~(v2_struct_0(X1))&l3_lattices(X1))=>m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k15_lattice3)).
% 0.20/0.37  fof(d13_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>(v13_lattices(X1)<=>?[X2]:(m1_subset_1(X2,u1_struct_0(X1))&![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(k2_lattices(X1,X2,X3)=X2&k2_lattices(X1,X3,X2)=X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_lattices)).
% 0.20/0.37  fof(d6_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>(v6_lattices(X1)<=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>k2_lattices(X1,X2,X3)=k2_lattices(X1,X3,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_lattices)).
% 0.20/0.37  fof(cc1_lattices, axiom, ![X1]:(l3_lattices(X1)=>((~(v2_struct_0(X1))&v10_lattices(X1))=>((((((~(v2_struct_0(X1))&v4_lattices(X1))&v5_lattices(X1))&v6_lattices(X1))&v7_lattices(X1))&v8_lattices(X1))&v9_lattices(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattices)).
% 0.20/0.37  fof(dt_l3_lattices, axiom, ![X1]:(l3_lattices(X1)=>(l1_lattices(X1)&l2_lattices(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l3_lattices)).
% 0.20/0.37  fof(c_0_18, plain, ![X6, X7, X8]:((~v1_xboole_0(X6)|~r2_hidden(X7,X6))&(r2_hidden(esk1_1(X8),X8)|v1_xboole_0(X8))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.20/0.37  fof(c_0_19, plain, ![X10, X11, X12, X13, X14]:((~r1_tarski(X10,X11)|(~r2_hidden(X12,X10)|r2_hidden(X12,X11)))&((r2_hidden(esk2_2(X13,X14),X13)|r1_tarski(X13,X14))&(~r2_hidden(esk2_2(X13,X14),X14)|r1_tarski(X13,X14)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.37  fof(c_0_20, plain, ![X42, X43, X44, X47, X48, X49]:((((m1_subset_1(esk8_3(X42,X43,X44),u1_struct_0(X43))|~r2_hidden(X42,a_2_5_lattice3(X43,X44))|(v2_struct_0(X43)|~v10_lattices(X43)|~v4_lattice3(X43)|~l3_lattices(X43)))&(X42=esk8_3(X42,X43,X44)|~r2_hidden(X42,a_2_5_lattice3(X43,X44))|(v2_struct_0(X43)|~v10_lattices(X43)|~v4_lattice3(X43)|~l3_lattices(X43))))&(((m1_subset_1(esk9_3(X42,X43,X44),u1_struct_0(X43))|~r2_hidden(X42,a_2_5_lattice3(X43,X44))|(v2_struct_0(X43)|~v10_lattices(X43)|~v4_lattice3(X43)|~l3_lattices(X43)))&(r3_lattices(X43,esk8_3(X42,X43,X44),esk9_3(X42,X43,X44))|~r2_hidden(X42,a_2_5_lattice3(X43,X44))|(v2_struct_0(X43)|~v10_lattices(X43)|~v4_lattice3(X43)|~l3_lattices(X43))))&(r2_hidden(esk9_3(X42,X43,X44),X44)|~r2_hidden(X42,a_2_5_lattice3(X43,X44))|(v2_struct_0(X43)|~v10_lattices(X43)|~v4_lattice3(X43)|~l3_lattices(X43)))))&(~m1_subset_1(X48,u1_struct_0(X43))|X42!=X48|(~m1_subset_1(X49,u1_struct_0(X43))|~r3_lattices(X43,X48,X49)|~r2_hidden(X49,X47))|r2_hidden(X42,a_2_5_lattice3(X43,X47))|(v2_struct_0(X43)|~v10_lattices(X43)|~v4_lattice3(X43)|~l3_lattices(X43)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_5_lattice3])])])])])])])).
% 0.20/0.37  fof(c_0_21, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>((((~(v2_struct_0(X1))&v10_lattices(X1))&v13_lattices(X1))&l3_lattices(X1))&k5_lattices(X1)=k15_lattice3(X1,k1_xboole_0)))), inference(assume_negation,[status(cth)],[t50_lattice3])).
% 0.20/0.37  fof(c_0_22, plain, ![X16]:(~r1_tarski(X16,k1_xboole_0)|X16=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).
% 0.20/0.37  cnf(c_0_23, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.37  cnf(c_0_24, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.37  cnf(c_0_25, plain, (r2_hidden(esk9_3(X1,X2,X3),X3)|v2_struct_0(X2)|~r2_hidden(X1,a_2_5_lattice3(X2,X3))|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.37  fof(c_0_26, plain, ![X54, X55, X56, X58]:((m1_subset_1(esk10_3(X54,X55,X56),u1_struct_0(X54))|r3_lattices(X54,k15_lattice3(X54,X55),k15_lattice3(X54,X56))|(v2_struct_0(X54)|~v10_lattices(X54)|~v4_lattice3(X54)|~l3_lattices(X54)))&((r2_hidden(esk10_3(X54,X55,X56),X55)|r3_lattices(X54,k15_lattice3(X54,X55),k15_lattice3(X54,X56))|(v2_struct_0(X54)|~v10_lattices(X54)|~v4_lattice3(X54)|~l3_lattices(X54)))&(~m1_subset_1(X58,u1_struct_0(X54))|(~r3_lattices(X54,esk10_3(X54,X55,X56),X58)|~r2_hidden(X58,X56))|r3_lattices(X54,k15_lattice3(X54,X55),k15_lattice3(X54,X56))|(v2_struct_0(X54)|~v10_lattices(X54)|~v4_lattice3(X54)|~l3_lattices(X54))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t48_lattice3])])])])])])).
% 0.20/0.37  fof(c_0_27, negated_conjecture, ((((~v2_struct_0(esk11_0)&v10_lattices(esk11_0))&v4_lattice3(esk11_0))&l3_lattices(esk11_0))&(v2_struct_0(esk11_0)|~v10_lattices(esk11_0)|~v13_lattices(esk11_0)|~l3_lattices(esk11_0)|k5_lattices(esk11_0)!=k15_lattice3(esk11_0,k1_xboole_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_21])])])])).
% 0.20/0.37  cnf(c_0_28, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.37  cnf(c_0_29, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.20/0.37  cnf(c_0_30, plain, (v2_struct_0(X1)|~v4_lattice3(X1)|~v10_lattices(X1)|~l3_lattices(X1)|~r2_hidden(X2,a_2_5_lattice3(X1,X3))|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_23, c_0_25])).
% 0.20/0.37  cnf(c_0_31, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.37  cnf(c_0_32, plain, (r2_hidden(esk10_3(X1,X2,X3),X2)|r3_lattices(X1,k15_lattice3(X1,X2),k15_lattice3(X1,X3))|v2_struct_0(X1)|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.37  cnf(c_0_33, negated_conjecture, (v4_lattice3(esk11_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.37  cnf(c_0_34, negated_conjecture, (v10_lattices(esk11_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.37  cnf(c_0_35, negated_conjecture, (l3_lattices(esk11_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.37  cnf(c_0_36, negated_conjecture, (~v2_struct_0(esk11_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.37  fof(c_0_37, plain, ![X52, X53]:((k15_lattice3(X52,X53)=k15_lattice3(X52,a_2_5_lattice3(X52,X53))|(v2_struct_0(X52)|~v10_lattices(X52)|~v4_lattice3(X52)|~l3_lattices(X52)))&(k16_lattice3(X52,X53)=k16_lattice3(X52,a_2_6_lattice3(X52,X53))|(v2_struct_0(X52)|~v10_lattices(X52)|~v4_lattice3(X52)|~l3_lattices(X52)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t47_lattice3])])])])])).
% 0.20/0.37  cnf(c_0_38, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.20/0.37  cnf(c_0_39, plain, (v2_struct_0(X1)|v1_xboole_0(a_2_5_lattice3(X1,X2))|~v4_lattice3(X1)|~v10_lattices(X1)|~l3_lattices(X1)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.20/0.37  cnf(c_0_40, negated_conjecture, (r3_lattices(esk11_0,k15_lattice3(esk11_0,X1),k15_lattice3(esk11_0,X2))|r2_hidden(esk10_3(esk11_0,X1,X2),X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34]), c_0_35])]), c_0_36])).
% 0.20/0.37  cnf(c_0_41, plain, (k15_lattice3(X1,X2)=k15_lattice3(X1,a_2_5_lattice3(X1,X2))|v2_struct_0(X1)|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.37  cnf(c_0_42, plain, (a_2_5_lattice3(X1,X2)=k1_xboole_0|v2_struct_0(X1)|~v4_lattice3(X1)|~v10_lattices(X1)|~l3_lattices(X1)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.20/0.37  cnf(c_0_43, negated_conjecture, (r3_lattices(esk11_0,k15_lattice3(esk11_0,X1),k15_lattice3(esk11_0,X2))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_23, c_0_40])).
% 0.20/0.37  cnf(c_0_44, plain, (k15_lattice3(X1,k1_xboole_0)=k15_lattice3(X1,X2)|v2_struct_0(X1)|~v4_lattice3(X1)|~v10_lattices(X1)|~l3_lattices(X1)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.20/0.37  fof(c_0_45, plain, ![X27, X28, X29]:((~r1_lattices(X27,X28,X29)|k2_lattices(X27,X28,X29)=X28|~m1_subset_1(X29,u1_struct_0(X27))|~m1_subset_1(X28,u1_struct_0(X27))|(v2_struct_0(X27)|~v8_lattices(X27)|~v9_lattices(X27)|~l3_lattices(X27)))&(k2_lattices(X27,X28,X29)!=X28|r1_lattices(X27,X28,X29)|~m1_subset_1(X29,u1_struct_0(X27))|~m1_subset_1(X28,u1_struct_0(X27))|(v2_struct_0(X27)|~v8_lattices(X27)|~v9_lattices(X27)|~l3_lattices(X27)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t21_lattices])])])])])).
% 0.20/0.37  fof(c_0_46, plain, ![X24, X25, X26]:((~r3_lattices(X24,X25,X26)|r1_lattices(X24,X25,X26)|(v2_struct_0(X24)|~v6_lattices(X24)|~v8_lattices(X24)|~v9_lattices(X24)|~l3_lattices(X24)|~m1_subset_1(X25,u1_struct_0(X24))|~m1_subset_1(X26,u1_struct_0(X24))))&(~r1_lattices(X24,X25,X26)|r3_lattices(X24,X25,X26)|(v2_struct_0(X24)|~v6_lattices(X24)|~v8_lattices(X24)|~v9_lattices(X24)|~l3_lattices(X24)|~m1_subset_1(X25,u1_struct_0(X24))|~m1_subset_1(X26,u1_struct_0(X24))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).
% 0.20/0.37  cnf(c_0_47, negated_conjecture, (r3_lattices(esk11_0,k15_lattice3(esk11_0,k1_xboole_0),k15_lattice3(esk11_0,X1))|~v1_xboole_0(X2)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_33]), c_0_34]), c_0_35])]), c_0_36])).
% 0.20/0.37  cnf(c_0_48, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.20/0.37  fof(c_0_49, plain, ![X50, X51]:((X51=k15_lattice3(X50,a_2_3_lattice3(X50,X51))|~m1_subset_1(X51,u1_struct_0(X50))|(v2_struct_0(X50)|~v10_lattices(X50)|~v4_lattice3(X50)|~l3_lattices(X50)))&(X51=k16_lattice3(X50,a_2_4_lattice3(X50,X51))|~m1_subset_1(X51,u1_struct_0(X50))|(v2_struct_0(X50)|~v10_lattices(X50)|~v4_lattice3(X50)|~l3_lattices(X50)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t45_lattice3])])])])])).
% 0.20/0.37  fof(c_0_50, plain, ![X18, X19, X20]:(((k2_lattices(X18,X19,X20)=X19|~m1_subset_1(X20,u1_struct_0(X18))|X19!=k5_lattices(X18)|~m1_subset_1(X19,u1_struct_0(X18))|~v13_lattices(X18)|(v2_struct_0(X18)|~l1_lattices(X18)))&(k2_lattices(X18,X20,X19)=X19|~m1_subset_1(X20,u1_struct_0(X18))|X19!=k5_lattices(X18)|~m1_subset_1(X19,u1_struct_0(X18))|~v13_lattices(X18)|(v2_struct_0(X18)|~l1_lattices(X18))))&((m1_subset_1(esk3_2(X18,X19),u1_struct_0(X18))|X19=k5_lattices(X18)|~m1_subset_1(X19,u1_struct_0(X18))|~v13_lattices(X18)|(v2_struct_0(X18)|~l1_lattices(X18)))&(k2_lattices(X18,X19,esk3_2(X18,X19))!=X19|k2_lattices(X18,esk3_2(X18,X19),X19)!=X19|X19=k5_lattices(X18)|~m1_subset_1(X19,u1_struct_0(X18))|~v13_lattices(X18)|(v2_struct_0(X18)|~l1_lattices(X18))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattices])])])])])])).
% 0.20/0.37  fof(c_0_51, plain, ![X22]:(v2_struct_0(X22)|~l1_lattices(X22)|m1_subset_1(k5_lattices(X22),u1_struct_0(X22))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_lattices])])])).
% 0.20/0.37  cnf(c_0_52, plain, (k2_lattices(X1,X2,X3)=X2|v2_struct_0(X1)|~r1_lattices(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.20/0.37  cnf(c_0_53, plain, (r1_lattices(X1,X2,X3)|v2_struct_0(X1)|~r3_lattices(X1,X2,X3)|~v6_lattices(X1)|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.20/0.37  cnf(c_0_54, negated_conjecture, (r3_lattices(esk11_0,k15_lattice3(esk11_0,k1_xboole_0),k15_lattice3(esk11_0,X1))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.20/0.37  cnf(c_0_55, plain, (X1=k15_lattice3(X2,a_2_3_lattice3(X2,X1))|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.20/0.37  cnf(c_0_56, plain, (k2_lattices(X1,X2,X3)=X3|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|X3!=k5_lattices(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~v13_lattices(X1)|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.20/0.37  cnf(c_0_57, plain, (v2_struct_0(X1)|m1_subset_1(k5_lattices(X1),u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.20/0.37  cnf(c_0_58, plain, (k2_lattices(X1,X2,X3)=X2|v2_struct_0(X1)|~r3_lattices(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v9_lattices(X1)|~v8_lattices(X1)|~v6_lattices(X1)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.20/0.37  cnf(c_0_59, negated_conjecture, (r3_lattices(esk11_0,k15_lattice3(esk11_0,k1_xboole_0),X1)|~m1_subset_1(X1,u1_struct_0(esk11_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_33]), c_0_34]), c_0_35])]), c_0_36])).
% 0.20/0.37  cnf(c_0_60, negated_conjecture, (v2_struct_0(esk11_0)|~v10_lattices(esk11_0)|~v13_lattices(esk11_0)|~l3_lattices(esk11_0)|k5_lattices(esk11_0)!=k15_lattice3(esk11_0,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.37  cnf(c_0_61, plain, (k2_lattices(X1,X2,k5_lattices(X1))=k5_lattices(X1)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v13_lattices(X1)|~l1_lattices(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_56]), c_0_57])).
% 0.20/0.37  cnf(c_0_62, negated_conjecture, (k2_lattices(esk11_0,k15_lattice3(esk11_0,k1_xboole_0),X1)=k15_lattice3(esk11_0,k1_xboole_0)|~m1_subset_1(k15_lattice3(esk11_0,k1_xboole_0),u1_struct_0(esk11_0))|~m1_subset_1(X1,u1_struct_0(esk11_0))|~v9_lattices(esk11_0)|~v8_lattices(esk11_0)|~v6_lattices(esk11_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_35])]), c_0_36])).
% 0.20/0.37  cnf(c_0_63, negated_conjecture, (k15_lattice3(esk11_0,k1_xboole_0)!=k5_lattices(esk11_0)|~v13_lattices(esk11_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_35]), c_0_34])]), c_0_36])).
% 0.20/0.37  fof(c_0_64, plain, ![X40, X41]:(v2_struct_0(X40)|~l3_lattices(X40)|m1_subset_1(k15_lattice3(X40,X41),u1_struct_0(X40))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k15_lattice3])])])).
% 0.20/0.37  fof(c_0_65, plain, ![X30, X32, X33]:(((m1_subset_1(esk4_1(X30),u1_struct_0(X30))|~v13_lattices(X30)|(v2_struct_0(X30)|~l1_lattices(X30)))&((k2_lattices(X30,esk4_1(X30),X32)=esk4_1(X30)|~m1_subset_1(X32,u1_struct_0(X30))|~v13_lattices(X30)|(v2_struct_0(X30)|~l1_lattices(X30)))&(k2_lattices(X30,X32,esk4_1(X30))=esk4_1(X30)|~m1_subset_1(X32,u1_struct_0(X30))|~v13_lattices(X30)|(v2_struct_0(X30)|~l1_lattices(X30)))))&((m1_subset_1(esk5_2(X30,X33),u1_struct_0(X30))|~m1_subset_1(X33,u1_struct_0(X30))|v13_lattices(X30)|(v2_struct_0(X30)|~l1_lattices(X30)))&(k2_lattices(X30,X33,esk5_2(X30,X33))!=X33|k2_lattices(X30,esk5_2(X30,X33),X33)!=X33|~m1_subset_1(X33,u1_struct_0(X30))|v13_lattices(X30)|(v2_struct_0(X30)|~l1_lattices(X30))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d13_lattices])])])])])])).
% 0.20/0.37  fof(c_0_66, plain, ![X35, X36, X37]:((~v6_lattices(X35)|(~m1_subset_1(X36,u1_struct_0(X35))|(~m1_subset_1(X37,u1_struct_0(X35))|k2_lattices(X35,X36,X37)=k2_lattices(X35,X37,X36)))|(v2_struct_0(X35)|~l1_lattices(X35)))&((m1_subset_1(esk6_1(X35),u1_struct_0(X35))|v6_lattices(X35)|(v2_struct_0(X35)|~l1_lattices(X35)))&((m1_subset_1(esk7_1(X35),u1_struct_0(X35))|v6_lattices(X35)|(v2_struct_0(X35)|~l1_lattices(X35)))&(k2_lattices(X35,esk6_1(X35),esk7_1(X35))!=k2_lattices(X35,esk7_1(X35),esk6_1(X35))|v6_lattices(X35)|(v2_struct_0(X35)|~l1_lattices(X35)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d6_lattices])])])])])])).
% 0.20/0.37  cnf(c_0_67, negated_conjecture, (~m1_subset_1(k15_lattice3(esk11_0,k1_xboole_0),u1_struct_0(esk11_0))|~m1_subset_1(k5_lattices(esk11_0),u1_struct_0(esk11_0))|~v13_lattices(esk11_0)|~l1_lattices(esk11_0)|~v9_lattices(esk11_0)|~v8_lattices(esk11_0)|~v6_lattices(esk11_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_36]), c_0_63])).
% 0.20/0.37  cnf(c_0_68, plain, (v2_struct_0(X1)|m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.20/0.37  cnf(c_0_69, plain, (v13_lattices(X1)|v2_struct_0(X1)|k2_lattices(X1,X2,esk5_2(X1,X2))!=X2|k2_lattices(X1,esk5_2(X1,X2),X2)!=X2|~m1_subset_1(X2,u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.20/0.37  cnf(c_0_70, plain, (k2_lattices(X1,X2,X3)=k2_lattices(X1,X3,X2)|v2_struct_0(X1)|~v6_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.20/0.37  cnf(c_0_71, plain, (m1_subset_1(esk5_2(X1,X2),u1_struct_0(X1))|v13_lattices(X1)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.20/0.37  cnf(c_0_72, negated_conjecture, (~m1_subset_1(k5_lattices(esk11_0),u1_struct_0(esk11_0))|~v13_lattices(esk11_0)|~l1_lattices(esk11_0)|~v9_lattices(esk11_0)|~v8_lattices(esk11_0)|~v6_lattices(esk11_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_35])]), c_0_36])).
% 0.20/0.37  cnf(c_0_73, plain, (v13_lattices(X1)|v2_struct_0(X1)|k2_lattices(X1,X2,esk5_2(X1,X2))!=X2|~m1_subset_1(X2,u1_struct_0(X1))|~l1_lattices(X1)|~v6_lattices(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_71])).
% 0.20/0.37  cnf(c_0_74, negated_conjecture, (~v13_lattices(esk11_0)|~l1_lattices(esk11_0)|~v9_lattices(esk11_0)|~v8_lattices(esk11_0)|~v6_lattices(esk11_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_57]), c_0_36])).
% 0.20/0.37  cnf(c_0_75, negated_conjecture, (~m1_subset_1(esk5_2(esk11_0,k15_lattice3(esk11_0,k1_xboole_0)),u1_struct_0(esk11_0))|~m1_subset_1(k15_lattice3(esk11_0,k1_xboole_0),u1_struct_0(esk11_0))|~l1_lattices(esk11_0)|~v9_lattices(esk11_0)|~v8_lattices(esk11_0)|~v6_lattices(esk11_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_62]), c_0_36]), c_0_74])).
% 0.20/0.37  cnf(c_0_76, negated_conjecture, (~m1_subset_1(k15_lattice3(esk11_0,k1_xboole_0),u1_struct_0(esk11_0))|~l1_lattices(esk11_0)|~v9_lattices(esk11_0)|~v8_lattices(esk11_0)|~v6_lattices(esk11_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_71]), c_0_36]), c_0_74])).
% 0.20/0.37  fof(c_0_77, plain, ![X17]:(((((((~v2_struct_0(X17)|(v2_struct_0(X17)|~v10_lattices(X17))|~l3_lattices(X17))&(v4_lattices(X17)|(v2_struct_0(X17)|~v10_lattices(X17))|~l3_lattices(X17)))&(v5_lattices(X17)|(v2_struct_0(X17)|~v10_lattices(X17))|~l3_lattices(X17)))&(v6_lattices(X17)|(v2_struct_0(X17)|~v10_lattices(X17))|~l3_lattices(X17)))&(v7_lattices(X17)|(v2_struct_0(X17)|~v10_lattices(X17))|~l3_lattices(X17)))&(v8_lattices(X17)|(v2_struct_0(X17)|~v10_lattices(X17))|~l3_lattices(X17)))&(v9_lattices(X17)|(v2_struct_0(X17)|~v10_lattices(X17))|~l3_lattices(X17))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).
% 0.20/0.37  cnf(c_0_78, negated_conjecture, (~l1_lattices(esk11_0)|~v9_lattices(esk11_0)|~v8_lattices(esk11_0)|~v6_lattices(esk11_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_68]), c_0_35])]), c_0_36])).
% 0.20/0.37  cnf(c_0_79, plain, (v9_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_77])).
% 0.20/0.37  cnf(c_0_80, negated_conjecture, (~l1_lattices(esk11_0)|~v8_lattices(esk11_0)|~v6_lattices(esk11_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_34]), c_0_35])]), c_0_36])).
% 0.20/0.37  cnf(c_0_81, plain, (v8_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_77])).
% 0.20/0.37  cnf(c_0_82, negated_conjecture, (~l1_lattices(esk11_0)|~v6_lattices(esk11_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_34]), c_0_35])]), c_0_36])).
% 0.20/0.37  cnf(c_0_83, plain, (v6_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_77])).
% 0.20/0.37  fof(c_0_84, plain, ![X23]:((l1_lattices(X23)|~l3_lattices(X23))&(l2_lattices(X23)|~l3_lattices(X23))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).
% 0.20/0.37  cnf(c_0_85, negated_conjecture, (~l1_lattices(esk11_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_34]), c_0_35])]), c_0_36])).
% 0.20/0.37  cnf(c_0_86, plain, (l1_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_84])).
% 0.20/0.37  cnf(c_0_87, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_35])]), ['proof']).
% 0.20/0.37  # SZS output end CNFRefutation
% 0.20/0.37  # Proof object total steps             : 88
% 0.20/0.37  # Proof object clause steps            : 52
% 0.20/0.37  # Proof object formula steps           : 36
% 0.20/0.37  # Proof object conjectures             : 25
% 0.20/0.37  # Proof object clause conjectures      : 22
% 0.20/0.37  # Proof object formula conjectures     : 3
% 0.20/0.37  # Proof object initial clauses used    : 26
% 0.20/0.37  # Proof object initial formulas used   : 18
% 0.20/0.37  # Proof object generating inferences   : 24
% 0.20/0.37  # Proof object simplifying inferences  : 51
% 0.20/0.37  # Training examples: 0 positive, 0 negative
% 0.20/0.37  # Parsed axioms                        : 18
% 0.20/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.37  # Initial clauses                      : 53
% 0.20/0.37  # Removed in clause preprocessing      : 1
% 0.20/0.37  # Initial clauses in saturation        : 52
% 0.20/0.37  # Processed clauses                    : 224
% 0.20/0.37  # ...of these trivial                  : 3
% 0.20/0.37  # ...subsumed                          : 91
% 0.20/0.37  # ...remaining for further processing  : 130
% 0.20/0.37  # Other redundant clauses eliminated   : 4
% 0.20/0.37  # Clauses deleted for lack of memory   : 0
% 0.20/0.37  # Backward-subsumed                    : 11
% 0.20/0.37  # Backward-rewritten                   : 2
% 0.20/0.37  # Generated clauses                    : 320
% 0.20/0.37  # ...of the previous two non-trivial   : 291
% 0.20/0.37  # Contextual simplify-reflections      : 9
% 0.20/0.37  # Paramodulations                      : 316
% 0.20/0.37  # Factorizations                       : 0
% 0.20/0.37  # Equation resolutions                 : 4
% 0.20/0.37  # Propositional unsat checks           : 0
% 0.20/0.37  #    Propositional check models        : 0
% 0.20/0.37  #    Propositional check unsatisfiable : 0
% 0.20/0.37  #    Propositional clauses             : 0
% 0.20/0.37  #    Propositional clauses after purity: 0
% 0.20/0.37  #    Propositional unsat core size     : 0
% 0.20/0.37  #    Propositional preprocessing time  : 0.000
% 0.20/0.37  #    Propositional encoding time       : 0.000
% 0.20/0.37  #    Propositional solver time         : 0.000
% 0.20/0.37  #    Success case prop preproc time    : 0.000
% 0.20/0.37  #    Success case prop encoding time   : 0.000
% 0.20/0.37  #    Success case prop solver time     : 0.000
% 0.20/0.37  # Current number of processed clauses  : 114
% 0.20/0.37  #    Positive orientable unit clauses  : 7
% 0.20/0.37  #    Positive unorientable unit clauses: 0
% 0.20/0.37  #    Negative unit clauses             : 2
% 0.20/0.37  #    Non-unit-clauses                  : 105
% 0.20/0.37  # Current number of unprocessed clauses: 111
% 0.20/0.37  # ...number of literals in the above   : 724
% 0.20/0.37  # Current number of archived formulas  : 0
% 0.20/0.37  # Current number of archived clauses   : 13
% 0.20/0.37  # Clause-clause subsumption calls (NU) : 4279
% 0.20/0.37  # Rec. Clause-clause subsumption calls : 774
% 0.20/0.37  # Non-unit clause-clause subsumptions  : 111
% 0.20/0.37  # Unit Clause-clause subsumption calls : 69
% 0.20/0.37  # Rewrite failures with RHS unbound    : 0
% 0.20/0.37  # BW rewrite match attempts            : 5
% 0.20/0.37  # BW rewrite match successes           : 2
% 0.20/0.37  # Condensation attempts                : 0
% 0.20/0.37  # Condensation successes               : 0
% 0.20/0.37  # Termbank termtop insertions          : 13631
% 0.20/0.37  
% 0.20/0.37  # -------------------------------------------------
% 0.20/0.37  # User time                : 0.030 s
% 0.20/0.37  # System time              : 0.001 s
% 0.20/0.37  # Total time               : 0.031 s
% 0.20/0.37  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
