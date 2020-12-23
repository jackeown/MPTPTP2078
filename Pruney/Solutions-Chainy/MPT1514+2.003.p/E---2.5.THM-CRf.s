%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:05 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   72 (1734 expanded)
%              Number of clauses        :   51 ( 556 expanded)
%              Number of leaves         :   10 ( 426 expanded)
%              Depth                    :   22
%              Number of atoms          :  435 (13903 expanded)
%              Number of equality atoms :   18 ( 250 expanded)
%              Maximal formula depth    :   22 (   6 average)
%              Maximal clause size      :   40 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t48_lattice3,conjecture,(
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

fof(dt_k15_lattice3,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k15_lattice3)).

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

fof(t38_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v4_lattice3(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( r2_hidden(X2,X3)
             => ( r3_lattices(X1,X2,k15_lattice3(X1,X3))
                & r3_lattices(X1,k16_lattice3(X1,X3),X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_lattice3)).

fof(t37_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v4_lattice3(X1)
        & l3_lattices(X1) )
     => ! [X2] : k15_lattice3(X1,X2) = k16_lattice3(X1,a_2_2_lattice3(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_lattice3)).

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

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
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
    inference(assume_negation,[status(cth)],[t48_lattice3])).

fof(c_0_11,plain,(
    ! [X37,X38] :
      ( ( k15_lattice3(X37,X38) = k15_lattice3(X37,a_2_5_lattice3(X37,X38))
        | v2_struct_0(X37)
        | ~ v10_lattices(X37)
        | ~ v4_lattice3(X37)
        | ~ l3_lattices(X37) )
      & ( k16_lattice3(X37,X38) = k16_lattice3(X37,a_2_6_lattice3(X37,X38))
        | v2_struct_0(X37)
        | ~ v10_lattices(X37)
        | ~ v4_lattice3(X37)
        | ~ l3_lattices(X37) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t47_lattice3])])])])])).

fof(c_0_12,negated_conjecture,(
    ! [X42] :
      ( ~ v2_struct_0(esk5_0)
      & v10_lattices(esk5_0)
      & v4_lattice3(esk5_0)
      & l3_lattices(esk5_0)
      & ( m1_subset_1(esk8_1(X42),u1_struct_0(esk5_0))
        | ~ r2_hidden(X42,esk6_0)
        | ~ m1_subset_1(X42,u1_struct_0(esk5_0)) )
      & ( r3_lattices(esk5_0,X42,esk8_1(X42))
        | ~ r2_hidden(X42,esk6_0)
        | ~ m1_subset_1(X42,u1_struct_0(esk5_0)) )
      & ( r2_hidden(esk8_1(X42),esk7_0)
        | ~ r2_hidden(X42,esk6_0)
        | ~ m1_subset_1(X42,u1_struct_0(esk5_0)) )
      & ~ r3_lattices(esk5_0,k15_lattice3(esk5_0,esk6_0),k15_lattice3(esk5_0,esk7_0)) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])])])).

fof(c_0_13,plain,(
    ! [X16,X17] :
      ( v2_struct_0(X16)
      | ~ l3_lattices(X16)
      | m1_subset_1(k15_lattice3(X16,X17),u1_struct_0(X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k15_lattice3])])])).

cnf(c_0_14,plain,
    ( k15_lattice3(X1,X2) = k15_lattice3(X1,a_2_5_lattice3(X1,X2))
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( v4_lattice3(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( v10_lattices(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( l3_lattices(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_19,plain,(
    ! [X18,X19,X20,X22,X23] :
      ( ( m1_subset_1(esk2_3(X18,X19,X20),u1_struct_0(X19))
        | ~ r2_hidden(X18,a_2_2_lattice3(X19,X20))
        | v2_struct_0(X19)
        | ~ v10_lattices(X19)
        | ~ v4_lattice3(X19)
        | ~ l3_lattices(X19) )
      & ( X18 = esk2_3(X18,X19,X20)
        | ~ r2_hidden(X18,a_2_2_lattice3(X19,X20))
        | v2_struct_0(X19)
        | ~ v10_lattices(X19)
        | ~ v4_lattice3(X19)
        | ~ l3_lattices(X19) )
      & ( r4_lattice3(X19,esk2_3(X18,X19,X20),X20)
        | ~ r2_hidden(X18,a_2_2_lattice3(X19,X20))
        | v2_struct_0(X19)
        | ~ v10_lattices(X19)
        | ~ v4_lattice3(X19)
        | ~ l3_lattices(X19) )
      & ( ~ m1_subset_1(X23,u1_struct_0(X19))
        | X18 != X23
        | ~ r4_lattice3(X19,X23,X22)
        | r2_hidden(X18,a_2_2_lattice3(X19,X22))
        | v2_struct_0(X19)
        | ~ v10_lattices(X19)
        | ~ v4_lattice3(X19)
        | ~ l3_lattices(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_2_lattice3])])])])])])])).

fof(c_0_20,plain,(
    ! [X10,X11,X12,X13,X14] :
      ( ( ~ r4_lattice3(X10,X11,X12)
        | ~ m1_subset_1(X13,u1_struct_0(X10))
        | ~ r2_hidden(X13,X12)
        | r1_lattices(X10,X13,X11)
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | v2_struct_0(X10)
        | ~ l3_lattices(X10) )
      & ( m1_subset_1(esk1_3(X10,X11,X14),u1_struct_0(X10))
        | r4_lattice3(X10,X11,X14)
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | v2_struct_0(X10)
        | ~ l3_lattices(X10) )
      & ( r2_hidden(esk1_3(X10,X11,X14),X14)
        | r4_lattice3(X10,X11,X14)
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | v2_struct_0(X10)
        | ~ l3_lattices(X10) )
      & ( ~ r1_lattices(X10,esk1_3(X10,X11,X14),X11)
        | r4_lattice3(X10,X11,X14)
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | v2_struct_0(X10)
        | ~ l3_lattices(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_lattice3])])])])])])])).

cnf(c_0_21,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,negated_conjecture,
    ( k15_lattice3(esk5_0,a_2_5_lattice3(esk5_0,X1)) = k15_lattice3(esk5_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16]),c_0_17])]),c_0_18])).

fof(c_0_23,plain,(
    ! [X34,X35,X36] :
      ( ( r3_lattices(X34,X35,k15_lattice3(X34,X36))
        | ~ r2_hidden(X35,X36)
        | ~ m1_subset_1(X35,u1_struct_0(X34))
        | v2_struct_0(X34)
        | ~ v10_lattices(X34)
        | ~ v4_lattice3(X34)
        | ~ l3_lattices(X34) )
      & ( r3_lattices(X34,k16_lattice3(X34,X36),X35)
        | ~ r2_hidden(X35,X36)
        | ~ m1_subset_1(X35,u1_struct_0(X34))
        | v2_struct_0(X34)
        | ~ v10_lattices(X34)
        | ~ v4_lattice3(X34)
        | ~ l3_lattices(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t38_lattice3])])])])])).

cnf(c_0_24,plain,
    ( r2_hidden(X3,a_2_2_lattice3(X2,X4))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | X3 != X1
    | ~ r4_lattice3(X2,X1,X4)
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))
    | r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(k15_lattice3(esk5_0,X1),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_17])]),c_0_18])).

fof(c_0_27,plain,(
    ! [X32,X33] :
      ( v2_struct_0(X32)
      | ~ v10_lattices(X32)
      | ~ v4_lattice3(X32)
      | ~ l3_lattices(X32)
      | k15_lattice3(X32,X33) = k16_lattice3(X32,a_2_2_lattice3(X32,X33)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t37_lattice3])])])])).

cnf(c_0_28,plain,
    ( r3_lattices(X1,k16_lattice3(X1,X2),X3)
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,a_2_2_lattice3(X2,X3))
    | v2_struct_0(X2)
    | ~ v4_lattice3(X2)
    | ~ r4_lattice3(X2,X1,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(er,[status(thm)],[c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( r4_lattice3(esk5_0,k15_lattice3(esk5_0,X1),X2)
    | m1_subset_1(esk1_3(esk5_0,k15_lattice3(esk5_0,X1),X2),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_17])]),c_0_18])).

cnf(c_0_31,plain,
    ( v2_struct_0(X1)
    | k15_lattice3(X1,X2) = k16_lattice3(X1,a_2_2_lattice3(X1,X2))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( r3_lattices(esk5_0,k16_lattice3(esk5_0,X1),k15_lattice3(esk5_0,X2))
    | ~ r2_hidden(k15_lattice3(esk5_0,X2),X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_26]),c_0_15]),c_0_16]),c_0_17])]),c_0_18])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(k15_lattice3(esk5_0,X1),a_2_2_lattice3(esk5_0,X2))
    | m1_subset_1(esk1_3(esk5_0,k15_lattice3(esk5_0,X1),X2),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_15]),c_0_26]),c_0_16]),c_0_17])]),c_0_18])).

cnf(c_0_34,negated_conjecture,
    ( k16_lattice3(esk5_0,a_2_2_lattice3(esk5_0,X1)) = k15_lattice3(esk5_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_15]),c_0_16]),c_0_17])]),c_0_18])).

cnf(c_0_35,negated_conjecture,
    ( ~ r3_lattices(esk5_0,k15_lattice3(esk5_0,esk6_0),k15_lattice3(esk5_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_36,negated_conjecture,
    ( r3_lattices(esk5_0,k15_lattice3(esk5_0,X1),k15_lattice3(esk5_0,X2))
    | m1_subset_1(esk1_3(esk5_0,k15_lattice3(esk5_0,X2),X1),u1_struct_0(esk5_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])).

cnf(c_0_37,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X3)
    | r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk8_1(X1),u1_struct_0(esk5_0))
    | ~ r2_hidden(X1,esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(esk1_3(esk5_0,k15_lattice3(esk5_0,esk7_0),esk6_0),u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk1_3(esk5_0,k15_lattice3(esk5_0,X1),X2),X2)
    | r4_lattice3(esk5_0,k15_lattice3(esk5_0,X1),X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_26]),c_0_17])]),c_0_18])).

fof(c_0_41,plain,(
    ! [X24,X25,X26,X29,X30,X31] :
      ( ( m1_subset_1(esk3_3(X24,X25,X26),u1_struct_0(X25))
        | ~ r2_hidden(X24,a_2_5_lattice3(X25,X26))
        | v2_struct_0(X25)
        | ~ v10_lattices(X25)
        | ~ v4_lattice3(X25)
        | ~ l3_lattices(X25) )
      & ( X24 = esk3_3(X24,X25,X26)
        | ~ r2_hidden(X24,a_2_5_lattice3(X25,X26))
        | v2_struct_0(X25)
        | ~ v10_lattices(X25)
        | ~ v4_lattice3(X25)
        | ~ l3_lattices(X25) )
      & ( m1_subset_1(esk4_3(X24,X25,X26),u1_struct_0(X25))
        | ~ r2_hidden(X24,a_2_5_lattice3(X25,X26))
        | v2_struct_0(X25)
        | ~ v10_lattices(X25)
        | ~ v4_lattice3(X25)
        | ~ l3_lattices(X25) )
      & ( r3_lattices(X25,esk3_3(X24,X25,X26),esk4_3(X24,X25,X26))
        | ~ r2_hidden(X24,a_2_5_lattice3(X25,X26))
        | v2_struct_0(X25)
        | ~ v10_lattices(X25)
        | ~ v4_lattice3(X25)
        | ~ l3_lattices(X25) )
      & ( r2_hidden(esk4_3(X24,X25,X26),X26)
        | ~ r2_hidden(X24,a_2_5_lattice3(X25,X26))
        | v2_struct_0(X25)
        | ~ v10_lattices(X25)
        | ~ v4_lattice3(X25)
        | ~ l3_lattices(X25) )
      & ( ~ m1_subset_1(X30,u1_struct_0(X25))
        | X24 != X30
        | ~ m1_subset_1(X31,u1_struct_0(X25))
        | ~ r3_lattices(X25,X30,X31)
        | ~ r2_hidden(X31,X29)
        | r2_hidden(X24,a_2_5_lattice3(X25,X29))
        | v2_struct_0(X25)
        | ~ v10_lattices(X25)
        | ~ v4_lattice3(X25)
        | ~ l3_lattices(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_5_lattice3])])])])])])])).

cnf(c_0_42,negated_conjecture,
    ( r3_lattices(esk5_0,X1,esk8_1(X1))
    | ~ r2_hidden(X1,esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(esk8_1(esk1_3(esk5_0,k15_lattice3(esk5_0,esk7_0),esk6_0)),u1_struct_0(esk5_0))
    | ~ r2_hidden(esk1_3(esk5_0,k15_lattice3(esk5_0,esk7_0),esk6_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk1_3(esk5_0,k15_lattice3(esk5_0,X1),X2),X2)
    | r2_hidden(k15_lattice3(esk5_0,X1),a_2_2_lattice3(esk5_0,X2)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_40]),c_0_15]),c_0_26]),c_0_16]),c_0_17])]),c_0_18])).

cnf(c_0_45,plain,
    ( r2_hidden(X3,a_2_5_lattice3(X2,X5))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | X3 != X1
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r3_lattices(X2,X1,X4)
    | ~ r2_hidden(X4,X5)
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_46,negated_conjecture,
    ( r3_lattices(esk5_0,esk1_3(esk5_0,k15_lattice3(esk5_0,esk7_0),esk6_0),esk8_1(esk1_3(esk5_0,k15_lattice3(esk5_0,esk7_0),esk6_0)))
    | ~ r2_hidden(esk1_3(esk5_0,k15_lattice3(esk5_0,esk7_0),esk6_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_39])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(k15_lattice3(esk5_0,esk7_0),a_2_2_lattice3(esk5_0,esk6_0))
    | m1_subset_1(esk8_1(esk1_3(esk5_0,k15_lattice3(esk5_0,esk7_0),esk6_0)),u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,a_2_5_lattice3(X2,X3))
    | v2_struct_0(X2)
    | ~ v4_lattice3(X2)
    | ~ r2_hidden(X4,X3)
    | ~ r3_lattices(X2,X1,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(er,[status(thm)],[c_0_45])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(k15_lattice3(esk5_0,esk7_0),a_2_2_lattice3(esk5_0,esk6_0))
    | r3_lattices(esk5_0,esk1_3(esk5_0,k15_lattice3(esk5_0,esk7_0),esk6_0),esk8_1(esk1_3(esk5_0,k15_lattice3(esk5_0,esk7_0),esk6_0))) ),
    inference(spm,[status(thm)],[c_0_46,c_0_44])).

cnf(c_0_50,negated_conjecture,
    ( m1_subset_1(esk8_1(esk1_3(esk5_0,k15_lattice3(esk5_0,esk7_0),esk6_0)),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_47]),c_0_34]),c_0_35])).

cnf(c_0_51,plain,
    ( r3_lattices(X1,X2,k15_lattice3(X1,X3))
    | v2_struct_0(X1)
    | ~ r2_hidden(X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(esk1_3(esk5_0,k15_lattice3(esk5_0,esk7_0),esk6_0),a_2_5_lattice3(esk5_0,X1))
    | r2_hidden(k15_lattice3(esk5_0,esk7_0),a_2_2_lattice3(esk5_0,esk6_0))
    | ~ r2_hidden(esk8_1(esk1_3(esk5_0,k15_lattice3(esk5_0,esk7_0),esk6_0)),X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_15]),c_0_50]),c_0_39]),c_0_16]),c_0_17])]),c_0_18])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(esk8_1(X1),esk7_0)
    | ~ r2_hidden(X1,esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_54,plain,(
    ! [X7,X8,X9] :
      ( ( ~ r3_lattices(X7,X8,X9)
        | r1_lattices(X7,X8,X9)
        | v2_struct_0(X7)
        | ~ v6_lattices(X7)
        | ~ v8_lattices(X7)
        | ~ v9_lattices(X7)
        | ~ l3_lattices(X7)
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | ~ m1_subset_1(X9,u1_struct_0(X7)) )
      & ( ~ r1_lattices(X7,X8,X9)
        | r3_lattices(X7,X8,X9)
        | v2_struct_0(X7)
        | ~ v6_lattices(X7)
        | ~ v8_lattices(X7)
        | ~ v9_lattices(X7)
        | ~ l3_lattices(X7)
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | ~ m1_subset_1(X9,u1_struct_0(X7)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).

cnf(c_0_55,negated_conjecture,
    ( r3_lattices(esk5_0,esk1_3(esk5_0,k15_lattice3(esk5_0,esk7_0),esk6_0),k15_lattice3(esk5_0,X1))
    | ~ r2_hidden(esk1_3(esk5_0,k15_lattice3(esk5_0,esk7_0),esk6_0),X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_39]),c_0_15]),c_0_16]),c_0_17])]),c_0_18])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk1_3(esk5_0,k15_lattice3(esk5_0,esk7_0),esk6_0),a_2_5_lattice3(esk5_0,esk7_0))
    | r2_hidden(k15_lattice3(esk5_0,esk7_0),a_2_2_lattice3(esk5_0,esk6_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_39])]),c_0_44])).

cnf(c_0_57,plain,
    ( r1_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(k15_lattice3(esk5_0,esk7_0),a_2_2_lattice3(esk5_0,esk6_0))
    | r3_lattices(esk5_0,esk1_3(esk5_0,k15_lattice3(esk5_0,esk7_0),esk6_0),k15_lattice3(esk5_0,esk7_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_22])).

fof(c_0_59,plain,(
    ! [X6] :
      ( ( ~ v2_struct_0(X6)
        | v2_struct_0(X6)
        | ~ v10_lattices(X6)
        | ~ l3_lattices(X6) )
      & ( v4_lattices(X6)
        | v2_struct_0(X6)
        | ~ v10_lattices(X6)
        | ~ l3_lattices(X6) )
      & ( v5_lattices(X6)
        | v2_struct_0(X6)
        | ~ v10_lattices(X6)
        | ~ l3_lattices(X6) )
      & ( v6_lattices(X6)
        | v2_struct_0(X6)
        | ~ v10_lattices(X6)
        | ~ l3_lattices(X6) )
      & ( v7_lattices(X6)
        | v2_struct_0(X6)
        | ~ v10_lattices(X6)
        | ~ l3_lattices(X6) )
      & ( v8_lattices(X6)
        | v2_struct_0(X6)
        | ~ v10_lattices(X6)
        | ~ l3_lattices(X6) )
      & ( v9_lattices(X6)
        | v2_struct_0(X6)
        | ~ v10_lattices(X6)
        | ~ l3_lattices(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(k15_lattice3(esk5_0,esk7_0),a_2_2_lattice3(esk5_0,esk6_0))
    | r1_lattices(esk5_0,esk1_3(esk5_0,k15_lattice3(esk5_0,esk7_0),esk6_0),k15_lattice3(esk5_0,esk7_0))
    | ~ v9_lattices(esk5_0)
    | ~ v8_lattices(esk5_0)
    | ~ v6_lattices(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_26]),c_0_39]),c_0_17])]),c_0_18])).

cnf(c_0_61,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(k15_lattice3(esk5_0,esk7_0),a_2_2_lattice3(esk5_0,esk6_0))
    | r1_lattices(esk5_0,esk1_3(esk5_0,k15_lattice3(esk5_0,esk7_0),esk6_0),k15_lattice3(esk5_0,esk7_0))
    | ~ v9_lattices(esk5_0)
    | ~ v8_lattices(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_16]),c_0_17])]),c_0_18])).

cnf(c_0_63,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(k15_lattice3(esk5_0,esk7_0),a_2_2_lattice3(esk5_0,esk6_0))
    | r1_lattices(esk5_0,esk1_3(esk5_0,k15_lattice3(esk5_0,esk7_0),esk6_0),k15_lattice3(esk5_0,esk7_0))
    | ~ v9_lattices(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_16]),c_0_17])]),c_0_18])).

cnf(c_0_65,plain,
    ( v9_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_66,plain,
    ( r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,esk1_3(X1,X2,X3),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(k15_lattice3(esk5_0,esk7_0),a_2_2_lattice3(esk5_0,esk6_0))
    | r1_lattices(esk5_0,esk1_3(esk5_0,k15_lattice3(esk5_0,esk7_0),esk6_0),k15_lattice3(esk5_0,esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_16]),c_0_17])]),c_0_18])).

cnf(c_0_68,negated_conjecture,
    ( r2_hidden(k15_lattice3(esk5_0,esk7_0),a_2_2_lattice3(esk5_0,esk6_0))
    | r4_lattice3(esk5_0,k15_lattice3(esk5_0,esk7_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_26]),c_0_17])]),c_0_18])).

cnf(c_0_69,plain,
    ( r3_lattices(X1,k16_lattice3(X1,X2),k15_lattice3(X1,X3))
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ r2_hidden(k15_lattice3(X1,X3),X2)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_21])).

cnf(c_0_70,negated_conjecture,
    ( r2_hidden(k15_lattice3(esk5_0,esk7_0),a_2_2_lattice3(esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_68]),c_0_15]),c_0_26]),c_0_16]),c_0_17])]),c_0_18])).

cnf(c_0_71,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_34]),c_0_15]),c_0_16]),c_0_17])]),c_0_35]),c_0_18]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:10:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.42  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S088I
% 0.20/0.42  # and selection function SelectCQArNTEqFirstUnlessPDom.
% 0.20/0.42  #
% 0.20/0.42  # Preprocessing time       : 0.046 s
% 0.20/0.42  # Presaturation interreduction done
% 0.20/0.42  
% 0.20/0.42  # Proof found!
% 0.20/0.42  # SZS status Theorem
% 0.20/0.42  # SZS output start CNFRefutation
% 0.20/0.42  fof(t48_lattice3, conjecture, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2, X3]:(![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>~((r2_hidden(X4,X2)&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>~((r3_lattices(X1,X4,X5)&r2_hidden(X5,X3)))))))=>r3_lattices(X1,k15_lattice3(X1,X2),k15_lattice3(X1,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_lattice3)).
% 0.20/0.42  fof(t47_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(k15_lattice3(X1,X2)=k15_lattice3(X1,a_2_5_lattice3(X1,X2))&k16_lattice3(X1,X2)=k16_lattice3(X1,a_2_6_lattice3(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_lattice3)).
% 0.20/0.42  fof(dt_k15_lattice3, axiom, ![X1, X2]:((~(v2_struct_0(X1))&l3_lattices(X1))=>m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k15_lattice3)).
% 0.20/0.42  fof(fraenkel_a_2_2_lattice3, axiom, ![X1, X2, X3]:((((~(v2_struct_0(X2))&v10_lattices(X2))&v4_lattice3(X2))&l3_lattices(X2))=>(r2_hidden(X1,a_2_2_lattice3(X2,X3))<=>?[X4]:((m1_subset_1(X4,u1_struct_0(X2))&X1=X4)&r4_lattice3(X2,X4,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_2_lattice3)).
% 0.20/0.42  fof(d17_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(r4_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X3)=>r1_lattices(X1,X4,X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d17_lattice3)).
% 0.20/0.42  fof(t38_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(r2_hidden(X2,X3)=>(r3_lattices(X1,X2,k15_lattice3(X1,X3))&r3_lattices(X1,k16_lattice3(X1,X3),X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_lattice3)).
% 0.20/0.42  fof(t37_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:k15_lattice3(X1,X2)=k16_lattice3(X1,a_2_2_lattice3(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_lattice3)).
% 0.20/0.42  fof(fraenkel_a_2_5_lattice3, axiom, ![X1, X2, X3]:((((~(v2_struct_0(X2))&v10_lattices(X2))&v4_lattice3(X2))&l3_lattices(X2))=>(r2_hidden(X1,a_2_5_lattice3(X2,X3))<=>?[X4]:((m1_subset_1(X4,u1_struct_0(X2))&X1=X4)&?[X5]:((m1_subset_1(X5,u1_struct_0(X2))&r3_lattices(X2,X4,X5))&r2_hidden(X5,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_5_lattice3)).
% 0.20/0.42  fof(redefinition_r3_lattices, axiom, ![X1, X2, X3]:(((((((~(v2_struct_0(X1))&v6_lattices(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>(r3_lattices(X1,X2,X3)<=>r1_lattices(X1,X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 0.20/0.42  fof(cc1_lattices, axiom, ![X1]:(l3_lattices(X1)=>((~(v2_struct_0(X1))&v10_lattices(X1))=>((((((~(v2_struct_0(X1))&v4_lattices(X1))&v5_lattices(X1))&v6_lattices(X1))&v7_lattices(X1))&v8_lattices(X1))&v9_lattices(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattices)).
% 0.20/0.42  fof(c_0_10, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2, X3]:(![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>~((r2_hidden(X4,X2)&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>~((r3_lattices(X1,X4,X5)&r2_hidden(X5,X3)))))))=>r3_lattices(X1,k15_lattice3(X1,X2),k15_lattice3(X1,X3))))), inference(assume_negation,[status(cth)],[t48_lattice3])).
% 0.20/0.42  fof(c_0_11, plain, ![X37, X38]:((k15_lattice3(X37,X38)=k15_lattice3(X37,a_2_5_lattice3(X37,X38))|(v2_struct_0(X37)|~v10_lattices(X37)|~v4_lattice3(X37)|~l3_lattices(X37)))&(k16_lattice3(X37,X38)=k16_lattice3(X37,a_2_6_lattice3(X37,X38))|(v2_struct_0(X37)|~v10_lattices(X37)|~v4_lattice3(X37)|~l3_lattices(X37)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t47_lattice3])])])])])).
% 0.20/0.42  fof(c_0_12, negated_conjecture, ![X42]:((((~v2_struct_0(esk5_0)&v10_lattices(esk5_0))&v4_lattice3(esk5_0))&l3_lattices(esk5_0))&(((m1_subset_1(esk8_1(X42),u1_struct_0(esk5_0))|~r2_hidden(X42,esk6_0)|~m1_subset_1(X42,u1_struct_0(esk5_0)))&((r3_lattices(esk5_0,X42,esk8_1(X42))|~r2_hidden(X42,esk6_0)|~m1_subset_1(X42,u1_struct_0(esk5_0)))&(r2_hidden(esk8_1(X42),esk7_0)|~r2_hidden(X42,esk6_0)|~m1_subset_1(X42,u1_struct_0(esk5_0)))))&~r3_lattices(esk5_0,k15_lattice3(esk5_0,esk6_0),k15_lattice3(esk5_0,esk7_0)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])])])).
% 0.20/0.42  fof(c_0_13, plain, ![X16, X17]:(v2_struct_0(X16)|~l3_lattices(X16)|m1_subset_1(k15_lattice3(X16,X17),u1_struct_0(X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k15_lattice3])])])).
% 0.20/0.42  cnf(c_0_14, plain, (k15_lattice3(X1,X2)=k15_lattice3(X1,a_2_5_lattice3(X1,X2))|v2_struct_0(X1)|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.42  cnf(c_0_15, negated_conjecture, (v4_lattice3(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.42  cnf(c_0_16, negated_conjecture, (v10_lattices(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.42  cnf(c_0_17, negated_conjecture, (l3_lattices(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.42  cnf(c_0_18, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.42  fof(c_0_19, plain, ![X18, X19, X20, X22, X23]:((((m1_subset_1(esk2_3(X18,X19,X20),u1_struct_0(X19))|~r2_hidden(X18,a_2_2_lattice3(X19,X20))|(v2_struct_0(X19)|~v10_lattices(X19)|~v4_lattice3(X19)|~l3_lattices(X19)))&(X18=esk2_3(X18,X19,X20)|~r2_hidden(X18,a_2_2_lattice3(X19,X20))|(v2_struct_0(X19)|~v10_lattices(X19)|~v4_lattice3(X19)|~l3_lattices(X19))))&(r4_lattice3(X19,esk2_3(X18,X19,X20),X20)|~r2_hidden(X18,a_2_2_lattice3(X19,X20))|(v2_struct_0(X19)|~v10_lattices(X19)|~v4_lattice3(X19)|~l3_lattices(X19))))&(~m1_subset_1(X23,u1_struct_0(X19))|X18!=X23|~r4_lattice3(X19,X23,X22)|r2_hidden(X18,a_2_2_lattice3(X19,X22))|(v2_struct_0(X19)|~v10_lattices(X19)|~v4_lattice3(X19)|~l3_lattices(X19)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_2_lattice3])])])])])])])).
% 0.20/0.42  fof(c_0_20, plain, ![X10, X11, X12, X13, X14]:((~r4_lattice3(X10,X11,X12)|(~m1_subset_1(X13,u1_struct_0(X10))|(~r2_hidden(X13,X12)|r1_lattices(X10,X13,X11)))|~m1_subset_1(X11,u1_struct_0(X10))|(v2_struct_0(X10)|~l3_lattices(X10)))&((m1_subset_1(esk1_3(X10,X11,X14),u1_struct_0(X10))|r4_lattice3(X10,X11,X14)|~m1_subset_1(X11,u1_struct_0(X10))|(v2_struct_0(X10)|~l3_lattices(X10)))&((r2_hidden(esk1_3(X10,X11,X14),X14)|r4_lattice3(X10,X11,X14)|~m1_subset_1(X11,u1_struct_0(X10))|(v2_struct_0(X10)|~l3_lattices(X10)))&(~r1_lattices(X10,esk1_3(X10,X11,X14),X11)|r4_lattice3(X10,X11,X14)|~m1_subset_1(X11,u1_struct_0(X10))|(v2_struct_0(X10)|~l3_lattices(X10)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_lattice3])])])])])])])).
% 0.20/0.42  cnf(c_0_21, plain, (v2_struct_0(X1)|m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.42  cnf(c_0_22, negated_conjecture, (k15_lattice3(esk5_0,a_2_5_lattice3(esk5_0,X1))=k15_lattice3(esk5_0,X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16]), c_0_17])]), c_0_18])).
% 0.20/0.42  fof(c_0_23, plain, ![X34, X35, X36]:((r3_lattices(X34,X35,k15_lattice3(X34,X36))|~r2_hidden(X35,X36)|~m1_subset_1(X35,u1_struct_0(X34))|(v2_struct_0(X34)|~v10_lattices(X34)|~v4_lattice3(X34)|~l3_lattices(X34)))&(r3_lattices(X34,k16_lattice3(X34,X36),X35)|~r2_hidden(X35,X36)|~m1_subset_1(X35,u1_struct_0(X34))|(v2_struct_0(X34)|~v10_lattices(X34)|~v4_lattice3(X34)|~l3_lattices(X34)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t38_lattice3])])])])])).
% 0.20/0.42  cnf(c_0_24, plain, (r2_hidden(X3,a_2_2_lattice3(X2,X4))|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|X3!=X1|~r4_lattice3(X2,X1,X4)|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.42  cnf(c_0_25, plain, (m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))|r4_lattice3(X1,X2,X3)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.42  cnf(c_0_26, negated_conjecture, (m1_subset_1(k15_lattice3(esk5_0,X1),u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_17])]), c_0_18])).
% 0.20/0.42  fof(c_0_27, plain, ![X32, X33]:(v2_struct_0(X32)|~v10_lattices(X32)|~v4_lattice3(X32)|~l3_lattices(X32)|k15_lattice3(X32,X33)=k16_lattice3(X32,a_2_2_lattice3(X32,X33))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t37_lattice3])])])])).
% 0.20/0.42  cnf(c_0_28, plain, (r3_lattices(X1,k16_lattice3(X1,X2),X3)|v2_struct_0(X1)|~r2_hidden(X3,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.42  cnf(c_0_29, plain, (r2_hidden(X1,a_2_2_lattice3(X2,X3))|v2_struct_0(X2)|~v4_lattice3(X2)|~r4_lattice3(X2,X1,X3)|~m1_subset_1(X1,u1_struct_0(X2))|~v10_lattices(X2)|~l3_lattices(X2)), inference(er,[status(thm)],[c_0_24])).
% 0.20/0.42  cnf(c_0_30, negated_conjecture, (r4_lattice3(esk5_0,k15_lattice3(esk5_0,X1),X2)|m1_subset_1(esk1_3(esk5_0,k15_lattice3(esk5_0,X1),X2),u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_17])]), c_0_18])).
% 0.20/0.42  cnf(c_0_31, plain, (v2_struct_0(X1)|k15_lattice3(X1,X2)=k16_lattice3(X1,a_2_2_lattice3(X1,X2))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.42  cnf(c_0_32, negated_conjecture, (r3_lattices(esk5_0,k16_lattice3(esk5_0,X1),k15_lattice3(esk5_0,X2))|~r2_hidden(k15_lattice3(esk5_0,X2),X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_26]), c_0_15]), c_0_16]), c_0_17])]), c_0_18])).
% 0.20/0.42  cnf(c_0_33, negated_conjecture, (r2_hidden(k15_lattice3(esk5_0,X1),a_2_2_lattice3(esk5_0,X2))|m1_subset_1(esk1_3(esk5_0,k15_lattice3(esk5_0,X1),X2),u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_15]), c_0_26]), c_0_16]), c_0_17])]), c_0_18])).
% 0.20/0.42  cnf(c_0_34, negated_conjecture, (k16_lattice3(esk5_0,a_2_2_lattice3(esk5_0,X1))=k15_lattice3(esk5_0,X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_15]), c_0_16]), c_0_17])]), c_0_18])).
% 0.20/0.42  cnf(c_0_35, negated_conjecture, (~r3_lattices(esk5_0,k15_lattice3(esk5_0,esk6_0),k15_lattice3(esk5_0,esk7_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.42  cnf(c_0_36, negated_conjecture, (r3_lattices(esk5_0,k15_lattice3(esk5_0,X1),k15_lattice3(esk5_0,X2))|m1_subset_1(esk1_3(esk5_0,k15_lattice3(esk5_0,X2),X1),u1_struct_0(esk5_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34])).
% 0.20/0.42  cnf(c_0_37, plain, (r2_hidden(esk1_3(X1,X2,X3),X3)|r4_lattice3(X1,X2,X3)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.42  cnf(c_0_38, negated_conjecture, (m1_subset_1(esk8_1(X1),u1_struct_0(esk5_0))|~r2_hidden(X1,esk6_0)|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.42  cnf(c_0_39, negated_conjecture, (m1_subset_1(esk1_3(esk5_0,k15_lattice3(esk5_0,esk7_0),esk6_0),u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.20/0.42  cnf(c_0_40, negated_conjecture, (r2_hidden(esk1_3(esk5_0,k15_lattice3(esk5_0,X1),X2),X2)|r4_lattice3(esk5_0,k15_lattice3(esk5_0,X1),X2)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_26]), c_0_17])]), c_0_18])).
% 0.20/0.42  fof(c_0_41, plain, ![X24, X25, X26, X29, X30, X31]:((((m1_subset_1(esk3_3(X24,X25,X26),u1_struct_0(X25))|~r2_hidden(X24,a_2_5_lattice3(X25,X26))|(v2_struct_0(X25)|~v10_lattices(X25)|~v4_lattice3(X25)|~l3_lattices(X25)))&(X24=esk3_3(X24,X25,X26)|~r2_hidden(X24,a_2_5_lattice3(X25,X26))|(v2_struct_0(X25)|~v10_lattices(X25)|~v4_lattice3(X25)|~l3_lattices(X25))))&(((m1_subset_1(esk4_3(X24,X25,X26),u1_struct_0(X25))|~r2_hidden(X24,a_2_5_lattice3(X25,X26))|(v2_struct_0(X25)|~v10_lattices(X25)|~v4_lattice3(X25)|~l3_lattices(X25)))&(r3_lattices(X25,esk3_3(X24,X25,X26),esk4_3(X24,X25,X26))|~r2_hidden(X24,a_2_5_lattice3(X25,X26))|(v2_struct_0(X25)|~v10_lattices(X25)|~v4_lattice3(X25)|~l3_lattices(X25))))&(r2_hidden(esk4_3(X24,X25,X26),X26)|~r2_hidden(X24,a_2_5_lattice3(X25,X26))|(v2_struct_0(X25)|~v10_lattices(X25)|~v4_lattice3(X25)|~l3_lattices(X25)))))&(~m1_subset_1(X30,u1_struct_0(X25))|X24!=X30|(~m1_subset_1(X31,u1_struct_0(X25))|~r3_lattices(X25,X30,X31)|~r2_hidden(X31,X29))|r2_hidden(X24,a_2_5_lattice3(X25,X29))|(v2_struct_0(X25)|~v10_lattices(X25)|~v4_lattice3(X25)|~l3_lattices(X25)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_5_lattice3])])])])])])])).
% 0.20/0.42  cnf(c_0_42, negated_conjecture, (r3_lattices(esk5_0,X1,esk8_1(X1))|~r2_hidden(X1,esk6_0)|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.42  cnf(c_0_43, negated_conjecture, (m1_subset_1(esk8_1(esk1_3(esk5_0,k15_lattice3(esk5_0,esk7_0),esk6_0)),u1_struct_0(esk5_0))|~r2_hidden(esk1_3(esk5_0,k15_lattice3(esk5_0,esk7_0),esk6_0),esk6_0)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.20/0.42  cnf(c_0_44, negated_conjecture, (r2_hidden(esk1_3(esk5_0,k15_lattice3(esk5_0,X1),X2),X2)|r2_hidden(k15_lattice3(esk5_0,X1),a_2_2_lattice3(esk5_0,X2))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_40]), c_0_15]), c_0_26]), c_0_16]), c_0_17])]), c_0_18])).
% 0.20/0.42  cnf(c_0_45, plain, (r2_hidden(X3,a_2_5_lattice3(X2,X5))|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|X3!=X1|~m1_subset_1(X4,u1_struct_0(X2))|~r3_lattices(X2,X1,X4)|~r2_hidden(X4,X5)|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.20/0.42  cnf(c_0_46, negated_conjecture, (r3_lattices(esk5_0,esk1_3(esk5_0,k15_lattice3(esk5_0,esk7_0),esk6_0),esk8_1(esk1_3(esk5_0,k15_lattice3(esk5_0,esk7_0),esk6_0)))|~r2_hidden(esk1_3(esk5_0,k15_lattice3(esk5_0,esk7_0),esk6_0),esk6_0)), inference(spm,[status(thm)],[c_0_42, c_0_39])).
% 0.20/0.42  cnf(c_0_47, negated_conjecture, (r2_hidden(k15_lattice3(esk5_0,esk7_0),a_2_2_lattice3(esk5_0,esk6_0))|m1_subset_1(esk8_1(esk1_3(esk5_0,k15_lattice3(esk5_0,esk7_0),esk6_0)),u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.20/0.42  cnf(c_0_48, plain, (r2_hidden(X1,a_2_5_lattice3(X2,X3))|v2_struct_0(X2)|~v4_lattice3(X2)|~r2_hidden(X4,X3)|~r3_lattices(X2,X1,X4)|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))|~v10_lattices(X2)|~l3_lattices(X2)), inference(er,[status(thm)],[c_0_45])).
% 0.20/0.42  cnf(c_0_49, negated_conjecture, (r2_hidden(k15_lattice3(esk5_0,esk7_0),a_2_2_lattice3(esk5_0,esk6_0))|r3_lattices(esk5_0,esk1_3(esk5_0,k15_lattice3(esk5_0,esk7_0),esk6_0),esk8_1(esk1_3(esk5_0,k15_lattice3(esk5_0,esk7_0),esk6_0)))), inference(spm,[status(thm)],[c_0_46, c_0_44])).
% 0.20/0.42  cnf(c_0_50, negated_conjecture, (m1_subset_1(esk8_1(esk1_3(esk5_0,k15_lattice3(esk5_0,esk7_0),esk6_0)),u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_47]), c_0_34]), c_0_35])).
% 0.20/0.42  cnf(c_0_51, plain, (r3_lattices(X1,X2,k15_lattice3(X1,X3))|v2_struct_0(X1)|~r2_hidden(X2,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.42  cnf(c_0_52, negated_conjecture, (r2_hidden(esk1_3(esk5_0,k15_lattice3(esk5_0,esk7_0),esk6_0),a_2_5_lattice3(esk5_0,X1))|r2_hidden(k15_lattice3(esk5_0,esk7_0),a_2_2_lattice3(esk5_0,esk6_0))|~r2_hidden(esk8_1(esk1_3(esk5_0,k15_lattice3(esk5_0,esk7_0),esk6_0)),X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_15]), c_0_50]), c_0_39]), c_0_16]), c_0_17])]), c_0_18])).
% 0.20/0.42  cnf(c_0_53, negated_conjecture, (r2_hidden(esk8_1(X1),esk7_0)|~r2_hidden(X1,esk6_0)|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.42  fof(c_0_54, plain, ![X7, X8, X9]:((~r3_lattices(X7,X8,X9)|r1_lattices(X7,X8,X9)|(v2_struct_0(X7)|~v6_lattices(X7)|~v8_lattices(X7)|~v9_lattices(X7)|~l3_lattices(X7)|~m1_subset_1(X8,u1_struct_0(X7))|~m1_subset_1(X9,u1_struct_0(X7))))&(~r1_lattices(X7,X8,X9)|r3_lattices(X7,X8,X9)|(v2_struct_0(X7)|~v6_lattices(X7)|~v8_lattices(X7)|~v9_lattices(X7)|~l3_lattices(X7)|~m1_subset_1(X8,u1_struct_0(X7))|~m1_subset_1(X9,u1_struct_0(X7))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).
% 0.20/0.42  cnf(c_0_55, negated_conjecture, (r3_lattices(esk5_0,esk1_3(esk5_0,k15_lattice3(esk5_0,esk7_0),esk6_0),k15_lattice3(esk5_0,X1))|~r2_hidden(esk1_3(esk5_0,k15_lattice3(esk5_0,esk7_0),esk6_0),X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_39]), c_0_15]), c_0_16]), c_0_17])]), c_0_18])).
% 0.20/0.42  cnf(c_0_56, negated_conjecture, (r2_hidden(esk1_3(esk5_0,k15_lattice3(esk5_0,esk7_0),esk6_0),a_2_5_lattice3(esk5_0,esk7_0))|r2_hidden(k15_lattice3(esk5_0,esk7_0),a_2_2_lattice3(esk5_0,esk6_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_39])]), c_0_44])).
% 0.20/0.42  cnf(c_0_57, plain, (r1_lattices(X1,X2,X3)|v2_struct_0(X1)|~r3_lattices(X1,X2,X3)|~v6_lattices(X1)|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.20/0.42  cnf(c_0_58, negated_conjecture, (r2_hidden(k15_lattice3(esk5_0,esk7_0),a_2_2_lattice3(esk5_0,esk6_0))|r3_lattices(esk5_0,esk1_3(esk5_0,k15_lattice3(esk5_0,esk7_0),esk6_0),k15_lattice3(esk5_0,esk7_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_22])).
% 0.20/0.42  fof(c_0_59, plain, ![X6]:(((((((~v2_struct_0(X6)|(v2_struct_0(X6)|~v10_lattices(X6))|~l3_lattices(X6))&(v4_lattices(X6)|(v2_struct_0(X6)|~v10_lattices(X6))|~l3_lattices(X6)))&(v5_lattices(X6)|(v2_struct_0(X6)|~v10_lattices(X6))|~l3_lattices(X6)))&(v6_lattices(X6)|(v2_struct_0(X6)|~v10_lattices(X6))|~l3_lattices(X6)))&(v7_lattices(X6)|(v2_struct_0(X6)|~v10_lattices(X6))|~l3_lattices(X6)))&(v8_lattices(X6)|(v2_struct_0(X6)|~v10_lattices(X6))|~l3_lattices(X6)))&(v9_lattices(X6)|(v2_struct_0(X6)|~v10_lattices(X6))|~l3_lattices(X6))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).
% 0.20/0.42  cnf(c_0_60, negated_conjecture, (r2_hidden(k15_lattice3(esk5_0,esk7_0),a_2_2_lattice3(esk5_0,esk6_0))|r1_lattices(esk5_0,esk1_3(esk5_0,k15_lattice3(esk5_0,esk7_0),esk6_0),k15_lattice3(esk5_0,esk7_0))|~v9_lattices(esk5_0)|~v8_lattices(esk5_0)|~v6_lattices(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_26]), c_0_39]), c_0_17])]), c_0_18])).
% 0.20/0.42  cnf(c_0_61, plain, (v6_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.20/0.42  cnf(c_0_62, negated_conjecture, (r2_hidden(k15_lattice3(esk5_0,esk7_0),a_2_2_lattice3(esk5_0,esk6_0))|r1_lattices(esk5_0,esk1_3(esk5_0,k15_lattice3(esk5_0,esk7_0),esk6_0),k15_lattice3(esk5_0,esk7_0))|~v9_lattices(esk5_0)|~v8_lattices(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_16]), c_0_17])]), c_0_18])).
% 0.20/0.42  cnf(c_0_63, plain, (v8_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.20/0.42  cnf(c_0_64, negated_conjecture, (r2_hidden(k15_lattice3(esk5_0,esk7_0),a_2_2_lattice3(esk5_0,esk6_0))|r1_lattices(esk5_0,esk1_3(esk5_0,k15_lattice3(esk5_0,esk7_0),esk6_0),k15_lattice3(esk5_0,esk7_0))|~v9_lattices(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_16]), c_0_17])]), c_0_18])).
% 0.20/0.42  cnf(c_0_65, plain, (v9_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.20/0.42  cnf(c_0_66, plain, (r4_lattice3(X1,X2,X3)|v2_struct_0(X1)|~r1_lattices(X1,esk1_3(X1,X2,X3),X2)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.42  cnf(c_0_67, negated_conjecture, (r2_hidden(k15_lattice3(esk5_0,esk7_0),a_2_2_lattice3(esk5_0,esk6_0))|r1_lattices(esk5_0,esk1_3(esk5_0,k15_lattice3(esk5_0,esk7_0),esk6_0),k15_lattice3(esk5_0,esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_16]), c_0_17])]), c_0_18])).
% 0.20/0.42  cnf(c_0_68, negated_conjecture, (r2_hidden(k15_lattice3(esk5_0,esk7_0),a_2_2_lattice3(esk5_0,esk6_0))|r4_lattice3(esk5_0,k15_lattice3(esk5_0,esk7_0),esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_26]), c_0_17])]), c_0_18])).
% 0.20/0.42  cnf(c_0_69, plain, (r3_lattices(X1,k16_lattice3(X1,X2),k15_lattice3(X1,X3))|v2_struct_0(X1)|~v4_lattice3(X1)|~r2_hidden(k15_lattice3(X1,X3),X2)|~v10_lattices(X1)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_28, c_0_21])).
% 0.20/0.42  cnf(c_0_70, negated_conjecture, (r2_hidden(k15_lattice3(esk5_0,esk7_0),a_2_2_lattice3(esk5_0,esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_68]), c_0_15]), c_0_26]), c_0_16]), c_0_17])]), c_0_18])).
% 0.20/0.42  cnf(c_0_71, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_34]), c_0_15]), c_0_16]), c_0_17])]), c_0_35]), c_0_18]), ['proof']).
% 0.20/0.42  # SZS output end CNFRefutation
% 0.20/0.42  # Proof object total steps             : 72
% 0.20/0.42  # Proof object clause steps            : 51
% 0.20/0.42  # Proof object formula steps           : 21
% 0.20/0.42  # Proof object conjectures             : 37
% 0.20/0.42  # Proof object clause conjectures      : 34
% 0.20/0.42  # Proof object formula conjectures     : 3
% 0.20/0.42  # Proof object initial clauses used    : 22
% 0.20/0.42  # Proof object initial formulas used   : 10
% 0.20/0.42  # Proof object generating inferences   : 27
% 0.20/0.42  # Proof object simplifying inferences  : 89
% 0.20/0.42  # Training examples: 0 positive, 0 negative
% 0.20/0.42  # Parsed axioms                        : 10
% 0.20/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.42  # Initial clauses                      : 37
% 0.20/0.42  # Removed in clause preprocessing      : 1
% 0.20/0.42  # Initial clauses in saturation        : 36
% 0.20/0.42  # Processed clauses                    : 195
% 0.20/0.42  # ...of these trivial                  : 0
% 0.20/0.42  # ...subsumed                          : 31
% 0.20/0.42  # ...remaining for further processing  : 164
% 0.20/0.42  # Other redundant clauses eliminated   : 2
% 0.20/0.42  # Clauses deleted for lack of memory   : 0
% 0.20/0.42  # Backward-subsumed                    : 12
% 0.20/0.42  # Backward-rewritten                   : 20
% 0.20/0.42  # Generated clauses                    : 277
% 0.20/0.42  # ...of the previous two non-trivial   : 266
% 0.20/0.42  # Contextual simplify-reflections      : 1
% 0.20/0.42  # Paramodulations                      : 275
% 0.20/0.42  # Factorizations                       : 0
% 0.20/0.42  # Equation resolutions                 : 2
% 0.20/0.42  # Propositional unsat checks           : 0
% 0.20/0.42  #    Propositional check models        : 0
% 0.20/0.42  #    Propositional check unsatisfiable : 0
% 0.20/0.42  #    Propositional clauses             : 0
% 0.20/0.42  #    Propositional clauses after purity: 0
% 0.20/0.42  #    Propositional unsat core size     : 0
% 0.20/0.42  #    Propositional preprocessing time  : 0.000
% 0.20/0.42  #    Propositional encoding time       : 0.000
% 0.20/0.42  #    Propositional solver time         : 0.000
% 0.20/0.42  #    Success case prop preproc time    : 0.000
% 0.20/0.42  #    Success case prop encoding time   : 0.000
% 0.20/0.42  #    Success case prop solver time     : 0.000
% 0.20/0.42  # Current number of processed clauses  : 94
% 0.20/0.42  #    Positive orientable unit clauses  : 13
% 0.20/0.42  #    Positive unorientable unit clauses: 0
% 0.20/0.42  #    Negative unit clauses             : 2
% 0.20/0.42  #    Non-unit-clauses                  : 79
% 0.20/0.42  # Current number of unprocessed clauses: 120
% 0.20/0.42  # ...number of literals in the above   : 376
% 0.20/0.42  # Current number of archived formulas  : 0
% 0.20/0.42  # Current number of archived clauses   : 68
% 0.20/0.42  # Clause-clause subsumption calls (NU) : 2196
% 0.20/0.42  # Rec. Clause-clause subsumption calls : 684
% 0.20/0.42  # Non-unit clause-clause subsumptions  : 44
% 0.20/0.42  # Unit Clause-clause subsumption calls : 63
% 0.20/0.42  # Rewrite failures with RHS unbound    : 0
% 0.20/0.42  # BW rewrite match attempts            : 13
% 0.20/0.42  # BW rewrite match successes           : 5
% 0.20/0.42  # Condensation attempts                : 0
% 0.20/0.42  # Condensation successes               : 0
% 0.20/0.42  # Termbank termtop insertions          : 12571
% 0.20/0.42  
% 0.20/0.42  # -------------------------------------------------
% 0.20/0.42  # User time                : 0.069 s
% 0.20/0.42  # System time              : 0.008 s
% 0.20/0.42  # Total time               : 0.077 s
% 0.20/0.42  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
