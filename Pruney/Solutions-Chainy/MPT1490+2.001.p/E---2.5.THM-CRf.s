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
% DateTime   : Thu Dec  3 11:14:58 EST 2020

% Result     : Theorem 40.61s
% Output     : CNFRefutation 40.61s
% Verified   : 
% Statistics : Number of formulae       :  119 (10427 expanded)
%              Number of clauses        :  100 (3319 expanded)
%              Number of leaves         :    9 (2565 expanded)
%              Depth                    :   35
%              Number of atoms          :  676 (69313 expanded)
%              Number of equality atoms :   32 (2112 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   28 (   5 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t23_lattice3,conjecture,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X2)
        & v10_lattices(X2)
        & v17_lattices(X2)
        & l3_lattices(X2) )
     => ! [X3] :
          ( m1_subset_1(X3,u1_struct_0(X2))
         => ( r4_lattice3(X2,X3,X1)
          <=> r3_lattice3(X2,k7_lattices(X2,X3),a_2_0_lattice3(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_lattice3)).

fof(t49_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v17_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => k7_lattices(X1,k7_lattices(X1,X2)) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_lattices)).

fof(fraenkel_a_2_0_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X3)
        & v10_lattices(X3)
        & v17_lattices(X3)
        & l3_lattices(X3) )
     => ( r2_hidden(X1,a_2_0_lattice3(X2,X3))
      <=> ? [X4] :
            ( m1_subset_1(X4,u1_struct_0(X3))
            & X1 = k7_lattices(X3,X4)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_0_lattice3)).

fof(dt_k7_lattices,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => m1_subset_1(k7_lattices(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_lattices)).

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

fof(t53_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v17_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r3_lattices(X1,X2,X3)
               => r3_lattices(X1,k7_lattices(X1,X3),k7_lattices(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_lattices)).

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

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( ~ v2_struct_0(X2)
          & v10_lattices(X2)
          & v17_lattices(X2)
          & l3_lattices(X2) )
       => ! [X3] :
            ( m1_subset_1(X3,u1_struct_0(X2))
           => ( r4_lattice3(X2,X3,X1)
            <=> r3_lattice3(X2,k7_lattices(X2,X3),a_2_0_lattice3(X1,X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t23_lattice3])).

fof(c_0_10,plain,(
    ! [X11,X12] :
      ( v2_struct_0(X11)
      | ~ v10_lattices(X11)
      | ~ v17_lattices(X11)
      | ~ l3_lattices(X11)
      | ~ m1_subset_1(X12,u1_struct_0(X11))
      | k7_lattices(X11,k7_lattices(X11,X12)) = X12 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t49_lattices])])])])).

fof(c_0_11,negated_conjecture,
    ( ~ v2_struct_0(esk5_0)
    & v10_lattices(esk5_0)
    & v17_lattices(esk5_0)
    & l3_lattices(esk5_0)
    & m1_subset_1(esk6_0,u1_struct_0(esk5_0))
    & ( ~ r4_lattice3(esk5_0,esk6_0,esk4_0)
      | ~ r3_lattice3(esk5_0,k7_lattices(esk5_0,esk6_0),a_2_0_lattice3(esk4_0,esk5_0)) )
    & ( r4_lattice3(esk5_0,esk6_0,esk4_0)
      | r3_lattice3(esk5_0,k7_lattices(esk5_0,esk6_0),a_2_0_lattice3(esk4_0,esk5_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).

cnf(c_0_12,plain,
    ( v2_struct_0(X1)
    | k7_lattices(X1,k7_lattices(X1,X2)) = X2
    | ~ v10_lattices(X1)
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( v17_lattices(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_14,negated_conjecture,
    ( v10_lattices(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( l3_lattices(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_17,plain,(
    ! [X28,X29,X30,X32] :
      ( ( m1_subset_1(esk3_3(X28,X29,X30),u1_struct_0(X30))
        | ~ r2_hidden(X28,a_2_0_lattice3(X29,X30))
        | v2_struct_0(X30)
        | ~ v10_lattices(X30)
        | ~ v17_lattices(X30)
        | ~ l3_lattices(X30) )
      & ( X28 = k7_lattices(X30,esk3_3(X28,X29,X30))
        | ~ r2_hidden(X28,a_2_0_lattice3(X29,X30))
        | v2_struct_0(X30)
        | ~ v10_lattices(X30)
        | ~ v17_lattices(X30)
        | ~ l3_lattices(X30) )
      & ( r2_hidden(esk3_3(X28,X29,X30),X29)
        | ~ r2_hidden(X28,a_2_0_lattice3(X29,X30))
        | v2_struct_0(X30)
        | ~ v10_lattices(X30)
        | ~ v17_lattices(X30)
        | ~ l3_lattices(X30) )
      & ( ~ m1_subset_1(X32,u1_struct_0(X30))
        | X28 != k7_lattices(X30,X32)
        | ~ r2_hidden(X32,X29)
        | r2_hidden(X28,a_2_0_lattice3(X29,X30))
        | v2_struct_0(X30)
        | ~ v10_lattices(X30)
        | ~ v17_lattices(X30)
        | ~ l3_lattices(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_0_lattice3])])])])])])).

cnf(c_0_18,negated_conjecture,
    ( k7_lattices(esk5_0,k7_lattices(esk5_0,X1)) = X1
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_19,plain,
    ( X1 = k7_lattices(X2,esk3_3(X1,X3,X2))
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_0_lattice3(X3,X2))
    | ~ v10_lattices(X2)
    | ~ v17_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_20,negated_conjecture,
    ( esk3_3(X1,X2,esk5_0) = k7_lattices(esk5_0,X1)
    | ~ r2_hidden(X1,a_2_0_lattice3(X2,esk5_0))
    | ~ m1_subset_1(esk3_3(X1,X2,esk5_0),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_13]),c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_21,plain,
    ( m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X3))
    | v2_struct_0(X3)
    | ~ r2_hidden(X1,a_2_0_lattice3(X2,X3))
    | ~ v10_lattices(X3)
    | ~ v17_lattices(X3)
    | ~ l3_lattices(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( r2_hidden(X3,a_2_0_lattice3(X4,X2))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | X3 != k7_lattices(X2,X1)
    | ~ r2_hidden(X1,X4)
    | ~ v10_lattices(X2)
    | ~ v17_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),X2)
    | v2_struct_0(X3)
    | ~ r2_hidden(X1,a_2_0_lattice3(X2,X3))
    | ~ v10_lattices(X3)
    | ~ v17_lattices(X3)
    | ~ l3_lattices(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( esk3_3(X1,X2,esk5_0) = k7_lattices(esk5_0,X1)
    | ~ r2_hidden(X1,a_2_0_lattice3(X2,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_13]),c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(X1,a_2_0_lattice3(X2,esk5_0))
    | ~ r2_hidden(k7_lattices(esk5_0,X1),X2)
    | ~ m1_subset_1(k7_lattices(esk5_0,X1),u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(er,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_18]),c_0_13]),c_0_14]),c_0_15])]),c_0_16])])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(k7_lattices(esk5_0,X1),X2)
    | ~ r2_hidden(X1,a_2_0_lattice3(X2,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_13]),c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_27,plain,
    ( r2_hidden(k7_lattices(X1,X2),a_2_0_lattice3(X3,X1))
    | v2_struct_0(X1)
    | ~ r2_hidden(X2,X3)
    | ~ v17_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(k7_lattices(esk5_0,X1),a_2_0_lattice3(X2,esk5_0))
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(k7_lattices(esk5_0,X1),u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_18])).

fof(c_0_29,plain,(
    ! [X6,X7] :
      ( v2_struct_0(X6)
      | ~ l3_lattices(X6)
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | m1_subset_1(k7_lattices(X6,X7),u1_struct_0(X6)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_lattices])])])).

cnf(c_0_30,negated_conjecture,
    ( k7_lattices(esk5_0,k7_lattices(esk5_0,X1)) = X1
    | ~ r2_hidden(X1,a_2_0_lattice3(X2,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_24]),c_0_13]),c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(k7_lattices(esk5_0,k7_lattices(esk5_0,X1)),X2)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_13]),c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(X1,a_2_0_lattice3(a_2_0_lattice3(X2,esk5_0),esk5_0))
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(k7_lattices(esk5_0,X1),u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_28])).

cnf(c_0_33,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k7_lattices(X1,X2),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(k7_lattices(esk5_0,X1),u1_struct_0(esk5_0))
    | ~ r2_hidden(X1,a_2_0_lattice3(X2,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_24]),c_0_13]),c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_35,negated_conjecture,
    ( k7_lattices(esk5_0,k7_lattices(esk5_0,k7_lattices(esk5_0,k7_lattices(esk5_0,X1)))) = k7_lattices(esk5_0,k7_lattices(esk5_0,X1))
    | ~ r2_hidden(X1,a_2_0_lattice3(X2,esk5_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(X1,a_2_0_lattice3(a_2_0_lattice3(X2,esk5_0),esk5_0))
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_15])]),c_0_16])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(k7_lattices(esk5_0,k7_lattices(esk5_0,k7_lattices(esk5_0,X1))),u1_struct_0(esk5_0))
    | ~ r2_hidden(X1,a_2_0_lattice3(X2,esk5_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( k7_lattices(esk5_0,k7_lattices(esk5_0,k7_lattices(esk5_0,k7_lattices(esk5_0,X1)))) = k7_lattices(esk5_0,k7_lattices(esk5_0,X1))
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(k7_lattices(esk5_0,k7_lattices(esk5_0,k7_lattices(esk5_0,X1))),u1_struct_0(esk5_0))
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_36])).

cnf(c_0_40,negated_conjecture,
    ( k7_lattices(esk5_0,k7_lattices(esk5_0,k7_lattices(esk5_0,k7_lattices(esk5_0,esk3_3(X1,X2,X3))))) = k7_lattices(esk5_0,k7_lattices(esk5_0,esk3_3(X1,X2,X3)))
    | v2_struct_0(X3)
    | ~ r2_hidden(X1,a_2_0_lattice3(X2,X3))
    | ~ v17_lattices(X3)
    | ~ m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(esk5_0))
    | ~ v10_lattices(X3)
    | ~ l3_lattices(X3) ),
    inference(spm,[status(thm)],[c_0_38,c_0_23])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(k7_lattices(esk5_0,k7_lattices(esk5_0,k7_lattices(esk5_0,esk3_3(X1,X2,X3)))),u1_struct_0(esk5_0))
    | v2_struct_0(X3)
    | ~ r2_hidden(X1,a_2_0_lattice3(X2,X3))
    | ~ v17_lattices(X3)
    | ~ m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(esk5_0))
    | ~ v10_lattices(X3)
    | ~ l3_lattices(X3) ),
    inference(spm,[status(thm)],[c_0_39,c_0_23])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(X1,a_2_0_lattice3(X2,esk5_0))
    | v2_struct_0(X3)
    | X1 != k7_lattices(esk5_0,k7_lattices(esk5_0,esk3_3(X4,X5,X3)))
    | ~ r2_hidden(k7_lattices(esk5_0,k7_lattices(esk5_0,k7_lattices(esk5_0,esk3_3(X4,X5,X3)))),X2)
    | ~ r2_hidden(X4,a_2_0_lattice3(X5,X3))
    | ~ v17_lattices(X3)
    | ~ m1_subset_1(esk3_3(X4,X5,X3),u1_struct_0(esk5_0))
    | ~ v10_lattices(X3)
    | ~ l3_lattices(X3) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_40]),c_0_13]),c_0_14]),c_0_15])]),c_0_16]),c_0_41])).

fof(c_0_43,plain,(
    ! [X16,X17,X18,X19,X20] :
      ( ( ~ r3_lattice3(X16,X17,X18)
        | ~ m1_subset_1(X19,u1_struct_0(X16))
        | ~ r2_hidden(X19,X18)
        | r1_lattices(X16,X17,X19)
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | v2_struct_0(X16)
        | ~ l3_lattices(X16) )
      & ( m1_subset_1(esk1_3(X16,X17,X20),u1_struct_0(X16))
        | r3_lattice3(X16,X17,X20)
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | v2_struct_0(X16)
        | ~ l3_lattices(X16) )
      & ( r2_hidden(esk1_3(X16,X17,X20),X20)
        | r3_lattice3(X16,X17,X20)
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | v2_struct_0(X16)
        | ~ l3_lattices(X16) )
      & ( ~ r1_lattices(X16,X17,esk1_3(X16,X17,X20))
        | r3_lattice3(X16,X17,X20)
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | v2_struct_0(X16)
        | ~ l3_lattices(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattice3])])])])])])])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(X1,a_2_0_lattice3(X2,esk5_0))
    | v2_struct_0(X3)
    | X1 != esk3_3(X4,X5,X3)
    | ~ r2_hidden(k7_lattices(esk5_0,esk3_3(X4,X5,X3)),X2)
    | ~ r2_hidden(X4,a_2_0_lattice3(X5,X3))
    | ~ v17_lattices(X3)
    | ~ m1_subset_1(esk3_3(X4,X5,X3),u1_struct_0(esk5_0))
    | ~ v10_lattices(X3)
    | ~ l3_lattices(X3) ),
    inference(spm,[status(thm)],[c_0_42,c_0_18])).

fof(c_0_45,plain,(
    ! [X8,X9,X10] :
      ( ( ~ r3_lattices(X8,X9,X10)
        | r1_lattices(X8,X9,X10)
        | v2_struct_0(X8)
        | ~ v6_lattices(X8)
        | ~ v8_lattices(X8)
        | ~ v9_lattices(X8)
        | ~ l3_lattices(X8)
        | ~ m1_subset_1(X9,u1_struct_0(X8))
        | ~ m1_subset_1(X10,u1_struct_0(X8)) )
      & ( ~ r1_lattices(X8,X9,X10)
        | r3_lattices(X8,X9,X10)
        | v2_struct_0(X8)
        | ~ v6_lattices(X8)
        | ~ v8_lattices(X8)
        | ~ v9_lattices(X8)
        | ~ l3_lattices(X8)
        | ~ m1_subset_1(X9,u1_struct_0(X8))
        | ~ m1_subset_1(X10,u1_struct_0(X8)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).

fof(c_0_46,plain,(
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

cnf(c_0_47,plain,
    ( r1_lattices(X1,X2,X4)
    | v2_struct_0(X1)
    | ~ r3_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_48,negated_conjecture,
    ( r4_lattice3(esk5_0,esk6_0,esk4_0)
    | r3_lattice3(esk5_0,k7_lattices(esk5_0,esk6_0),a_2_0_lattice3(esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(X1,a_2_0_lattice3(a_2_0_lattice3(X2,esk5_0),esk5_0))
    | v2_struct_0(X3)
    | X1 != esk3_3(X4,X5,X3)
    | ~ r2_hidden(esk3_3(X4,X5,X3),X2)
    | ~ r2_hidden(X4,a_2_0_lattice3(X5,X3))
    | ~ v17_lattices(X3)
    | ~ m1_subset_1(esk3_3(X4,X5,X3),u1_struct_0(esk5_0))
    | ~ v10_lattices(X3)
    | ~ l3_lattices(X3) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_27]),c_0_13]),c_0_14]),c_0_15])]),c_0_16])).

fof(c_0_50,plain,(
    ! [X13,X14,X15] :
      ( v2_struct_0(X13)
      | ~ v10_lattices(X13)
      | ~ v17_lattices(X13)
      | ~ l3_lattices(X13)
      | ~ m1_subset_1(X14,u1_struct_0(X13))
      | ~ m1_subset_1(X15,u1_struct_0(X13))
      | ~ r3_lattices(X13,X14,X15)
      | r3_lattices(X13,k7_lattices(X13,X15),k7_lattices(X13,X14)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t53_lattices])])])])).

cnf(c_0_51,plain,
    ( r3_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_52,plain,
    ( v9_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_53,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_54,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_55,negated_conjecture,
    ( r4_lattice3(esk5_0,esk6_0,esk4_0)
    | r1_lattices(esk5_0,k7_lattices(esk5_0,esk6_0),X1)
    | ~ r2_hidden(X1,a_2_0_lattice3(esk4_0,esk5_0))
    | ~ m1_subset_1(k7_lattices(esk5_0,esk6_0),u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_15])]),c_0_16])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(X1,a_2_0_lattice3(a_2_0_lattice3(X2,esk5_0),esk5_0))
    | v2_struct_0(X3)
    | X1 != esk3_3(X4,X2,X3)
    | ~ r2_hidden(X4,a_2_0_lattice3(X2,X3))
    | ~ v17_lattices(X3)
    | ~ m1_subset_1(esk3_3(X4,X2,X3),u1_struct_0(esk5_0))
    | ~ v10_lattices(X3)
    | ~ l3_lattices(X3) ),
    inference(spm,[status(thm)],[c_0_49,c_0_23])).

fof(c_0_57,plain,(
    ! [X22,X23,X24,X25,X26] :
      ( ( ~ r4_lattice3(X22,X23,X24)
        | ~ m1_subset_1(X25,u1_struct_0(X22))
        | ~ r2_hidden(X25,X24)
        | r1_lattices(X22,X25,X23)
        | ~ m1_subset_1(X23,u1_struct_0(X22))
        | v2_struct_0(X22)
        | ~ l3_lattices(X22) )
      & ( m1_subset_1(esk2_3(X22,X23,X26),u1_struct_0(X22))
        | r4_lattice3(X22,X23,X26)
        | ~ m1_subset_1(X23,u1_struct_0(X22))
        | v2_struct_0(X22)
        | ~ l3_lattices(X22) )
      & ( r2_hidden(esk2_3(X22,X23,X26),X26)
        | r4_lattice3(X22,X23,X26)
        | ~ m1_subset_1(X23,u1_struct_0(X22))
        | v2_struct_0(X22)
        | ~ l3_lattices(X22) )
      & ( ~ r1_lattices(X22,esk2_3(X22,X23,X26),X23)
        | r4_lattice3(X22,X23,X26)
        | ~ m1_subset_1(X23,u1_struct_0(X22))
        | v2_struct_0(X22)
        | ~ l3_lattices(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_lattice3])])])])])])])).

cnf(c_0_58,plain,
    ( v2_struct_0(X1)
    | r3_lattices(X1,k7_lattices(X1,X3),k7_lattices(X1,X2))
    | ~ v10_lattices(X1)
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r3_lattices(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_59,plain,
    ( r3_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53]),c_0_54])).

cnf(c_0_60,negated_conjecture,
    ( r4_lattice3(esk5_0,esk6_0,esk4_0)
    | r1_lattices(esk5_0,k7_lattices(esk5_0,esk6_0),esk3_3(X1,a_2_0_lattice3(esk4_0,esk5_0),X2))
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_0_lattice3(a_2_0_lattice3(esk4_0,esk5_0),X2))
    | ~ v17_lattices(X2)
    | ~ m1_subset_1(esk3_3(X1,a_2_0_lattice3(esk4_0,esk5_0),X2),u1_struct_0(esk5_0))
    | ~ m1_subset_1(k7_lattices(esk5_0,esk6_0),u1_struct_0(esk5_0))
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(spm,[status(thm)],[c_0_55,c_0_23])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(X1,a_2_0_lattice3(a_2_0_lattice3(X2,esk5_0),esk5_0))
    | X1 != esk3_3(X3,X2,esk5_0)
    | ~ r2_hidden(X3,a_2_0_lattice3(X2,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_21]),c_0_13]),c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_62,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X3)
    | r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_63,plain,
    ( r1_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_64,plain,
    ( r3_lattices(X1,k7_lattices(X1,X2),k7_lattices(X1,X3))
    | v2_struct_0(X1)
    | ~ v17_lattices(X1)
    | ~ r1_lattices(X1,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_65,negated_conjecture,
    ( r4_lattice3(esk5_0,esk6_0,esk4_0)
    | r1_lattices(esk5_0,k7_lattices(esk5_0,esk6_0),k7_lattices(esk5_0,X1))
    | ~ r2_hidden(X1,a_2_0_lattice3(a_2_0_lattice3(esk4_0,esk5_0),esk5_0))
    | ~ m1_subset_1(k7_lattices(esk5_0,esk6_0),u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_24]),c_0_13]),c_0_14]),c_0_15])]),c_0_16]),c_0_34])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(esk3_3(X1,X2,esk5_0),a_2_0_lattice3(a_2_0_lattice3(X2,esk5_0),esk5_0))
    | ~ r2_hidden(X1,a_2_0_lattice3(X2,esk5_0)) ),
    inference(er,[status(thm)],[c_0_61])).

cnf(c_0_67,negated_conjecture,
    ( k7_lattices(esk5_0,k7_lattices(esk5_0,k7_lattices(esk5_0,k7_lattices(esk5_0,esk2_3(X1,X2,X3))))) = k7_lattices(esk5_0,k7_lattices(esk5_0,esk2_3(X1,X2,X3)))
    | r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(esk5_0))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_62])).

cnf(c_0_68,negated_conjecture,
    ( r4_lattice3(X1,X2,X3)
    | m1_subset_1(k7_lattices(esk5_0,k7_lattices(esk5_0,k7_lattices(esk5_0,esk2_3(X1,X2,X3)))),u1_struct_0(esk5_0))
    | v2_struct_0(X1)
    | ~ m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(esk5_0))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_62])).

cnf(c_0_69,plain,
    ( r1_lattices(X1,k7_lattices(X1,X2),k7_lattices(X1,X3))
    | v2_struct_0(X1)
    | ~ v17_lattices(X1)
    | ~ r1_lattices(X1,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_53]),c_0_54]),c_0_52]),c_0_33]),c_0_33])).

cnf(c_0_70,negated_conjecture,
    ( r4_lattice3(esk5_0,esk6_0,esk4_0)
    | r1_lattices(esk5_0,k7_lattices(esk5_0,esk6_0),k7_lattices(esk5_0,esk3_3(X1,esk4_0,esk5_0)))
    | ~ r2_hidden(X1,a_2_0_lattice3(esk4_0,esk5_0))
    | ~ m1_subset_1(k7_lattices(esk5_0,esk6_0),u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_71,negated_conjecture,
    ( m1_subset_1(k7_lattices(esk5_0,esk3_3(X1,X2,esk5_0)),u1_struct_0(esk5_0))
    | ~ r2_hidden(X1,a_2_0_lattice3(X2,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_66])).

cnf(c_0_72,negated_conjecture,
    ( r4_lattice3(X1,X2,X3)
    | r2_hidden(X4,a_2_0_lattice3(X5,esk5_0))
    | v2_struct_0(X1)
    | X4 != k7_lattices(esk5_0,k7_lattices(esk5_0,esk2_3(X1,X2,X3)))
    | ~ r2_hidden(k7_lattices(esk5_0,k7_lattices(esk5_0,k7_lattices(esk5_0,esk2_3(X1,X2,X3)))),X5)
    | ~ m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(esk5_0))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_67]),c_0_13]),c_0_14]),c_0_15])]),c_0_16]),c_0_68])).

cnf(c_0_73,negated_conjecture,
    ( r4_lattice3(esk5_0,esk6_0,esk4_0)
    | r1_lattices(esk5_0,k7_lattices(esk5_0,k7_lattices(esk5_0,esk3_3(X1,esk4_0,esk5_0))),k7_lattices(esk5_0,k7_lattices(esk5_0,esk6_0)))
    | ~ r2_hidden(X1,a_2_0_lattice3(esk4_0,esk5_0))
    | ~ m1_subset_1(k7_lattices(esk5_0,esk6_0),u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_13]),c_0_14]),c_0_15])]),c_0_16]),c_0_71])).

cnf(c_0_74,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_75,negated_conjecture,
    ( r2_hidden(k7_lattices(esk5_0,esk3_3(X1,a_2_0_lattice3(X2,esk5_0),X3)),X2)
    | v2_struct_0(X3)
    | ~ r2_hidden(X1,a_2_0_lattice3(a_2_0_lattice3(X2,esk5_0),X3))
    | ~ v17_lattices(X3)
    | ~ v10_lattices(X3)
    | ~ l3_lattices(X3) ),
    inference(spm,[status(thm)],[c_0_26,c_0_23])).

cnf(c_0_76,negated_conjecture,
    ( r4_lattice3(X1,X2,X3)
    | r2_hidden(X4,a_2_0_lattice3(X5,esk5_0))
    | v2_struct_0(X1)
    | X4 != esk2_3(X1,X2,X3)
    | ~ r2_hidden(k7_lattices(esk5_0,esk2_3(X1,X2,X3)),X5)
    | ~ m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(esk5_0))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_72,c_0_18])).

cnf(c_0_77,negated_conjecture,
    ( r4_lattice3(esk5_0,esk6_0,esk4_0)
    | r1_lattices(esk5_0,k7_lattices(esk5_0,k7_lattices(esk5_0,esk3_3(X1,esk4_0,esk5_0))),esk6_0)
    | ~ r2_hidden(X1,a_2_0_lattice3(esk4_0,esk5_0))
    | ~ m1_subset_1(k7_lattices(esk5_0,esk6_0),u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_18]),c_0_74])])).

cnf(c_0_78,negated_conjecture,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,a_2_0_lattice3(a_2_0_lattice3(X2,esk5_0),esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_19]),c_0_13]),c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_79,negated_conjecture,
    ( r4_lattice3(X1,X2,X3)
    | r2_hidden(X4,a_2_0_lattice3(a_2_0_lattice3(X5,esk5_0),esk5_0))
    | v2_struct_0(X1)
    | X4 != esk2_3(X1,X2,X3)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X5)
    | ~ m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(esk5_0))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_27]),c_0_13]),c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_80,negated_conjecture,
    ( r4_lattice3(esk5_0,esk6_0,esk4_0)
    | r1_lattices(esk5_0,k7_lattices(esk5_0,X1),esk6_0)
    | ~ r2_hidden(X1,a_2_0_lattice3(esk4_0,esk5_0))
    | ~ m1_subset_1(k7_lattices(esk5_0,esk6_0),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_19]),c_0_13]),c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_81,negated_conjecture,
    ( r2_hidden(esk3_3(X1,X2,esk5_0),X2)
    | ~ r2_hidden(X1,a_2_0_lattice3(X2,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_78,c_0_66])).

cnf(c_0_82,negated_conjecture,
    ( r4_lattice3(X1,X2,X3)
    | r2_hidden(X4,a_2_0_lattice3(a_2_0_lattice3(X3,esk5_0),esk5_0))
    | v2_struct_0(X1)
    | X4 != esk2_3(X1,X2,X3)
    | ~ m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(esk5_0))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_79,c_0_62])).

cnf(c_0_83,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X1))
    | r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_84,negated_conjecture,
    ( r4_lattice3(esk5_0,esk6_0,esk4_0)
    | r1_lattices(esk5_0,k7_lattices(esk5_0,esk3_3(X1,a_2_0_lattice3(esk4_0,esk5_0),esk5_0)),esk6_0)
    | ~ r2_hidden(X1,a_2_0_lattice3(a_2_0_lattice3(esk4_0,esk5_0),esk5_0))
    | ~ m1_subset_1(k7_lattices(esk5_0,esk6_0),u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_85,negated_conjecture,
    ( r4_lattice3(esk5_0,X1,X2)
    | r2_hidden(X3,a_2_0_lattice3(a_2_0_lattice3(X2,esk5_0),esk5_0))
    | X3 != esk2_3(esk5_0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_15])]),c_0_16])).

cnf(c_0_86,negated_conjecture,
    ( r4_lattice3(esk5_0,esk6_0,esk4_0)
    | r1_lattices(esk5_0,X1,esk6_0)
    | ~ r2_hidden(X1,a_2_0_lattice3(a_2_0_lattice3(esk4_0,esk5_0),esk5_0))
    | ~ m1_subset_1(k7_lattices(esk5_0,esk6_0),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_19]),c_0_13]),c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_87,negated_conjecture,
    ( r4_lattice3(esk5_0,X1,X2)
    | r2_hidden(esk2_3(esk5_0,X1,X2),a_2_0_lattice3(a_2_0_lattice3(X2,esk5_0),esk5_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(er,[status(thm)],[c_0_85])).

cnf(c_0_88,plain,
    ( r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,esk2_3(X1,X2,X3),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_89,negated_conjecture,
    ( r4_lattice3(esk5_0,esk6_0,esk4_0)
    | r4_lattice3(esk5_0,X1,esk4_0)
    | r1_lattices(esk5_0,esk2_3(esk5_0,X1,esk4_0),esk6_0)
    | ~ m1_subset_1(k7_lattices(esk5_0,esk6_0),u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_90,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X3)
    | r3_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_91,plain,
    ( r1_lattices(X1,X4,X2)
    | v2_struct_0(X1)
    | ~ r4_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_92,negated_conjecture,
    ( r4_lattice3(esk5_0,esk6_0,esk4_0)
    | ~ m1_subset_1(k7_lattices(esk5_0,esk6_0),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_74]),c_0_15])]),c_0_16])).

cnf(c_0_93,plain,
    ( m1_subset_1(X1,u1_struct_0(X2))
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_0_lattice3(X3,X2))
    | ~ v17_lattices(X2)
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_19]),c_0_21])).

cnf(c_0_94,negated_conjecture,
    ( k7_lattices(esk5_0,k7_lattices(esk5_0,k7_lattices(esk5_0,k7_lattices(esk5_0,esk1_3(X1,X2,X3))))) = k7_lattices(esk5_0,k7_lattices(esk5_0,esk1_3(X1,X2,X3)))
    | r3_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(esk5_0))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_90])).

cnf(c_0_95,negated_conjecture,
    ( r3_lattice3(X1,X2,X3)
    | m1_subset_1(k7_lattices(esk5_0,k7_lattices(esk5_0,k7_lattices(esk5_0,esk1_3(X1,X2,X3)))),u1_struct_0(esk5_0))
    | v2_struct_0(X1)
    | ~ m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(esk5_0))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_90])).

cnf(c_0_96,negated_conjecture,
    ( r1_lattices(esk5_0,X1,esk6_0)
    | ~ r2_hidden(X1,esk4_0)
    | ~ m1_subset_1(k7_lattices(esk5_0,esk6_0),u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_74]),c_0_15])]),c_0_16])).

cnf(c_0_97,negated_conjecture,
    ( m1_subset_1(esk3_3(X1,X2,esk5_0),u1_struct_0(esk5_0))
    | ~ r2_hidden(X1,a_2_0_lattice3(X2,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_66]),c_0_13]),c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_98,negated_conjecture,
    ( r2_hidden(X1,a_2_0_lattice3(X2,esk5_0))
    | r3_lattice3(X3,X4,X5)
    | v2_struct_0(X3)
    | X1 != k7_lattices(esk5_0,k7_lattices(esk5_0,esk1_3(X3,X4,X5)))
    | ~ r2_hidden(k7_lattices(esk5_0,k7_lattices(esk5_0,k7_lattices(esk5_0,esk1_3(X3,X4,X5)))),X2)
    | ~ m1_subset_1(esk1_3(X3,X4,X5),u1_struct_0(esk5_0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ l3_lattices(X3) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_94]),c_0_13]),c_0_14]),c_0_15])]),c_0_16]),c_0_95])).

cnf(c_0_99,negated_conjecture,
    ( r1_lattices(esk5_0,esk3_3(X1,esk4_0,esk5_0),esk6_0)
    | ~ r2_hidden(X1,a_2_0_lattice3(esk4_0,esk5_0))
    | ~ m1_subset_1(k7_lattices(esk5_0,esk6_0),u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_81]),c_0_97])).

cnf(c_0_100,negated_conjecture,
    ( r2_hidden(k7_lattices(esk5_0,k7_lattices(esk5_0,esk3_3(X1,a_2_0_lattice3(a_2_0_lattice3(X2,esk5_0),esk5_0),X3))),X2)
    | v2_struct_0(X3)
    | ~ r2_hidden(X1,a_2_0_lattice3(a_2_0_lattice3(a_2_0_lattice3(X2,esk5_0),esk5_0),X3))
    | ~ v17_lattices(X3)
    | ~ v10_lattices(X3)
    | ~ l3_lattices(X3) ),
    inference(spm,[status(thm)],[c_0_26,c_0_75])).

cnf(c_0_101,negated_conjecture,
    ( r2_hidden(X1,a_2_0_lattice3(X2,esk5_0))
    | r3_lattice3(X3,X4,X5)
    | v2_struct_0(X3)
    | X1 != esk1_3(X3,X4,X5)
    | ~ r2_hidden(k7_lattices(esk5_0,esk1_3(X3,X4,X5)),X2)
    | ~ m1_subset_1(esk1_3(X3,X4,X5),u1_struct_0(esk5_0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ l3_lattices(X3) ),
    inference(spm,[status(thm)],[c_0_98,c_0_18])).

cnf(c_0_102,negated_conjecture,
    ( r1_lattices(esk5_0,k7_lattices(esk5_0,esk6_0),k7_lattices(esk5_0,esk3_3(X1,esk4_0,esk5_0)))
    | ~ r2_hidden(X1,a_2_0_lattice3(esk4_0,esk5_0))
    | ~ m1_subset_1(k7_lattices(esk5_0,esk6_0),u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_99]),c_0_13]),c_0_74]),c_0_14]),c_0_15])]),c_0_16]),c_0_97])).

cnf(c_0_103,negated_conjecture,
    ( r2_hidden(k7_lattices(esk5_0,X1),X2)
    | ~ r2_hidden(X1,a_2_0_lattice3(a_2_0_lattice3(a_2_0_lattice3(X2,esk5_0),esk5_0),esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_19]),c_0_13]),c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_104,negated_conjecture,
    ( r2_hidden(X1,a_2_0_lattice3(a_2_0_lattice3(X2,esk5_0),esk5_0))
    | r3_lattice3(X3,X4,X5)
    | v2_struct_0(X3)
    | X1 != esk1_3(X3,X4,X5)
    | ~ r2_hidden(esk1_3(X3,X4,X5),X2)
    | ~ m1_subset_1(esk1_3(X3,X4,X5),u1_struct_0(esk5_0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ l3_lattices(X3) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_27]),c_0_13]),c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_105,negated_conjecture,
    ( r1_lattices(esk5_0,k7_lattices(esk5_0,esk6_0),X1)
    | ~ r2_hidden(X1,a_2_0_lattice3(esk4_0,esk5_0))
    | ~ m1_subset_1(k7_lattices(esk5_0,esk6_0),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_19]),c_0_13]),c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_106,negated_conjecture,
    ( r2_hidden(k7_lattices(esk5_0,esk3_3(X1,a_2_0_lattice3(X2,esk5_0),esk5_0)),X2)
    | ~ r2_hidden(X1,a_2_0_lattice3(a_2_0_lattice3(X2,esk5_0),esk5_0)) ),
    inference(spm,[status(thm)],[c_0_103,c_0_66])).

cnf(c_0_107,negated_conjecture,
    ( r2_hidden(X1,a_2_0_lattice3(a_2_0_lattice3(X2,esk5_0),esk5_0))
    | r3_lattice3(X3,X4,X2)
    | v2_struct_0(X3)
    | X1 != esk1_3(X3,X4,X2)
    | ~ m1_subset_1(esk1_3(X3,X4,X2),u1_struct_0(esk5_0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ l3_lattices(X3) ),
    inference(spm,[status(thm)],[c_0_104,c_0_90])).

cnf(c_0_108,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))
    | r3_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_109,negated_conjecture,
    ( r1_lattices(esk5_0,k7_lattices(esk5_0,esk6_0),k7_lattices(esk5_0,esk3_3(X1,a_2_0_lattice3(a_2_0_lattice3(esk4_0,esk5_0),esk5_0),esk5_0)))
    | ~ r2_hidden(X1,a_2_0_lattice3(a_2_0_lattice3(a_2_0_lattice3(esk4_0,esk5_0),esk5_0),esk5_0))
    | ~ m1_subset_1(k7_lattices(esk5_0,esk6_0),u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_105,c_0_106])).

cnf(c_0_110,negated_conjecture,
    ( r2_hidden(X1,a_2_0_lattice3(a_2_0_lattice3(X2,esk5_0),esk5_0))
    | r3_lattice3(esk5_0,X3,X2)
    | X1 != esk1_3(esk5_0,X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_108]),c_0_15])]),c_0_16])).

cnf(c_0_111,negated_conjecture,
    ( r1_lattices(esk5_0,k7_lattices(esk5_0,esk6_0),X1)
    | ~ r2_hidden(X1,a_2_0_lattice3(a_2_0_lattice3(a_2_0_lattice3(esk4_0,esk5_0),esk5_0),esk5_0))
    | ~ m1_subset_1(k7_lattices(esk5_0,esk6_0),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_19]),c_0_13]),c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_112,negated_conjecture,
    ( r2_hidden(esk1_3(esk5_0,X1,X2),a_2_0_lattice3(a_2_0_lattice3(X2,esk5_0),esk5_0))
    | r3_lattice3(esk5_0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(er,[status(thm)],[c_0_110])).

cnf(c_0_113,plain,
    ( r3_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,esk1_3(X1,X2,X3))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_114,negated_conjecture,
    ( r3_lattice3(esk5_0,X1,a_2_0_lattice3(esk4_0,esk5_0))
    | r1_lattices(esk5_0,k7_lattices(esk5_0,esk6_0),esk1_3(esk5_0,X1,a_2_0_lattice3(esk4_0,esk5_0)))
    | ~ m1_subset_1(k7_lattices(esk5_0,esk6_0),u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_111,c_0_112])).

cnf(c_0_115,negated_conjecture,
    ( ~ r4_lattice3(esk5_0,esk6_0,esk4_0)
    | ~ r3_lattice3(esk5_0,k7_lattices(esk5_0,esk6_0),a_2_0_lattice3(esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_116,negated_conjecture,
    ( r3_lattice3(esk5_0,k7_lattices(esk5_0,esk6_0),a_2_0_lattice3(esk4_0,esk5_0))
    | ~ m1_subset_1(k7_lattices(esk5_0,esk6_0),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_114]),c_0_15])]),c_0_16])).

cnf(c_0_117,negated_conjecture,
    ( ~ m1_subset_1(k7_lattices(esk5_0,esk6_0),u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_116]),c_0_92])).

cnf(c_0_118,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_33]),c_0_74]),c_0_15])]),c_0_16]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n014.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:17:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 40.61/40.87  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 40.61/40.87  # and selection function SelectMaxLComplexAvoidPosPred.
% 40.61/40.87  #
% 40.61/40.87  # Preprocessing time       : 0.030 s
% 40.61/40.87  # Presaturation interreduction done
% 40.61/40.87  
% 40.61/40.87  # Proof found!
% 40.61/40.87  # SZS status Theorem
% 40.61/40.87  # SZS output start CNFRefutation
% 40.61/40.87  fof(t23_lattice3, conjecture, ![X1, X2]:((((~(v2_struct_0(X2))&v10_lattices(X2))&v17_lattices(X2))&l3_lattices(X2))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>(r4_lattice3(X2,X3,X1)<=>r3_lattice3(X2,k7_lattices(X2,X3),a_2_0_lattice3(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_lattice3)).
% 40.61/40.87  fof(t49_lattices, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v17_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>k7_lattices(X1,k7_lattices(X1,X2))=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_lattices)).
% 40.61/40.87  fof(fraenkel_a_2_0_lattice3, axiom, ![X1, X2, X3]:((((~(v2_struct_0(X3))&v10_lattices(X3))&v17_lattices(X3))&l3_lattices(X3))=>(r2_hidden(X1,a_2_0_lattice3(X2,X3))<=>?[X4]:((m1_subset_1(X4,u1_struct_0(X3))&X1=k7_lattices(X3,X4))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_0_lattice3)).
% 40.61/40.87  fof(dt_k7_lattices, axiom, ![X1, X2]:(((~(v2_struct_0(X1))&l3_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>m1_subset_1(k7_lattices(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_lattices)).
% 40.61/40.87  fof(d16_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(r3_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X3)=>r1_lattices(X1,X2,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_lattice3)).
% 40.61/40.87  fof(redefinition_r3_lattices, axiom, ![X1, X2, X3]:(((((((~(v2_struct_0(X1))&v6_lattices(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>(r3_lattices(X1,X2,X3)<=>r1_lattices(X1,X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 40.61/40.87  fof(cc1_lattices, axiom, ![X1]:(l3_lattices(X1)=>((~(v2_struct_0(X1))&v10_lattices(X1))=>((((((~(v2_struct_0(X1))&v4_lattices(X1))&v5_lattices(X1))&v6_lattices(X1))&v7_lattices(X1))&v8_lattices(X1))&v9_lattices(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattices)).
% 40.61/40.87  fof(t53_lattices, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v17_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r3_lattices(X1,X2,X3)=>r3_lattices(X1,k7_lattices(X1,X3),k7_lattices(X1,X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_lattices)).
% 40.61/40.87  fof(d17_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(r4_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X3)=>r1_lattices(X1,X4,X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d17_lattice3)).
% 40.61/40.87  fof(c_0_9, negated_conjecture, ~(![X1, X2]:((((~(v2_struct_0(X2))&v10_lattices(X2))&v17_lattices(X2))&l3_lattices(X2))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>(r4_lattice3(X2,X3,X1)<=>r3_lattice3(X2,k7_lattices(X2,X3),a_2_0_lattice3(X1,X2)))))), inference(assume_negation,[status(cth)],[t23_lattice3])).
% 40.61/40.87  fof(c_0_10, plain, ![X11, X12]:(v2_struct_0(X11)|~v10_lattices(X11)|~v17_lattices(X11)|~l3_lattices(X11)|(~m1_subset_1(X12,u1_struct_0(X11))|k7_lattices(X11,k7_lattices(X11,X12))=X12)), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t49_lattices])])])])).
% 40.61/40.87  fof(c_0_11, negated_conjecture, ((((~v2_struct_0(esk5_0)&v10_lattices(esk5_0))&v17_lattices(esk5_0))&l3_lattices(esk5_0))&(m1_subset_1(esk6_0,u1_struct_0(esk5_0))&((~r4_lattice3(esk5_0,esk6_0,esk4_0)|~r3_lattice3(esk5_0,k7_lattices(esk5_0,esk6_0),a_2_0_lattice3(esk4_0,esk5_0)))&(r4_lattice3(esk5_0,esk6_0,esk4_0)|r3_lattice3(esk5_0,k7_lattices(esk5_0,esk6_0),a_2_0_lattice3(esk4_0,esk5_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).
% 40.61/40.87  cnf(c_0_12, plain, (v2_struct_0(X1)|k7_lattices(X1,k7_lattices(X1,X2))=X2|~v10_lattices(X1)|~v17_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 40.61/40.87  cnf(c_0_13, negated_conjecture, (v17_lattices(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 40.61/40.87  cnf(c_0_14, negated_conjecture, (v10_lattices(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 40.61/40.87  cnf(c_0_15, negated_conjecture, (l3_lattices(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 40.61/40.87  cnf(c_0_16, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 40.61/40.87  fof(c_0_17, plain, ![X28, X29, X30, X32]:((((m1_subset_1(esk3_3(X28,X29,X30),u1_struct_0(X30))|~r2_hidden(X28,a_2_0_lattice3(X29,X30))|(v2_struct_0(X30)|~v10_lattices(X30)|~v17_lattices(X30)|~l3_lattices(X30)))&(X28=k7_lattices(X30,esk3_3(X28,X29,X30))|~r2_hidden(X28,a_2_0_lattice3(X29,X30))|(v2_struct_0(X30)|~v10_lattices(X30)|~v17_lattices(X30)|~l3_lattices(X30))))&(r2_hidden(esk3_3(X28,X29,X30),X29)|~r2_hidden(X28,a_2_0_lattice3(X29,X30))|(v2_struct_0(X30)|~v10_lattices(X30)|~v17_lattices(X30)|~l3_lattices(X30))))&(~m1_subset_1(X32,u1_struct_0(X30))|X28!=k7_lattices(X30,X32)|~r2_hidden(X32,X29)|r2_hidden(X28,a_2_0_lattice3(X29,X30))|(v2_struct_0(X30)|~v10_lattices(X30)|~v17_lattices(X30)|~l3_lattices(X30)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_0_lattice3])])])])])])).
% 40.61/40.87  cnf(c_0_18, negated_conjecture, (k7_lattices(esk5_0,k7_lattices(esk5_0,X1))=X1|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_13]), c_0_14]), c_0_15])]), c_0_16])).
% 40.61/40.87  cnf(c_0_19, plain, (X1=k7_lattices(X2,esk3_3(X1,X3,X2))|v2_struct_0(X2)|~r2_hidden(X1,a_2_0_lattice3(X3,X2))|~v10_lattices(X2)|~v17_lattices(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 40.61/40.87  cnf(c_0_20, negated_conjecture, (esk3_3(X1,X2,esk5_0)=k7_lattices(esk5_0,X1)|~r2_hidden(X1,a_2_0_lattice3(X2,esk5_0))|~m1_subset_1(esk3_3(X1,X2,esk5_0),u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_13]), c_0_14]), c_0_15])]), c_0_16])).
% 40.61/40.87  cnf(c_0_21, plain, (m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X3))|v2_struct_0(X3)|~r2_hidden(X1,a_2_0_lattice3(X2,X3))|~v10_lattices(X3)|~v17_lattices(X3)|~l3_lattices(X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 40.61/40.87  cnf(c_0_22, plain, (r2_hidden(X3,a_2_0_lattice3(X4,X2))|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|X3!=k7_lattices(X2,X1)|~r2_hidden(X1,X4)|~v10_lattices(X2)|~v17_lattices(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 40.61/40.87  cnf(c_0_23, plain, (r2_hidden(esk3_3(X1,X2,X3),X2)|v2_struct_0(X3)|~r2_hidden(X1,a_2_0_lattice3(X2,X3))|~v10_lattices(X3)|~v17_lattices(X3)|~l3_lattices(X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 40.61/40.87  cnf(c_0_24, negated_conjecture, (esk3_3(X1,X2,esk5_0)=k7_lattices(esk5_0,X1)|~r2_hidden(X1,a_2_0_lattice3(X2,esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_13]), c_0_14]), c_0_15])]), c_0_16])).
% 40.61/40.87  cnf(c_0_25, negated_conjecture, (r2_hidden(X1,a_2_0_lattice3(X2,esk5_0))|~r2_hidden(k7_lattices(esk5_0,X1),X2)|~m1_subset_1(k7_lattices(esk5_0,X1),u1_struct_0(esk5_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(er,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_18]), c_0_13]), c_0_14]), c_0_15])]), c_0_16])])).
% 40.61/40.87  cnf(c_0_26, negated_conjecture, (r2_hidden(k7_lattices(esk5_0,X1),X2)|~r2_hidden(X1,a_2_0_lattice3(X2,esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_13]), c_0_14]), c_0_15])]), c_0_16])).
% 40.61/40.87  cnf(c_0_27, plain, (r2_hidden(k7_lattices(X1,X2),a_2_0_lattice3(X3,X1))|v2_struct_0(X1)|~r2_hidden(X2,X3)|~v17_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(er,[status(thm)],[c_0_22])).
% 40.61/40.87  cnf(c_0_28, negated_conjecture, (r2_hidden(k7_lattices(esk5_0,X1),a_2_0_lattice3(X2,esk5_0))|~r2_hidden(X1,X2)|~m1_subset_1(k7_lattices(esk5_0,X1),u1_struct_0(esk5_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_25, c_0_18])).
% 40.61/40.87  fof(c_0_29, plain, ![X6, X7]:(v2_struct_0(X6)|~l3_lattices(X6)|~m1_subset_1(X7,u1_struct_0(X6))|m1_subset_1(k7_lattices(X6,X7),u1_struct_0(X6))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_lattices])])])).
% 40.61/40.87  cnf(c_0_30, negated_conjecture, (k7_lattices(esk5_0,k7_lattices(esk5_0,X1))=X1|~r2_hidden(X1,a_2_0_lattice3(X2,esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_24]), c_0_13]), c_0_14]), c_0_15])]), c_0_16])).
% 40.61/40.87  cnf(c_0_31, negated_conjecture, (r2_hidden(k7_lattices(esk5_0,k7_lattices(esk5_0,X1)),X2)|~r2_hidden(X1,X2)|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_13]), c_0_14]), c_0_15])]), c_0_16])).
% 40.61/40.87  cnf(c_0_32, negated_conjecture, (r2_hidden(X1,a_2_0_lattice3(a_2_0_lattice3(X2,esk5_0),esk5_0))|~r2_hidden(X1,X2)|~m1_subset_1(k7_lattices(esk5_0,X1),u1_struct_0(esk5_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_25, c_0_28])).
% 40.61/40.87  cnf(c_0_33, plain, (v2_struct_0(X1)|m1_subset_1(k7_lattices(X1,X2),u1_struct_0(X1))|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 40.61/40.87  cnf(c_0_34, negated_conjecture, (m1_subset_1(k7_lattices(esk5_0,X1),u1_struct_0(esk5_0))|~r2_hidden(X1,a_2_0_lattice3(X2,esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_24]), c_0_13]), c_0_14]), c_0_15])]), c_0_16])).
% 40.61/40.87  cnf(c_0_35, negated_conjecture, (k7_lattices(esk5_0,k7_lattices(esk5_0,k7_lattices(esk5_0,k7_lattices(esk5_0,X1))))=k7_lattices(esk5_0,k7_lattices(esk5_0,X1))|~r2_hidden(X1,a_2_0_lattice3(X2,esk5_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 40.61/40.87  cnf(c_0_36, negated_conjecture, (r2_hidden(X1,a_2_0_lattice3(a_2_0_lattice3(X2,esk5_0),esk5_0))|~r2_hidden(X1,X2)|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_15])]), c_0_16])).
% 40.61/40.87  cnf(c_0_37, negated_conjecture, (m1_subset_1(k7_lattices(esk5_0,k7_lattices(esk5_0,k7_lattices(esk5_0,X1))),u1_struct_0(esk5_0))|~r2_hidden(X1,a_2_0_lattice3(X2,esk5_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_34, c_0_31])).
% 40.61/40.87  cnf(c_0_38, negated_conjecture, (k7_lattices(esk5_0,k7_lattices(esk5_0,k7_lattices(esk5_0,k7_lattices(esk5_0,X1))))=k7_lattices(esk5_0,k7_lattices(esk5_0,X1))|~r2_hidden(X1,X2)|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 40.61/40.87  cnf(c_0_39, negated_conjecture, (m1_subset_1(k7_lattices(esk5_0,k7_lattices(esk5_0,k7_lattices(esk5_0,X1))),u1_struct_0(esk5_0))|~r2_hidden(X1,X2)|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_37, c_0_36])).
% 40.61/40.87  cnf(c_0_40, negated_conjecture, (k7_lattices(esk5_0,k7_lattices(esk5_0,k7_lattices(esk5_0,k7_lattices(esk5_0,esk3_3(X1,X2,X3)))))=k7_lattices(esk5_0,k7_lattices(esk5_0,esk3_3(X1,X2,X3)))|v2_struct_0(X3)|~r2_hidden(X1,a_2_0_lattice3(X2,X3))|~v17_lattices(X3)|~m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(esk5_0))|~v10_lattices(X3)|~l3_lattices(X3)), inference(spm,[status(thm)],[c_0_38, c_0_23])).
% 40.61/40.87  cnf(c_0_41, negated_conjecture, (m1_subset_1(k7_lattices(esk5_0,k7_lattices(esk5_0,k7_lattices(esk5_0,esk3_3(X1,X2,X3)))),u1_struct_0(esk5_0))|v2_struct_0(X3)|~r2_hidden(X1,a_2_0_lattice3(X2,X3))|~v17_lattices(X3)|~m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(esk5_0))|~v10_lattices(X3)|~l3_lattices(X3)), inference(spm,[status(thm)],[c_0_39, c_0_23])).
% 40.61/40.87  cnf(c_0_42, negated_conjecture, (r2_hidden(X1,a_2_0_lattice3(X2,esk5_0))|v2_struct_0(X3)|X1!=k7_lattices(esk5_0,k7_lattices(esk5_0,esk3_3(X4,X5,X3)))|~r2_hidden(k7_lattices(esk5_0,k7_lattices(esk5_0,k7_lattices(esk5_0,esk3_3(X4,X5,X3)))),X2)|~r2_hidden(X4,a_2_0_lattice3(X5,X3))|~v17_lattices(X3)|~m1_subset_1(esk3_3(X4,X5,X3),u1_struct_0(esk5_0))|~v10_lattices(X3)|~l3_lattices(X3)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_40]), c_0_13]), c_0_14]), c_0_15])]), c_0_16]), c_0_41])).
% 40.61/40.87  fof(c_0_43, plain, ![X16, X17, X18, X19, X20]:((~r3_lattice3(X16,X17,X18)|(~m1_subset_1(X19,u1_struct_0(X16))|(~r2_hidden(X19,X18)|r1_lattices(X16,X17,X19)))|~m1_subset_1(X17,u1_struct_0(X16))|(v2_struct_0(X16)|~l3_lattices(X16)))&((m1_subset_1(esk1_3(X16,X17,X20),u1_struct_0(X16))|r3_lattice3(X16,X17,X20)|~m1_subset_1(X17,u1_struct_0(X16))|(v2_struct_0(X16)|~l3_lattices(X16)))&((r2_hidden(esk1_3(X16,X17,X20),X20)|r3_lattice3(X16,X17,X20)|~m1_subset_1(X17,u1_struct_0(X16))|(v2_struct_0(X16)|~l3_lattices(X16)))&(~r1_lattices(X16,X17,esk1_3(X16,X17,X20))|r3_lattice3(X16,X17,X20)|~m1_subset_1(X17,u1_struct_0(X16))|(v2_struct_0(X16)|~l3_lattices(X16)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattice3])])])])])])])).
% 40.61/40.87  cnf(c_0_44, negated_conjecture, (r2_hidden(X1,a_2_0_lattice3(X2,esk5_0))|v2_struct_0(X3)|X1!=esk3_3(X4,X5,X3)|~r2_hidden(k7_lattices(esk5_0,esk3_3(X4,X5,X3)),X2)|~r2_hidden(X4,a_2_0_lattice3(X5,X3))|~v17_lattices(X3)|~m1_subset_1(esk3_3(X4,X5,X3),u1_struct_0(esk5_0))|~v10_lattices(X3)|~l3_lattices(X3)), inference(spm,[status(thm)],[c_0_42, c_0_18])).
% 40.61/40.87  fof(c_0_45, plain, ![X8, X9, X10]:((~r3_lattices(X8,X9,X10)|r1_lattices(X8,X9,X10)|(v2_struct_0(X8)|~v6_lattices(X8)|~v8_lattices(X8)|~v9_lattices(X8)|~l3_lattices(X8)|~m1_subset_1(X9,u1_struct_0(X8))|~m1_subset_1(X10,u1_struct_0(X8))))&(~r1_lattices(X8,X9,X10)|r3_lattices(X8,X9,X10)|(v2_struct_0(X8)|~v6_lattices(X8)|~v8_lattices(X8)|~v9_lattices(X8)|~l3_lattices(X8)|~m1_subset_1(X9,u1_struct_0(X8))|~m1_subset_1(X10,u1_struct_0(X8))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).
% 40.61/40.87  fof(c_0_46, plain, ![X5]:(((((((~v2_struct_0(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5))&(v4_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v5_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v6_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v7_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v8_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v9_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).
% 40.61/40.87  cnf(c_0_47, plain, (r1_lattices(X1,X2,X4)|v2_struct_0(X1)|~r3_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X4,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 40.61/40.87  cnf(c_0_48, negated_conjecture, (r4_lattice3(esk5_0,esk6_0,esk4_0)|r3_lattice3(esk5_0,k7_lattices(esk5_0,esk6_0),a_2_0_lattice3(esk4_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 40.61/40.87  cnf(c_0_49, negated_conjecture, (r2_hidden(X1,a_2_0_lattice3(a_2_0_lattice3(X2,esk5_0),esk5_0))|v2_struct_0(X3)|X1!=esk3_3(X4,X5,X3)|~r2_hidden(esk3_3(X4,X5,X3),X2)|~r2_hidden(X4,a_2_0_lattice3(X5,X3))|~v17_lattices(X3)|~m1_subset_1(esk3_3(X4,X5,X3),u1_struct_0(esk5_0))|~v10_lattices(X3)|~l3_lattices(X3)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_27]), c_0_13]), c_0_14]), c_0_15])]), c_0_16])).
% 40.61/40.87  fof(c_0_50, plain, ![X13, X14, X15]:(v2_struct_0(X13)|~v10_lattices(X13)|~v17_lattices(X13)|~l3_lattices(X13)|(~m1_subset_1(X14,u1_struct_0(X13))|(~m1_subset_1(X15,u1_struct_0(X13))|(~r3_lattices(X13,X14,X15)|r3_lattices(X13,k7_lattices(X13,X15),k7_lattices(X13,X14)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t53_lattices])])])])).
% 40.61/40.87  cnf(c_0_51, plain, (r3_lattices(X1,X2,X3)|v2_struct_0(X1)|~r1_lattices(X1,X2,X3)|~v6_lattices(X1)|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 40.61/40.87  cnf(c_0_52, plain, (v9_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 40.61/40.87  cnf(c_0_53, plain, (v6_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 40.61/40.87  cnf(c_0_54, plain, (v8_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 40.61/40.87  cnf(c_0_55, negated_conjecture, (r4_lattice3(esk5_0,esk6_0,esk4_0)|r1_lattices(esk5_0,k7_lattices(esk5_0,esk6_0),X1)|~r2_hidden(X1,a_2_0_lattice3(esk4_0,esk5_0))|~m1_subset_1(k7_lattices(esk5_0,esk6_0),u1_struct_0(esk5_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_15])]), c_0_16])).
% 40.61/40.87  cnf(c_0_56, negated_conjecture, (r2_hidden(X1,a_2_0_lattice3(a_2_0_lattice3(X2,esk5_0),esk5_0))|v2_struct_0(X3)|X1!=esk3_3(X4,X2,X3)|~r2_hidden(X4,a_2_0_lattice3(X2,X3))|~v17_lattices(X3)|~m1_subset_1(esk3_3(X4,X2,X3),u1_struct_0(esk5_0))|~v10_lattices(X3)|~l3_lattices(X3)), inference(spm,[status(thm)],[c_0_49, c_0_23])).
% 40.61/40.87  fof(c_0_57, plain, ![X22, X23, X24, X25, X26]:((~r4_lattice3(X22,X23,X24)|(~m1_subset_1(X25,u1_struct_0(X22))|(~r2_hidden(X25,X24)|r1_lattices(X22,X25,X23)))|~m1_subset_1(X23,u1_struct_0(X22))|(v2_struct_0(X22)|~l3_lattices(X22)))&((m1_subset_1(esk2_3(X22,X23,X26),u1_struct_0(X22))|r4_lattice3(X22,X23,X26)|~m1_subset_1(X23,u1_struct_0(X22))|(v2_struct_0(X22)|~l3_lattices(X22)))&((r2_hidden(esk2_3(X22,X23,X26),X26)|r4_lattice3(X22,X23,X26)|~m1_subset_1(X23,u1_struct_0(X22))|(v2_struct_0(X22)|~l3_lattices(X22)))&(~r1_lattices(X22,esk2_3(X22,X23,X26),X23)|r4_lattice3(X22,X23,X26)|~m1_subset_1(X23,u1_struct_0(X22))|(v2_struct_0(X22)|~l3_lattices(X22)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_lattice3])])])])])])])).
% 40.61/40.87  cnf(c_0_58, plain, (v2_struct_0(X1)|r3_lattices(X1,k7_lattices(X1,X3),k7_lattices(X1,X2))|~v10_lattices(X1)|~v17_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~r3_lattices(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 40.61/40.87  cnf(c_0_59, plain, (r3_lattices(X1,X2,X3)|v2_struct_0(X1)|~r1_lattices(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53]), c_0_54])).
% 40.61/40.87  cnf(c_0_60, negated_conjecture, (r4_lattice3(esk5_0,esk6_0,esk4_0)|r1_lattices(esk5_0,k7_lattices(esk5_0,esk6_0),esk3_3(X1,a_2_0_lattice3(esk4_0,esk5_0),X2))|v2_struct_0(X2)|~r2_hidden(X1,a_2_0_lattice3(a_2_0_lattice3(esk4_0,esk5_0),X2))|~v17_lattices(X2)|~m1_subset_1(esk3_3(X1,a_2_0_lattice3(esk4_0,esk5_0),X2),u1_struct_0(esk5_0))|~m1_subset_1(k7_lattices(esk5_0,esk6_0),u1_struct_0(esk5_0))|~v10_lattices(X2)|~l3_lattices(X2)), inference(spm,[status(thm)],[c_0_55, c_0_23])).
% 40.61/40.87  cnf(c_0_61, negated_conjecture, (r2_hidden(X1,a_2_0_lattice3(a_2_0_lattice3(X2,esk5_0),esk5_0))|X1!=esk3_3(X3,X2,esk5_0)|~r2_hidden(X3,a_2_0_lattice3(X2,esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_21]), c_0_13]), c_0_14]), c_0_15])]), c_0_16])).
% 40.61/40.87  cnf(c_0_62, plain, (r2_hidden(esk2_3(X1,X2,X3),X3)|r4_lattice3(X1,X2,X3)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 40.61/40.87  cnf(c_0_63, plain, (r1_lattices(X1,X2,X3)|v2_struct_0(X1)|~r3_lattices(X1,X2,X3)|~v6_lattices(X1)|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 40.61/40.87  cnf(c_0_64, plain, (r3_lattices(X1,k7_lattices(X1,X2),k7_lattices(X1,X3))|v2_struct_0(X1)|~v17_lattices(X1)|~r1_lattices(X1,X3,X2)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 40.61/40.87  cnf(c_0_65, negated_conjecture, (r4_lattice3(esk5_0,esk6_0,esk4_0)|r1_lattices(esk5_0,k7_lattices(esk5_0,esk6_0),k7_lattices(esk5_0,X1))|~r2_hidden(X1,a_2_0_lattice3(a_2_0_lattice3(esk4_0,esk5_0),esk5_0))|~m1_subset_1(k7_lattices(esk5_0,esk6_0),u1_struct_0(esk5_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_24]), c_0_13]), c_0_14]), c_0_15])]), c_0_16]), c_0_34])).
% 40.61/40.87  cnf(c_0_66, negated_conjecture, (r2_hidden(esk3_3(X1,X2,esk5_0),a_2_0_lattice3(a_2_0_lattice3(X2,esk5_0),esk5_0))|~r2_hidden(X1,a_2_0_lattice3(X2,esk5_0))), inference(er,[status(thm)],[c_0_61])).
% 40.61/40.87  cnf(c_0_67, negated_conjecture, (k7_lattices(esk5_0,k7_lattices(esk5_0,k7_lattices(esk5_0,k7_lattices(esk5_0,esk2_3(X1,X2,X3)))))=k7_lattices(esk5_0,k7_lattices(esk5_0,esk2_3(X1,X2,X3)))|r4_lattice3(X1,X2,X3)|v2_struct_0(X1)|~m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(esk5_0))|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_38, c_0_62])).
% 40.61/40.87  cnf(c_0_68, negated_conjecture, (r4_lattice3(X1,X2,X3)|m1_subset_1(k7_lattices(esk5_0,k7_lattices(esk5_0,k7_lattices(esk5_0,esk2_3(X1,X2,X3)))),u1_struct_0(esk5_0))|v2_struct_0(X1)|~m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(esk5_0))|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_39, c_0_62])).
% 40.61/40.87  cnf(c_0_69, plain, (r1_lattices(X1,k7_lattices(X1,X2),k7_lattices(X1,X3))|v2_struct_0(X1)|~v17_lattices(X1)|~r1_lattices(X1,X3,X2)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_53]), c_0_54]), c_0_52]), c_0_33]), c_0_33])).
% 40.61/40.87  cnf(c_0_70, negated_conjecture, (r4_lattice3(esk5_0,esk6_0,esk4_0)|r1_lattices(esk5_0,k7_lattices(esk5_0,esk6_0),k7_lattices(esk5_0,esk3_3(X1,esk4_0,esk5_0)))|~r2_hidden(X1,a_2_0_lattice3(esk4_0,esk5_0))|~m1_subset_1(k7_lattices(esk5_0,esk6_0),u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 40.61/40.87  cnf(c_0_71, negated_conjecture, (m1_subset_1(k7_lattices(esk5_0,esk3_3(X1,X2,esk5_0)),u1_struct_0(esk5_0))|~r2_hidden(X1,a_2_0_lattice3(X2,esk5_0))), inference(spm,[status(thm)],[c_0_34, c_0_66])).
% 40.61/40.87  cnf(c_0_72, negated_conjecture, (r4_lattice3(X1,X2,X3)|r2_hidden(X4,a_2_0_lattice3(X5,esk5_0))|v2_struct_0(X1)|X4!=k7_lattices(esk5_0,k7_lattices(esk5_0,esk2_3(X1,X2,X3)))|~r2_hidden(k7_lattices(esk5_0,k7_lattices(esk5_0,k7_lattices(esk5_0,esk2_3(X1,X2,X3)))),X5)|~m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(esk5_0))|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_67]), c_0_13]), c_0_14]), c_0_15])]), c_0_16]), c_0_68])).
% 40.61/40.87  cnf(c_0_73, negated_conjecture, (r4_lattice3(esk5_0,esk6_0,esk4_0)|r1_lattices(esk5_0,k7_lattices(esk5_0,k7_lattices(esk5_0,esk3_3(X1,esk4_0,esk5_0))),k7_lattices(esk5_0,k7_lattices(esk5_0,esk6_0)))|~r2_hidden(X1,a_2_0_lattice3(esk4_0,esk5_0))|~m1_subset_1(k7_lattices(esk5_0,esk6_0),u1_struct_0(esk5_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_13]), c_0_14]), c_0_15])]), c_0_16]), c_0_71])).
% 40.61/40.87  cnf(c_0_74, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 40.61/40.87  cnf(c_0_75, negated_conjecture, (r2_hidden(k7_lattices(esk5_0,esk3_3(X1,a_2_0_lattice3(X2,esk5_0),X3)),X2)|v2_struct_0(X3)|~r2_hidden(X1,a_2_0_lattice3(a_2_0_lattice3(X2,esk5_0),X3))|~v17_lattices(X3)|~v10_lattices(X3)|~l3_lattices(X3)), inference(spm,[status(thm)],[c_0_26, c_0_23])).
% 40.61/40.87  cnf(c_0_76, negated_conjecture, (r4_lattice3(X1,X2,X3)|r2_hidden(X4,a_2_0_lattice3(X5,esk5_0))|v2_struct_0(X1)|X4!=esk2_3(X1,X2,X3)|~r2_hidden(k7_lattices(esk5_0,esk2_3(X1,X2,X3)),X5)|~m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(esk5_0))|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_72, c_0_18])).
% 40.61/40.87  cnf(c_0_77, negated_conjecture, (r4_lattice3(esk5_0,esk6_0,esk4_0)|r1_lattices(esk5_0,k7_lattices(esk5_0,k7_lattices(esk5_0,esk3_3(X1,esk4_0,esk5_0))),esk6_0)|~r2_hidden(X1,a_2_0_lattice3(esk4_0,esk5_0))|~m1_subset_1(k7_lattices(esk5_0,esk6_0),u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_18]), c_0_74])])).
% 40.61/40.87  cnf(c_0_78, negated_conjecture, (r2_hidden(X1,X2)|~r2_hidden(X1,a_2_0_lattice3(a_2_0_lattice3(X2,esk5_0),esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_19]), c_0_13]), c_0_14]), c_0_15])]), c_0_16])).
% 40.61/40.87  cnf(c_0_79, negated_conjecture, (r4_lattice3(X1,X2,X3)|r2_hidden(X4,a_2_0_lattice3(a_2_0_lattice3(X5,esk5_0),esk5_0))|v2_struct_0(X1)|X4!=esk2_3(X1,X2,X3)|~r2_hidden(esk2_3(X1,X2,X3),X5)|~m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(esk5_0))|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_27]), c_0_13]), c_0_14]), c_0_15])]), c_0_16])).
% 40.61/40.87  cnf(c_0_80, negated_conjecture, (r4_lattice3(esk5_0,esk6_0,esk4_0)|r1_lattices(esk5_0,k7_lattices(esk5_0,X1),esk6_0)|~r2_hidden(X1,a_2_0_lattice3(esk4_0,esk5_0))|~m1_subset_1(k7_lattices(esk5_0,esk6_0),u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_19]), c_0_13]), c_0_14]), c_0_15])]), c_0_16])).
% 40.61/40.87  cnf(c_0_81, negated_conjecture, (r2_hidden(esk3_3(X1,X2,esk5_0),X2)|~r2_hidden(X1,a_2_0_lattice3(X2,esk5_0))), inference(spm,[status(thm)],[c_0_78, c_0_66])).
% 40.61/40.87  cnf(c_0_82, negated_conjecture, (r4_lattice3(X1,X2,X3)|r2_hidden(X4,a_2_0_lattice3(a_2_0_lattice3(X3,esk5_0),esk5_0))|v2_struct_0(X1)|X4!=esk2_3(X1,X2,X3)|~m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(esk5_0))|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_79, c_0_62])).
% 40.61/40.87  cnf(c_0_83, plain, (m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X1))|r4_lattice3(X1,X2,X3)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 40.61/40.87  cnf(c_0_84, negated_conjecture, (r4_lattice3(esk5_0,esk6_0,esk4_0)|r1_lattices(esk5_0,k7_lattices(esk5_0,esk3_3(X1,a_2_0_lattice3(esk4_0,esk5_0),esk5_0)),esk6_0)|~r2_hidden(X1,a_2_0_lattice3(a_2_0_lattice3(esk4_0,esk5_0),esk5_0))|~m1_subset_1(k7_lattices(esk5_0,esk6_0),u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 40.61/40.87  cnf(c_0_85, negated_conjecture, (r4_lattice3(esk5_0,X1,X2)|r2_hidden(X3,a_2_0_lattice3(a_2_0_lattice3(X2,esk5_0),esk5_0))|X3!=esk2_3(esk5_0,X1,X2)|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_15])]), c_0_16])).
% 40.61/40.87  cnf(c_0_86, negated_conjecture, (r4_lattice3(esk5_0,esk6_0,esk4_0)|r1_lattices(esk5_0,X1,esk6_0)|~r2_hidden(X1,a_2_0_lattice3(a_2_0_lattice3(esk4_0,esk5_0),esk5_0))|~m1_subset_1(k7_lattices(esk5_0,esk6_0),u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_19]), c_0_13]), c_0_14]), c_0_15])]), c_0_16])).
% 40.61/40.87  cnf(c_0_87, negated_conjecture, (r4_lattice3(esk5_0,X1,X2)|r2_hidden(esk2_3(esk5_0,X1,X2),a_2_0_lattice3(a_2_0_lattice3(X2,esk5_0),esk5_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(er,[status(thm)],[c_0_85])).
% 40.61/40.87  cnf(c_0_88, plain, (r4_lattice3(X1,X2,X3)|v2_struct_0(X1)|~r1_lattices(X1,esk2_3(X1,X2,X3),X2)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 40.61/40.87  cnf(c_0_89, negated_conjecture, (r4_lattice3(esk5_0,esk6_0,esk4_0)|r4_lattice3(esk5_0,X1,esk4_0)|r1_lattices(esk5_0,esk2_3(esk5_0,X1,esk4_0),esk6_0)|~m1_subset_1(k7_lattices(esk5_0,esk6_0),u1_struct_0(esk5_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_86, c_0_87])).
% 40.61/40.87  cnf(c_0_90, plain, (r2_hidden(esk1_3(X1,X2,X3),X3)|r3_lattice3(X1,X2,X3)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 40.61/40.87  cnf(c_0_91, plain, (r1_lattices(X1,X4,X2)|v2_struct_0(X1)|~r4_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X4,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 40.61/40.87  cnf(c_0_92, negated_conjecture, (r4_lattice3(esk5_0,esk6_0,esk4_0)|~m1_subset_1(k7_lattices(esk5_0,esk6_0),u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_89]), c_0_74]), c_0_15])]), c_0_16])).
% 40.61/40.87  cnf(c_0_93, plain, (m1_subset_1(X1,u1_struct_0(X2))|v2_struct_0(X2)|~r2_hidden(X1,a_2_0_lattice3(X3,X2))|~v17_lattices(X2)|~v10_lattices(X2)|~l3_lattices(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_19]), c_0_21])).
% 40.61/40.87  cnf(c_0_94, negated_conjecture, (k7_lattices(esk5_0,k7_lattices(esk5_0,k7_lattices(esk5_0,k7_lattices(esk5_0,esk1_3(X1,X2,X3)))))=k7_lattices(esk5_0,k7_lattices(esk5_0,esk1_3(X1,X2,X3)))|r3_lattice3(X1,X2,X3)|v2_struct_0(X1)|~m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(esk5_0))|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_38, c_0_90])).
% 40.61/40.87  cnf(c_0_95, negated_conjecture, (r3_lattice3(X1,X2,X3)|m1_subset_1(k7_lattices(esk5_0,k7_lattices(esk5_0,k7_lattices(esk5_0,esk1_3(X1,X2,X3)))),u1_struct_0(esk5_0))|v2_struct_0(X1)|~m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(esk5_0))|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_39, c_0_90])).
% 40.61/40.87  cnf(c_0_96, negated_conjecture, (r1_lattices(esk5_0,X1,esk6_0)|~r2_hidden(X1,esk4_0)|~m1_subset_1(k7_lattices(esk5_0,esk6_0),u1_struct_0(esk5_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_74]), c_0_15])]), c_0_16])).
% 40.61/40.87  cnf(c_0_97, negated_conjecture, (m1_subset_1(esk3_3(X1,X2,esk5_0),u1_struct_0(esk5_0))|~r2_hidden(X1,a_2_0_lattice3(X2,esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_66]), c_0_13]), c_0_14]), c_0_15])]), c_0_16])).
% 40.61/40.87  cnf(c_0_98, negated_conjecture, (r2_hidden(X1,a_2_0_lattice3(X2,esk5_0))|r3_lattice3(X3,X4,X5)|v2_struct_0(X3)|X1!=k7_lattices(esk5_0,k7_lattices(esk5_0,esk1_3(X3,X4,X5)))|~r2_hidden(k7_lattices(esk5_0,k7_lattices(esk5_0,k7_lattices(esk5_0,esk1_3(X3,X4,X5)))),X2)|~m1_subset_1(esk1_3(X3,X4,X5),u1_struct_0(esk5_0))|~m1_subset_1(X4,u1_struct_0(X3))|~l3_lattices(X3)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_94]), c_0_13]), c_0_14]), c_0_15])]), c_0_16]), c_0_95])).
% 40.61/40.87  cnf(c_0_99, negated_conjecture, (r1_lattices(esk5_0,esk3_3(X1,esk4_0,esk5_0),esk6_0)|~r2_hidden(X1,a_2_0_lattice3(esk4_0,esk5_0))|~m1_subset_1(k7_lattices(esk5_0,esk6_0),u1_struct_0(esk5_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_81]), c_0_97])).
% 40.61/40.87  cnf(c_0_100, negated_conjecture, (r2_hidden(k7_lattices(esk5_0,k7_lattices(esk5_0,esk3_3(X1,a_2_0_lattice3(a_2_0_lattice3(X2,esk5_0),esk5_0),X3))),X2)|v2_struct_0(X3)|~r2_hidden(X1,a_2_0_lattice3(a_2_0_lattice3(a_2_0_lattice3(X2,esk5_0),esk5_0),X3))|~v17_lattices(X3)|~v10_lattices(X3)|~l3_lattices(X3)), inference(spm,[status(thm)],[c_0_26, c_0_75])).
% 40.61/40.87  cnf(c_0_101, negated_conjecture, (r2_hidden(X1,a_2_0_lattice3(X2,esk5_0))|r3_lattice3(X3,X4,X5)|v2_struct_0(X3)|X1!=esk1_3(X3,X4,X5)|~r2_hidden(k7_lattices(esk5_0,esk1_3(X3,X4,X5)),X2)|~m1_subset_1(esk1_3(X3,X4,X5),u1_struct_0(esk5_0))|~m1_subset_1(X4,u1_struct_0(X3))|~l3_lattices(X3)), inference(spm,[status(thm)],[c_0_98, c_0_18])).
% 40.61/40.87  cnf(c_0_102, negated_conjecture, (r1_lattices(esk5_0,k7_lattices(esk5_0,esk6_0),k7_lattices(esk5_0,esk3_3(X1,esk4_0,esk5_0)))|~r2_hidden(X1,a_2_0_lattice3(esk4_0,esk5_0))|~m1_subset_1(k7_lattices(esk5_0,esk6_0),u1_struct_0(esk5_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_99]), c_0_13]), c_0_74]), c_0_14]), c_0_15])]), c_0_16]), c_0_97])).
% 40.61/40.87  cnf(c_0_103, negated_conjecture, (r2_hidden(k7_lattices(esk5_0,X1),X2)|~r2_hidden(X1,a_2_0_lattice3(a_2_0_lattice3(a_2_0_lattice3(X2,esk5_0),esk5_0),esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_19]), c_0_13]), c_0_14]), c_0_15])]), c_0_16])).
% 40.61/40.87  cnf(c_0_104, negated_conjecture, (r2_hidden(X1,a_2_0_lattice3(a_2_0_lattice3(X2,esk5_0),esk5_0))|r3_lattice3(X3,X4,X5)|v2_struct_0(X3)|X1!=esk1_3(X3,X4,X5)|~r2_hidden(esk1_3(X3,X4,X5),X2)|~m1_subset_1(esk1_3(X3,X4,X5),u1_struct_0(esk5_0))|~m1_subset_1(X4,u1_struct_0(X3))|~l3_lattices(X3)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_27]), c_0_13]), c_0_14]), c_0_15])]), c_0_16])).
% 40.61/40.87  cnf(c_0_105, negated_conjecture, (r1_lattices(esk5_0,k7_lattices(esk5_0,esk6_0),X1)|~r2_hidden(X1,a_2_0_lattice3(esk4_0,esk5_0))|~m1_subset_1(k7_lattices(esk5_0,esk6_0),u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_19]), c_0_13]), c_0_14]), c_0_15])]), c_0_16])).
% 40.61/40.87  cnf(c_0_106, negated_conjecture, (r2_hidden(k7_lattices(esk5_0,esk3_3(X1,a_2_0_lattice3(X2,esk5_0),esk5_0)),X2)|~r2_hidden(X1,a_2_0_lattice3(a_2_0_lattice3(X2,esk5_0),esk5_0))), inference(spm,[status(thm)],[c_0_103, c_0_66])).
% 40.61/40.87  cnf(c_0_107, negated_conjecture, (r2_hidden(X1,a_2_0_lattice3(a_2_0_lattice3(X2,esk5_0),esk5_0))|r3_lattice3(X3,X4,X2)|v2_struct_0(X3)|X1!=esk1_3(X3,X4,X2)|~m1_subset_1(esk1_3(X3,X4,X2),u1_struct_0(esk5_0))|~m1_subset_1(X4,u1_struct_0(X3))|~l3_lattices(X3)), inference(spm,[status(thm)],[c_0_104, c_0_90])).
% 40.61/40.87  cnf(c_0_108, plain, (m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))|r3_lattice3(X1,X2,X3)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 40.61/40.87  cnf(c_0_109, negated_conjecture, (r1_lattices(esk5_0,k7_lattices(esk5_0,esk6_0),k7_lattices(esk5_0,esk3_3(X1,a_2_0_lattice3(a_2_0_lattice3(esk4_0,esk5_0),esk5_0),esk5_0)))|~r2_hidden(X1,a_2_0_lattice3(a_2_0_lattice3(a_2_0_lattice3(esk4_0,esk5_0),esk5_0),esk5_0))|~m1_subset_1(k7_lattices(esk5_0,esk6_0),u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_105, c_0_106])).
% 40.61/40.87  cnf(c_0_110, negated_conjecture, (r2_hidden(X1,a_2_0_lattice3(a_2_0_lattice3(X2,esk5_0),esk5_0))|r3_lattice3(esk5_0,X3,X2)|X1!=esk1_3(esk5_0,X3,X2)|~m1_subset_1(X3,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_108]), c_0_15])]), c_0_16])).
% 40.61/40.87  cnf(c_0_111, negated_conjecture, (r1_lattices(esk5_0,k7_lattices(esk5_0,esk6_0),X1)|~r2_hidden(X1,a_2_0_lattice3(a_2_0_lattice3(a_2_0_lattice3(esk4_0,esk5_0),esk5_0),esk5_0))|~m1_subset_1(k7_lattices(esk5_0,esk6_0),u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_19]), c_0_13]), c_0_14]), c_0_15])]), c_0_16])).
% 40.61/40.87  cnf(c_0_112, negated_conjecture, (r2_hidden(esk1_3(esk5_0,X1,X2),a_2_0_lattice3(a_2_0_lattice3(X2,esk5_0),esk5_0))|r3_lattice3(esk5_0,X1,X2)|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(er,[status(thm)],[c_0_110])).
% 40.61/40.87  cnf(c_0_113, plain, (r3_lattice3(X1,X2,X3)|v2_struct_0(X1)|~r1_lattices(X1,X2,esk1_3(X1,X2,X3))|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 40.61/40.87  cnf(c_0_114, negated_conjecture, (r3_lattice3(esk5_0,X1,a_2_0_lattice3(esk4_0,esk5_0))|r1_lattices(esk5_0,k7_lattices(esk5_0,esk6_0),esk1_3(esk5_0,X1,a_2_0_lattice3(esk4_0,esk5_0)))|~m1_subset_1(k7_lattices(esk5_0,esk6_0),u1_struct_0(esk5_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_111, c_0_112])).
% 40.61/40.87  cnf(c_0_115, negated_conjecture, (~r4_lattice3(esk5_0,esk6_0,esk4_0)|~r3_lattice3(esk5_0,k7_lattices(esk5_0,esk6_0),a_2_0_lattice3(esk4_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 40.61/40.87  cnf(c_0_116, negated_conjecture, (r3_lattice3(esk5_0,k7_lattices(esk5_0,esk6_0),a_2_0_lattice3(esk4_0,esk5_0))|~m1_subset_1(k7_lattices(esk5_0,esk6_0),u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_114]), c_0_15])]), c_0_16])).
% 40.61/40.87  cnf(c_0_117, negated_conjecture, (~m1_subset_1(k7_lattices(esk5_0,esk6_0),u1_struct_0(esk5_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_116]), c_0_92])).
% 40.61/40.87  cnf(c_0_118, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_33]), c_0_74]), c_0_15])]), c_0_16]), ['proof']).
% 40.61/40.87  # SZS output end CNFRefutation
% 40.61/40.87  # Proof object total steps             : 119
% 40.61/40.87  # Proof object clause steps            : 100
% 40.61/40.87  # Proof object formula steps           : 19
% 40.61/40.87  # Proof object conjectures             : 78
% 40.61/40.87  # Proof object clause conjectures      : 75
% 40.61/40.87  # Proof object formula conjectures     : 3
% 40.61/40.87  # Proof object initial clauses used    : 27
% 40.61/40.87  # Proof object initial formulas used   : 9
% 40.61/40.87  # Proof object generating inferences   : 73
% 40.61/40.87  # Proof object simplifying inferences  : 171
% 40.61/40.87  # Training examples: 0 positive, 0 negative
% 40.61/40.87  # Parsed axioms                        : 9
% 40.61/40.87  # Removed by relevancy pruning/SinE    : 0
% 40.61/40.87  # Initial clauses                      : 31
% 40.61/40.87  # Removed in clause preprocessing      : 1
% 40.61/40.87  # Initial clauses in saturation        : 30
% 40.61/40.87  # Processed clauses                    : 122669
% 40.61/40.87  # ...of these trivial                  : 192
% 40.61/40.87  # ...subsumed                          : 114723
% 40.61/40.87  # ...remaining for further processing  : 7754
% 40.61/40.87  # Other redundant clauses eliminated   : 255
% 40.61/40.87  # Clauses deleted for lack of memory   : 641242
% 40.61/40.87  # Backward-subsumed                    : 2449
% 40.61/40.87  # Backward-rewritten                   : 0
% 40.61/40.87  # Generated clauses                    : 2121004
% 40.61/40.87  # ...of the previous two non-trivial   : 2118830
% 40.61/40.87  # Contextual simplify-reflections      : 1153
% 40.61/40.87  # Paramodulations                      : 2120015
% 40.61/40.87  # Factorizations                       : 0
% 40.61/40.87  # Equation resolutions                 : 989
% 40.61/40.87  # Propositional unsat checks           : 0
% 40.61/40.87  #    Propositional check models        : 0
% 40.61/40.87  #    Propositional check unsatisfiable : 0
% 40.61/40.87  #    Propositional clauses             : 0
% 40.61/40.87  #    Propositional clauses after purity: 0
% 40.61/40.87  #    Propositional unsat core size     : 0
% 40.61/40.87  #    Propositional preprocessing time  : 0.000
% 40.61/40.87  #    Propositional encoding time       : 0.000
% 40.61/40.87  #    Propositional solver time         : 0.000
% 40.61/40.87  #    Success case prop preproc time    : 0.000
% 40.61/40.87  #    Success case prop encoding time   : 0.000
% 40.61/40.87  #    Success case prop solver time     : 0.000
% 40.61/40.87  # Current number of processed clauses  : 5275
% 40.61/40.87  #    Positive orientable unit clauses  : 4
% 40.61/40.87  #    Positive unorientable unit clauses: 0
% 40.61/40.87  #    Negative unit clauses             : 2
% 40.61/40.87  #    Non-unit-clauses                  : 5269
% 40.61/40.87  # Current number of unprocessed clauses: 1017809
% 40.61/40.87  # ...number of literals in the above   : 7054236
% 40.61/40.87  # Current number of archived formulas  : 0
% 40.61/40.87  # Current number of archived clauses   : 2479
% 40.61/40.87  # Clause-clause subsumption calls (NU) : 17599709
% 40.61/40.87  # Rec. Clause-clause subsumption calls : 4627804
% 40.61/40.87  # Non-unit clause-clause subsumptions  : 118325
% 40.61/40.87  # Unit Clause-clause subsumption calls : 817
% 40.61/40.87  # Rewrite failures with RHS unbound    : 0
% 40.61/40.87  # BW rewrite match attempts            : 0
% 40.61/40.87  # BW rewrite match successes           : 0
% 40.61/40.87  # Condensation attempts                : 0
% 40.61/40.87  # Condensation successes               : 0
% 40.61/40.87  # Termbank termtop insertions          : 140141000
% 40.66/40.94  
% 40.66/40.94  # -------------------------------------------------
% 40.66/40.94  # User time                : 39.622 s
% 40.66/40.94  # System time              : 0.924 s
% 40.66/40.94  # Total time               : 40.546 s
% 40.66/40.94  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
