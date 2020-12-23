%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:10 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 241 expanded)
%              Number of clauses        :   52 (  86 expanded)
%              Number of leaves         :    8 (  60 expanded)
%              Depth                    :   12
%              Number of atoms          :  664 (2438 expanded)
%              Number of equality atoms :   34 ( 163 expanded)
%              Maximal formula depth    :   23 (   9 average)
%              Maximal clause size      :   65 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(fraenkel_a_3_6_lattice3,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( ~ v2_struct_0(X2)
        & v10_lattices(X2)
        & v4_lattice3(X2)
        & l3_lattices(X2)
        & m1_subset_1(X3,u1_struct_0(X2))
        & m1_subset_1(X4,u1_struct_0(X2)) )
     => ( r2_hidden(X1,a_3_6_lattice3(X2,X3,X4))
      <=> ? [X5] :
            ( m1_subset_1(X5,u1_struct_0(X2))
            & X1 = X5
            & r3_lattices(X2,k4_lattices(X2,X3,X5),X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_3_6_lattice3)).

fof(d8_filter_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( ( ~ v2_struct_0(X1)
                  & v10_lattices(X1)
                  & v3_filter_0(X1)
                  & l3_lattices(X1) )
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( X4 = k4_filter_0(X1,X2,X3)
                    <=> ( r3_lattices(X1,k4_lattices(X1,X2,X4),X3)
                        & ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X1))
                           => ( r3_lattices(X1,k4_lattices(X1,X2,X5),X3)
                             => r3_lattices(X1,X5,X4) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_filter_0)).

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

fof(dt_k4_filter_0,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & l3_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k4_filter_0(X1,X2,X3),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_filter_0)).

fof(t52_lattice3,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v4_lattice3(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( ( ~ v2_struct_0(X1)
                  & v10_lattices(X1)
                  & v3_filter_0(X1)
                  & l3_lattices(X1) )
               => k4_filter_0(X1,X2,X3) = k15_lattice3(X1,a_3_6_lattice3(X1,X2,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_lattice3)).

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

fof(c_0_8,plain,(
    ! [X30,X31,X32,X33,X35] :
      ( ( m1_subset_1(esk4_4(X30,X31,X32,X33),u1_struct_0(X31))
        | ~ r2_hidden(X30,a_3_6_lattice3(X31,X32,X33))
        | v2_struct_0(X31)
        | ~ v10_lattices(X31)
        | ~ v4_lattice3(X31)
        | ~ l3_lattices(X31)
        | ~ m1_subset_1(X32,u1_struct_0(X31))
        | ~ m1_subset_1(X33,u1_struct_0(X31)) )
      & ( X30 = esk4_4(X30,X31,X32,X33)
        | ~ r2_hidden(X30,a_3_6_lattice3(X31,X32,X33))
        | v2_struct_0(X31)
        | ~ v10_lattices(X31)
        | ~ v4_lattice3(X31)
        | ~ l3_lattices(X31)
        | ~ m1_subset_1(X32,u1_struct_0(X31))
        | ~ m1_subset_1(X33,u1_struct_0(X31)) )
      & ( r3_lattices(X31,k4_lattices(X31,X32,esk4_4(X30,X31,X32,X33)),X33)
        | ~ r2_hidden(X30,a_3_6_lattice3(X31,X32,X33))
        | v2_struct_0(X31)
        | ~ v10_lattices(X31)
        | ~ v4_lattice3(X31)
        | ~ l3_lattices(X31)
        | ~ m1_subset_1(X32,u1_struct_0(X31))
        | ~ m1_subset_1(X33,u1_struct_0(X31)) )
      & ( ~ m1_subset_1(X35,u1_struct_0(X31))
        | X30 != X35
        | ~ r3_lattices(X31,k4_lattices(X31,X32,X35),X33)
        | r2_hidden(X30,a_3_6_lattice3(X31,X32,X33))
        | v2_struct_0(X31)
        | ~ v10_lattices(X31)
        | ~ v4_lattice3(X31)
        | ~ l3_lattices(X31)
        | ~ m1_subset_1(X32,u1_struct_0(X31))
        | ~ m1_subset_1(X33,u1_struct_0(X31)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_3_6_lattice3])])])])])])).

fof(c_0_9,plain,(
    ! [X10,X11,X12,X13,X14] :
      ( ( r3_lattices(X10,k4_lattices(X10,X11,X13),X12)
        | X13 != k4_filter_0(X10,X11,X12)
        | ~ m1_subset_1(X13,u1_struct_0(X10))
        | v2_struct_0(X10)
        | ~ v10_lattices(X10)
        | ~ v3_filter_0(X10)
        | ~ l3_lattices(X10)
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | v2_struct_0(X10)
        | ~ v10_lattices(X10)
        | ~ l3_lattices(X10) )
      & ( ~ m1_subset_1(X14,u1_struct_0(X10))
        | ~ r3_lattices(X10,k4_lattices(X10,X11,X14),X12)
        | r3_lattices(X10,X14,X13)
        | X13 != k4_filter_0(X10,X11,X12)
        | ~ m1_subset_1(X13,u1_struct_0(X10))
        | v2_struct_0(X10)
        | ~ v10_lattices(X10)
        | ~ v3_filter_0(X10)
        | ~ l3_lattices(X10)
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | v2_struct_0(X10)
        | ~ v10_lattices(X10)
        | ~ l3_lattices(X10) )
      & ( m1_subset_1(esk1_4(X10,X11,X12,X13),u1_struct_0(X10))
        | ~ r3_lattices(X10,k4_lattices(X10,X11,X13),X12)
        | X13 = k4_filter_0(X10,X11,X12)
        | ~ m1_subset_1(X13,u1_struct_0(X10))
        | v2_struct_0(X10)
        | ~ v10_lattices(X10)
        | ~ v3_filter_0(X10)
        | ~ l3_lattices(X10)
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | v2_struct_0(X10)
        | ~ v10_lattices(X10)
        | ~ l3_lattices(X10) )
      & ( r3_lattices(X10,k4_lattices(X10,X11,esk1_4(X10,X11,X12,X13)),X12)
        | ~ r3_lattices(X10,k4_lattices(X10,X11,X13),X12)
        | X13 = k4_filter_0(X10,X11,X12)
        | ~ m1_subset_1(X13,u1_struct_0(X10))
        | v2_struct_0(X10)
        | ~ v10_lattices(X10)
        | ~ v3_filter_0(X10)
        | ~ l3_lattices(X10)
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | v2_struct_0(X10)
        | ~ v10_lattices(X10)
        | ~ l3_lattices(X10) )
      & ( ~ r3_lattices(X10,esk1_4(X10,X11,X12,X13),X13)
        | ~ r3_lattices(X10,k4_lattices(X10,X11,X13),X12)
        | X13 = k4_filter_0(X10,X11,X12)
        | ~ m1_subset_1(X13,u1_struct_0(X10))
        | v2_struct_0(X10)
        | ~ v10_lattices(X10)
        | ~ v3_filter_0(X10)
        | ~ l3_lattices(X10)
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | v2_struct_0(X10)
        | ~ v10_lattices(X10)
        | ~ l3_lattices(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d8_filter_0])])])])])])).

fof(c_0_10,plain,(
    ! [X19,X20,X21,X22,X23] :
      ( ( ~ r4_lattice3(X19,X20,X21)
        | ~ m1_subset_1(X22,u1_struct_0(X19))
        | ~ r2_hidden(X22,X21)
        | r1_lattices(X19,X22,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X19))
        | v2_struct_0(X19)
        | ~ l3_lattices(X19) )
      & ( m1_subset_1(esk2_3(X19,X20,X23),u1_struct_0(X19))
        | r4_lattice3(X19,X20,X23)
        | ~ m1_subset_1(X20,u1_struct_0(X19))
        | v2_struct_0(X19)
        | ~ l3_lattices(X19) )
      & ( r2_hidden(esk2_3(X19,X20,X23),X23)
        | r4_lattice3(X19,X20,X23)
        | ~ m1_subset_1(X20,u1_struct_0(X19))
        | v2_struct_0(X19)
        | ~ l3_lattices(X19) )
      & ( ~ r1_lattices(X19,esk2_3(X19,X20,X23),X20)
        | r4_lattice3(X19,X20,X23)
        | ~ m1_subset_1(X20,u1_struct_0(X19))
        | v2_struct_0(X19)
        | ~ l3_lattices(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_lattice3])])])])])])])).

fof(c_0_11,plain,(
    ! [X16,X17,X18] :
      ( v2_struct_0(X16)
      | ~ v10_lattices(X16)
      | ~ l3_lattices(X16)
      | ~ m1_subset_1(X17,u1_struct_0(X16))
      | ~ m1_subset_1(X18,u1_struct_0(X16))
      | m1_subset_1(k4_filter_0(X16,X17,X18),u1_struct_0(X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_filter_0])])])).

cnf(c_0_12,plain,
    ( r2_hidden(X3,a_3_6_lattice3(X2,X4,X5))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | X3 != X1
    | ~ r3_lattices(X2,k4_lattices(X2,X4,X1),X5)
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X5,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( r3_lattices(X1,k4_lattices(X1,X2,X3),X4)
    | v2_struct_0(X1)
    | v2_struct_0(X1)
    | X3 != k4_filter_0(X1,X2,X4)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v3_filter_0(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v10_lattices(X1)
          & v4_lattice3(X1)
          & l3_lattices(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ( ( ~ v2_struct_0(X1)
                    & v10_lattices(X1)
                    & v3_filter_0(X1)
                    & l3_lattices(X1) )
                 => k4_filter_0(X1,X2,X3) = k15_lattice3(X1,a_3_6_lattice3(X1,X2,X3)) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t52_lattice3])).

cnf(c_0_15,plain,
    ( r1_lattices(X1,X4,X2)
    | v2_struct_0(X1)
    | ~ r4_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k4_filter_0(X1,X2,X3),u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,a_3_6_lattice3(X2,X3,X4))
    | v2_struct_0(X2)
    | ~ v4_lattice3(X2)
    | ~ r3_lattices(X2,k4_lattices(X2,X3,X1),X4)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( v2_struct_0(X1)
    | r3_lattices(X1,k4_lattices(X1,X2,X3),X4)
    | X3 != k4_filter_0(X1,X2,X4)
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1)
    | ~ v3_filter_0(X1)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(cn,[status(thm)],[c_0_13])).

fof(c_0_19,negated_conjecture,
    ( ~ v2_struct_0(esk5_0)
    & v10_lattices(esk5_0)
    & v4_lattice3(esk5_0)
    & l3_lattices(esk5_0)
    & m1_subset_1(esk6_0,u1_struct_0(esk5_0))
    & m1_subset_1(esk7_0,u1_struct_0(esk5_0))
    & ~ v2_struct_0(esk5_0)
    & v10_lattices(esk5_0)
    & v3_filter_0(esk5_0)
    & l3_lattices(esk5_0)
    & k4_filter_0(esk5_0,esk6_0,esk7_0) != k15_lattice3(esk5_0,a_3_6_lattice3(esk5_0,esk6_0,esk7_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).

cnf(c_0_20,plain,
    ( r1_lattices(X1,k4_filter_0(X1,X2,X3),X4)
    | v2_struct_0(X1)
    | ~ r2_hidden(k4_filter_0(X1,X2,X3),X5)
    | ~ r4_lattice3(X1,X4,X5)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_21,plain,
    ( r2_hidden(k4_filter_0(X1,X2,X3),a_3_6_lattice3(X1,X4,X5))
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ r3_lattices(X1,k4_lattices(X1,X4,k4_filter_0(X1,X2,X3)),X5)
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_16])).

cnf(c_0_22,plain,
    ( r3_lattices(X1,k4_lattices(X1,X2,k4_filter_0(X1,X2,X3)),X3)
    | v2_struct_0(X1)
    | ~ v3_filter_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_18]),c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( v3_filter_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( v10_lattices(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( l3_lattices(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_27,plain,(
    ! [X25,X26,X27,X28] :
      ( ( r4_lattice3(X25,X27,X26)
        | X27 != k15_lattice3(X25,X26)
        | ~ m1_subset_1(X27,u1_struct_0(X25))
        | v2_struct_0(X25)
        | ~ v10_lattices(X25)
        | ~ v4_lattice3(X25)
        | ~ l3_lattices(X25)
        | v2_struct_0(X25)
        | ~ l3_lattices(X25) )
      & ( ~ m1_subset_1(X28,u1_struct_0(X25))
        | ~ r4_lattice3(X25,X28,X26)
        | r1_lattices(X25,X27,X28)
        | X27 != k15_lattice3(X25,X26)
        | ~ m1_subset_1(X27,u1_struct_0(X25))
        | v2_struct_0(X25)
        | ~ v10_lattices(X25)
        | ~ v4_lattice3(X25)
        | ~ l3_lattices(X25)
        | v2_struct_0(X25)
        | ~ l3_lattices(X25) )
      & ( m1_subset_1(esk3_3(X25,X26,X27),u1_struct_0(X25))
        | ~ r4_lattice3(X25,X27,X26)
        | X27 = k15_lattice3(X25,X26)
        | ~ m1_subset_1(X27,u1_struct_0(X25))
        | v2_struct_0(X25)
        | ~ v10_lattices(X25)
        | ~ v4_lattice3(X25)
        | ~ l3_lattices(X25)
        | v2_struct_0(X25)
        | ~ l3_lattices(X25) )
      & ( r4_lattice3(X25,esk3_3(X25,X26,X27),X26)
        | ~ r4_lattice3(X25,X27,X26)
        | X27 = k15_lattice3(X25,X26)
        | ~ m1_subset_1(X27,u1_struct_0(X25))
        | v2_struct_0(X25)
        | ~ v10_lattices(X25)
        | ~ v4_lattice3(X25)
        | ~ l3_lattices(X25)
        | v2_struct_0(X25)
        | ~ l3_lattices(X25) )
      & ( ~ r1_lattices(X25,X27,esk3_3(X25,X26,X27))
        | ~ r4_lattice3(X25,X27,X26)
        | X27 = k15_lattice3(X25,X26)
        | ~ m1_subset_1(X27,u1_struct_0(X25))
        | v2_struct_0(X25)
        | ~ v10_lattices(X25)
        | ~ v4_lattice3(X25)
        | ~ l3_lattices(X25)
        | v2_struct_0(X25)
        | ~ l3_lattices(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d21_lattice3])])])])])])).

cnf(c_0_28,plain,
    ( r3_lattices(X2,X1,X5)
    | v2_struct_0(X2)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r3_lattices(X2,k4_lattices(X2,X3,X1),X4)
    | X5 != k4_filter_0(X2,X3,X4)
    | ~ m1_subset_1(X5,u1_struct_0(X2))
    | ~ v10_lattices(X2)
    | ~ v3_filter_0(X2)
    | ~ l3_lattices(X2)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_29,plain,
    ( r1_lattices(X1,k4_filter_0(X1,X2,X3),X4)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ r4_lattice3(X1,X4,a_3_6_lattice3(X1,X5,X6))
    | ~ r3_lattices(X1,k4_lattices(X1,X5,k4_filter_0(X1,X2,X3)),X6)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X6,u1_struct_0(X1))
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_30,negated_conjecture,
    ( r3_lattices(esk5_0,k4_lattices(esk5_0,X1,k4_filter_0(esk5_0,X1,X2)),X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( v4_lattice3(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_32,plain,
    ( r4_lattice3(X1,esk3_3(X1,X2,X3),X2)
    | X3 = k15_lattice3(X1,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X1)
    | ~ r4_lattice3(X1,X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_33,plain,(
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

fof(c_0_34,plain,(
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

cnf(c_0_35,plain,
    ( v2_struct_0(X2)
    | r3_lattices(X2,X1,X5)
    | X5 != k4_filter_0(X2,X3,X4)
    | ~ l3_lattices(X2)
    | ~ v10_lattices(X2)
    | ~ v3_filter_0(X2)
    | ~ m1_subset_1(X5,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r3_lattices(X2,k4_lattices(X2,X3,X1),X4) ),
    inference(cn,[status(thm)],[c_0_28])).

cnf(c_0_36,negated_conjecture,
    ( r1_lattices(esk5_0,k4_filter_0(esk5_0,X1,X2),X3)
    | ~ r4_lattice3(esk5_0,X3,a_3_6_lattice3(esk5_0,X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(esk5_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_37,plain,
    ( X3 = k15_lattice3(X1,X2)
    | v2_struct_0(X1)
    | r4_lattice3(X1,esk3_3(X1,X2,X3),X2)
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ r4_lattice3(X1,X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(cn,[status(thm)],[c_0_32])).

cnf(c_0_38,plain,
    ( m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X1))
    | X3 = k15_lattice3(X1,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X1)
    | ~ r4_lattice3(X1,X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_39,plain,
    ( r1_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_40,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_41,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,plain,
    ( v9_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_43,plain,
    ( r3_lattices(X1,X2,k4_filter_0(X1,X3,X4))
    | v2_struct_0(X1)
    | ~ v3_filter_0(X1)
    | ~ r3_lattices(X1,k4_lattices(X1,X3,X2),X4)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_35]),c_0_16])).

cnf(c_0_44,plain,
    ( r3_lattices(X1,k4_lattices(X1,X2,esk4_4(X3,X1,X2,X4)),X4)
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,a_3_6_lattice3(X1,X2,X4))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_45,plain,
    ( m1_subset_1(esk4_4(X1,X2,X3,X4),u1_struct_0(X2))
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_3_6_lattice3(X2,X3,X4))
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_46,plain,
    ( X2 = k15_lattice3(X1,X3)
    | v2_struct_0(X1)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,esk3_3(X1,X3,X2))
    | ~ r4_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_47,negated_conjecture,
    ( X1 = k15_lattice3(esk5_0,a_3_6_lattice3(esk5_0,X2,X3))
    | r1_lattices(esk5_0,k4_filter_0(esk5_0,X2,X3),esk3_3(esk5_0,a_3_6_lattice3(esk5_0,X2,X3),X1))
    | ~ r4_lattice3(esk5_0,X1,a_3_6_lattice3(esk5_0,X2,X3))
    | ~ m1_subset_1(esk3_3(esk5_0,a_3_6_lattice3(esk5_0,X2,X3),X1),u1_struct_0(esk5_0))
    | ~ m1_subset_1(X3,u1_struct_0(esk5_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_31]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_48,plain,
    ( X3 = k15_lattice3(X1,X2)
    | v2_struct_0(X1)
    | m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ r4_lattice3(X1,X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(cn,[status(thm)],[c_0_38])).

cnf(c_0_49,plain,
    ( r1_lattices(X1,X2,k4_filter_0(X1,X3,X4))
    | v2_struct_0(X1)
    | ~ r3_lattices(X1,X2,k4_filter_0(X1,X3,X4))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_16]),c_0_40]),c_0_41]),c_0_42])).

cnf(c_0_50,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X1))
    | r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_51,plain,
    ( r3_lattices(X1,esk4_4(X2,X1,X3,X4),k4_filter_0(X1,X3,X4))
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ r2_hidden(X2,a_3_6_lattice3(X1,X3,X4))
    | ~ v3_filter_0(X1)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45])).

cnf(c_0_52,plain,
    ( X1 = esk4_4(X1,X2,X3,X4)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_3_6_lattice3(X2,X3,X4))
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_53,plain,
    ( X2 = k15_lattice3(X1,X3)
    | v2_struct_0(X1)
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ r4_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r1_lattices(X1,X2,esk3_3(X1,X3,X2)) ),
    inference(cn,[status(thm)],[c_0_46])).

cnf(c_0_54,negated_conjecture,
    ( X1 = k15_lattice3(esk5_0,a_3_6_lattice3(esk5_0,X2,X3))
    | r1_lattices(esk5_0,k4_filter_0(esk5_0,X2,X3),esk3_3(esk5_0,a_3_6_lattice3(esk5_0,X2,X3),X1))
    | ~ r4_lattice3(esk5_0,X1,a_3_6_lattice3(esk5_0,X2,X3))
    | ~ m1_subset_1(X3,u1_struct_0(esk5_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_31]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_55,plain,
    ( r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,esk2_3(X1,X2,X3),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_56,plain,
    ( r4_lattice3(X1,X2,X3)
    | r1_lattices(X1,esk2_3(X1,X2,X3),k4_filter_0(X1,X4,X5))
    | v2_struct_0(X1)
    | ~ r3_lattices(X1,esk2_3(X1,X2,X3),k4_filter_0(X1,X4,X5))
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_57,plain,
    ( r3_lattices(X1,X2,k4_filter_0(X1,X3,X4))
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ r2_hidden(X2,a_3_6_lattice3(X1,X3,X4))
    | ~ v3_filter_0(X1)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_58,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X3)
    | r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_59,negated_conjecture,
    ( k4_filter_0(esk5_0,esk6_0,esk7_0) != k15_lattice3(esk5_0,a_3_6_lattice3(esk5_0,esk6_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_60,negated_conjecture,
    ( k15_lattice3(esk5_0,a_3_6_lattice3(esk5_0,X1,X2)) = k4_filter_0(esk5_0,X1,X2)
    | ~ r4_lattice3(esk5_0,k4_filter_0(esk5_0,X1,X2),a_3_6_lattice3(esk5_0,X1,X2))
    | ~ m1_subset_1(k4_filter_0(esk5_0,X1,X2),u1_struct_0(esk5_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_31]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_61,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_62,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_63,plain,
    ( r4_lattice3(X1,k4_filter_0(X1,X2,X3),X4)
    | v2_struct_0(X1)
    | ~ r3_lattices(X1,esk2_3(X1,k4_filter_0(X1,X2,X3),X4),k4_filter_0(X1,X2,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_16])).

cnf(c_0_64,plain,
    ( r4_lattice3(X1,X2,a_3_6_lattice3(X3,X4,X5))
    | r3_lattices(X3,esk2_3(X1,X2,a_3_6_lattice3(X3,X4,X5)),k4_filter_0(X3,X4,X5))
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ v4_lattice3(X3)
    | ~ v3_filter_0(X3)
    | ~ m1_subset_1(X5,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X3)
    | ~ l3_lattices(X3)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_65,negated_conjecture,
    ( ~ r4_lattice3(esk5_0,k4_filter_0(esk5_0,esk6_0,esk7_0),a_3_6_lattice3(esk5_0,esk6_0,esk7_0))
    | ~ m1_subset_1(k4_filter_0(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61]),c_0_62])])).

cnf(c_0_66,plain,
    ( r4_lattice3(X1,k4_filter_0(X1,X2,X3),a_3_6_lattice3(X1,X2,X3))
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v3_filter_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_16])).

cnf(c_0_67,negated_conjecture,
    ( ~ m1_subset_1(k4_filter_0(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_31]),c_0_23]),c_0_61]),c_0_62]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_68,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_16]),c_0_61]),c_0_62]),c_0_24]),c_0_25])]),c_0_26]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:33:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.46  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S5PRR_S0Y
% 0.19/0.46  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.46  #
% 0.19/0.46  # Preprocessing time       : 0.048 s
% 0.19/0.46  # Presaturation interreduction done
% 0.19/0.46  
% 0.19/0.46  # Proof found!
% 0.19/0.46  # SZS status Theorem
% 0.19/0.46  # SZS output start CNFRefutation
% 0.19/0.46  fof(fraenkel_a_3_6_lattice3, axiom, ![X1, X2, X3, X4]:((((((~(v2_struct_0(X2))&v10_lattices(X2))&v4_lattice3(X2))&l3_lattices(X2))&m1_subset_1(X3,u1_struct_0(X2)))&m1_subset_1(X4,u1_struct_0(X2)))=>(r2_hidden(X1,a_3_6_lattice3(X2,X3,X4))<=>?[X5]:((m1_subset_1(X5,u1_struct_0(X2))&X1=X5)&r3_lattices(X2,k4_lattices(X2,X3,X5),X4)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_3_6_lattice3)).
% 0.19/0.46  fof(d8_filter_0, axiom, ![X1]:(((~(v2_struct_0(X1))&v10_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>((((~(v2_struct_0(X1))&v10_lattices(X1))&v3_filter_0(X1))&l3_lattices(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(X4=k4_filter_0(X1,X2,X3)<=>(r3_lattices(X1,k4_lattices(X1,X2,X4),X3)&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>(r3_lattices(X1,k4_lattices(X1,X2,X5),X3)=>r3_lattices(X1,X5,X4)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_filter_0)).
% 0.19/0.46  fof(d17_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(r4_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X3)=>r1_lattices(X1,X4,X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d17_lattice3)).
% 0.19/0.46  fof(dt_k4_filter_0, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v10_lattices(X1))&l3_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>m1_subset_1(k4_filter_0(X1,X2,X3),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_filter_0)).
% 0.19/0.46  fof(t52_lattice3, conjecture, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>((((~(v2_struct_0(X1))&v10_lattices(X1))&v3_filter_0(X1))&l3_lattices(X1))=>k4_filter_0(X1,X2,X3)=k15_lattice3(X1,a_3_6_lattice3(X1,X2,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_lattice3)).
% 0.19/0.46  fof(d21_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(X3=k15_lattice3(X1,X2)<=>(r4_lattice3(X1,X3,X2)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r4_lattice3(X1,X4,X2)=>r1_lattices(X1,X3,X4)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d21_lattice3)).
% 0.19/0.46  fof(redefinition_r3_lattices, axiom, ![X1, X2, X3]:(((((((~(v2_struct_0(X1))&v6_lattices(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>(r3_lattices(X1,X2,X3)<=>r1_lattices(X1,X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 0.19/0.46  fof(cc1_lattices, axiom, ![X1]:(l3_lattices(X1)=>((~(v2_struct_0(X1))&v10_lattices(X1))=>((((((~(v2_struct_0(X1))&v4_lattices(X1))&v5_lattices(X1))&v6_lattices(X1))&v7_lattices(X1))&v8_lattices(X1))&v9_lattices(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattices)).
% 0.19/0.46  fof(c_0_8, plain, ![X30, X31, X32, X33, X35]:((((m1_subset_1(esk4_4(X30,X31,X32,X33),u1_struct_0(X31))|~r2_hidden(X30,a_3_6_lattice3(X31,X32,X33))|(v2_struct_0(X31)|~v10_lattices(X31)|~v4_lattice3(X31)|~l3_lattices(X31)|~m1_subset_1(X32,u1_struct_0(X31))|~m1_subset_1(X33,u1_struct_0(X31))))&(X30=esk4_4(X30,X31,X32,X33)|~r2_hidden(X30,a_3_6_lattice3(X31,X32,X33))|(v2_struct_0(X31)|~v10_lattices(X31)|~v4_lattice3(X31)|~l3_lattices(X31)|~m1_subset_1(X32,u1_struct_0(X31))|~m1_subset_1(X33,u1_struct_0(X31)))))&(r3_lattices(X31,k4_lattices(X31,X32,esk4_4(X30,X31,X32,X33)),X33)|~r2_hidden(X30,a_3_6_lattice3(X31,X32,X33))|(v2_struct_0(X31)|~v10_lattices(X31)|~v4_lattice3(X31)|~l3_lattices(X31)|~m1_subset_1(X32,u1_struct_0(X31))|~m1_subset_1(X33,u1_struct_0(X31)))))&(~m1_subset_1(X35,u1_struct_0(X31))|X30!=X35|~r3_lattices(X31,k4_lattices(X31,X32,X35),X33)|r2_hidden(X30,a_3_6_lattice3(X31,X32,X33))|(v2_struct_0(X31)|~v10_lattices(X31)|~v4_lattice3(X31)|~l3_lattices(X31)|~m1_subset_1(X32,u1_struct_0(X31))|~m1_subset_1(X33,u1_struct_0(X31))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_3_6_lattice3])])])])])])).
% 0.19/0.46  fof(c_0_9, plain, ![X10, X11, X12, X13, X14]:(((r3_lattices(X10,k4_lattices(X10,X11,X13),X12)|X13!=k4_filter_0(X10,X11,X12)|~m1_subset_1(X13,u1_struct_0(X10))|(v2_struct_0(X10)|~v10_lattices(X10)|~v3_filter_0(X10)|~l3_lattices(X10))|~m1_subset_1(X12,u1_struct_0(X10))|~m1_subset_1(X11,u1_struct_0(X10))|(v2_struct_0(X10)|~v10_lattices(X10)|~l3_lattices(X10)))&(~m1_subset_1(X14,u1_struct_0(X10))|(~r3_lattices(X10,k4_lattices(X10,X11,X14),X12)|r3_lattices(X10,X14,X13))|X13!=k4_filter_0(X10,X11,X12)|~m1_subset_1(X13,u1_struct_0(X10))|(v2_struct_0(X10)|~v10_lattices(X10)|~v3_filter_0(X10)|~l3_lattices(X10))|~m1_subset_1(X12,u1_struct_0(X10))|~m1_subset_1(X11,u1_struct_0(X10))|(v2_struct_0(X10)|~v10_lattices(X10)|~l3_lattices(X10))))&((m1_subset_1(esk1_4(X10,X11,X12,X13),u1_struct_0(X10))|~r3_lattices(X10,k4_lattices(X10,X11,X13),X12)|X13=k4_filter_0(X10,X11,X12)|~m1_subset_1(X13,u1_struct_0(X10))|(v2_struct_0(X10)|~v10_lattices(X10)|~v3_filter_0(X10)|~l3_lattices(X10))|~m1_subset_1(X12,u1_struct_0(X10))|~m1_subset_1(X11,u1_struct_0(X10))|(v2_struct_0(X10)|~v10_lattices(X10)|~l3_lattices(X10)))&((r3_lattices(X10,k4_lattices(X10,X11,esk1_4(X10,X11,X12,X13)),X12)|~r3_lattices(X10,k4_lattices(X10,X11,X13),X12)|X13=k4_filter_0(X10,X11,X12)|~m1_subset_1(X13,u1_struct_0(X10))|(v2_struct_0(X10)|~v10_lattices(X10)|~v3_filter_0(X10)|~l3_lattices(X10))|~m1_subset_1(X12,u1_struct_0(X10))|~m1_subset_1(X11,u1_struct_0(X10))|(v2_struct_0(X10)|~v10_lattices(X10)|~l3_lattices(X10)))&(~r3_lattices(X10,esk1_4(X10,X11,X12,X13),X13)|~r3_lattices(X10,k4_lattices(X10,X11,X13),X12)|X13=k4_filter_0(X10,X11,X12)|~m1_subset_1(X13,u1_struct_0(X10))|(v2_struct_0(X10)|~v10_lattices(X10)|~v3_filter_0(X10)|~l3_lattices(X10))|~m1_subset_1(X12,u1_struct_0(X10))|~m1_subset_1(X11,u1_struct_0(X10))|(v2_struct_0(X10)|~v10_lattices(X10)|~l3_lattices(X10)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d8_filter_0])])])])])])).
% 0.19/0.46  fof(c_0_10, plain, ![X19, X20, X21, X22, X23]:((~r4_lattice3(X19,X20,X21)|(~m1_subset_1(X22,u1_struct_0(X19))|(~r2_hidden(X22,X21)|r1_lattices(X19,X22,X20)))|~m1_subset_1(X20,u1_struct_0(X19))|(v2_struct_0(X19)|~l3_lattices(X19)))&((m1_subset_1(esk2_3(X19,X20,X23),u1_struct_0(X19))|r4_lattice3(X19,X20,X23)|~m1_subset_1(X20,u1_struct_0(X19))|(v2_struct_0(X19)|~l3_lattices(X19)))&((r2_hidden(esk2_3(X19,X20,X23),X23)|r4_lattice3(X19,X20,X23)|~m1_subset_1(X20,u1_struct_0(X19))|(v2_struct_0(X19)|~l3_lattices(X19)))&(~r1_lattices(X19,esk2_3(X19,X20,X23),X20)|r4_lattice3(X19,X20,X23)|~m1_subset_1(X20,u1_struct_0(X19))|(v2_struct_0(X19)|~l3_lattices(X19)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_lattice3])])])])])])])).
% 0.19/0.46  fof(c_0_11, plain, ![X16, X17, X18]:(v2_struct_0(X16)|~v10_lattices(X16)|~l3_lattices(X16)|~m1_subset_1(X17,u1_struct_0(X16))|~m1_subset_1(X18,u1_struct_0(X16))|m1_subset_1(k4_filter_0(X16,X17,X18),u1_struct_0(X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_filter_0])])])).
% 0.19/0.46  cnf(c_0_12, plain, (r2_hidden(X3,a_3_6_lattice3(X2,X4,X5))|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|X3!=X1|~r3_lattices(X2,k4_lattices(X2,X4,X1),X5)|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X5,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.46  cnf(c_0_13, plain, (r3_lattices(X1,k4_lattices(X1,X2,X3),X4)|v2_struct_0(X1)|v2_struct_0(X1)|X3!=k4_filter_0(X1,X2,X4)|~m1_subset_1(X3,u1_struct_0(X1))|~v10_lattices(X1)|~v3_filter_0(X1)|~l3_lattices(X1)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.46  fof(c_0_14, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>((((~(v2_struct_0(X1))&v10_lattices(X1))&v3_filter_0(X1))&l3_lattices(X1))=>k4_filter_0(X1,X2,X3)=k15_lattice3(X1,a_3_6_lattice3(X1,X2,X3))))))), inference(assume_negation,[status(cth)],[t52_lattice3])).
% 0.19/0.46  cnf(c_0_15, plain, (r1_lattices(X1,X4,X2)|v2_struct_0(X1)|~r4_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X4,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.46  cnf(c_0_16, plain, (v2_struct_0(X1)|m1_subset_1(k4_filter_0(X1,X2,X3),u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.46  cnf(c_0_17, plain, (r2_hidden(X1,a_3_6_lattice3(X2,X3,X4))|v2_struct_0(X2)|~v4_lattice3(X2)|~r3_lattices(X2,k4_lattices(X2,X3,X1),X4)|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X3,u1_struct_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))|~v10_lattices(X2)|~l3_lattices(X2)), inference(er,[status(thm)],[c_0_12])).
% 0.19/0.46  cnf(c_0_18, plain, (v2_struct_0(X1)|r3_lattices(X1,k4_lattices(X1,X2,X3),X4)|X3!=k4_filter_0(X1,X2,X4)|~l3_lattices(X1)|~v10_lattices(X1)|~v3_filter_0(X1)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))), inference(cn,[status(thm)],[c_0_13])).
% 0.19/0.46  fof(c_0_19, negated_conjecture, ((((~v2_struct_0(esk5_0)&v10_lattices(esk5_0))&v4_lattice3(esk5_0))&l3_lattices(esk5_0))&(m1_subset_1(esk6_0,u1_struct_0(esk5_0))&(m1_subset_1(esk7_0,u1_struct_0(esk5_0))&((((~v2_struct_0(esk5_0)&v10_lattices(esk5_0))&v3_filter_0(esk5_0))&l3_lattices(esk5_0))&k4_filter_0(esk5_0,esk6_0,esk7_0)!=k15_lattice3(esk5_0,a_3_6_lattice3(esk5_0,esk6_0,esk7_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).
% 0.19/0.46  cnf(c_0_20, plain, (r1_lattices(X1,k4_filter_0(X1,X2,X3),X4)|v2_struct_0(X1)|~r2_hidden(k4_filter_0(X1,X2,X3),X5)|~r4_lattice3(X1,X4,X5)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.19/0.46  cnf(c_0_21, plain, (r2_hidden(k4_filter_0(X1,X2,X3),a_3_6_lattice3(X1,X4,X5))|v2_struct_0(X1)|~v4_lattice3(X1)|~r3_lattices(X1,k4_lattices(X1,X4,k4_filter_0(X1,X2,X3)),X5)|~m1_subset_1(X5,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_17, c_0_16])).
% 0.19/0.46  cnf(c_0_22, plain, (r3_lattices(X1,k4_lattices(X1,X2,k4_filter_0(X1,X2,X3)),X3)|v2_struct_0(X1)|~v3_filter_0(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_18]), c_0_16])).
% 0.19/0.46  cnf(c_0_23, negated_conjecture, (v3_filter_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.46  cnf(c_0_24, negated_conjecture, (v10_lattices(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.46  cnf(c_0_25, negated_conjecture, (l3_lattices(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.46  cnf(c_0_26, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.46  fof(c_0_27, plain, ![X25, X26, X27, X28]:(((r4_lattice3(X25,X27,X26)|X27!=k15_lattice3(X25,X26)|~m1_subset_1(X27,u1_struct_0(X25))|(v2_struct_0(X25)|~v10_lattices(X25)|~v4_lattice3(X25)|~l3_lattices(X25))|(v2_struct_0(X25)|~l3_lattices(X25)))&(~m1_subset_1(X28,u1_struct_0(X25))|(~r4_lattice3(X25,X28,X26)|r1_lattices(X25,X27,X28))|X27!=k15_lattice3(X25,X26)|~m1_subset_1(X27,u1_struct_0(X25))|(v2_struct_0(X25)|~v10_lattices(X25)|~v4_lattice3(X25)|~l3_lattices(X25))|(v2_struct_0(X25)|~l3_lattices(X25))))&((m1_subset_1(esk3_3(X25,X26,X27),u1_struct_0(X25))|~r4_lattice3(X25,X27,X26)|X27=k15_lattice3(X25,X26)|~m1_subset_1(X27,u1_struct_0(X25))|(v2_struct_0(X25)|~v10_lattices(X25)|~v4_lattice3(X25)|~l3_lattices(X25))|(v2_struct_0(X25)|~l3_lattices(X25)))&((r4_lattice3(X25,esk3_3(X25,X26,X27),X26)|~r4_lattice3(X25,X27,X26)|X27=k15_lattice3(X25,X26)|~m1_subset_1(X27,u1_struct_0(X25))|(v2_struct_0(X25)|~v10_lattices(X25)|~v4_lattice3(X25)|~l3_lattices(X25))|(v2_struct_0(X25)|~l3_lattices(X25)))&(~r1_lattices(X25,X27,esk3_3(X25,X26,X27))|~r4_lattice3(X25,X27,X26)|X27=k15_lattice3(X25,X26)|~m1_subset_1(X27,u1_struct_0(X25))|(v2_struct_0(X25)|~v10_lattices(X25)|~v4_lattice3(X25)|~l3_lattices(X25))|(v2_struct_0(X25)|~l3_lattices(X25)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d21_lattice3])])])])])])).
% 0.19/0.46  cnf(c_0_28, plain, (r3_lattices(X2,X1,X5)|v2_struct_0(X2)|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~r3_lattices(X2,k4_lattices(X2,X3,X1),X4)|X5!=k4_filter_0(X2,X3,X4)|~m1_subset_1(X5,u1_struct_0(X2))|~v10_lattices(X2)|~v3_filter_0(X2)|~l3_lattices(X2)|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X3,u1_struct_0(X2))|~v10_lattices(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.46  cnf(c_0_29, plain, (r1_lattices(X1,k4_filter_0(X1,X2,X3),X4)|v2_struct_0(X1)|~v4_lattice3(X1)|~r4_lattice3(X1,X4,a_3_6_lattice3(X1,X5,X6))|~r3_lattices(X1,k4_lattices(X1,X5,k4_filter_0(X1,X2,X3)),X6)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X6,u1_struct_0(X1))|~m1_subset_1(X5,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.19/0.46  cnf(c_0_30, negated_conjecture, (r3_lattices(esk5_0,k4_lattices(esk5_0,X1,k4_filter_0(esk5_0,X1,X2)),X2)|~m1_subset_1(X2,u1_struct_0(esk5_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24]), c_0_25])]), c_0_26])).
% 0.19/0.46  cnf(c_0_31, negated_conjecture, (v4_lattice3(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.46  cnf(c_0_32, plain, (r4_lattice3(X1,esk3_3(X1,X2,X3),X2)|X3=k15_lattice3(X1,X2)|v2_struct_0(X1)|v2_struct_0(X1)|~r4_lattice3(X1,X3,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.46  fof(c_0_33, plain, ![X7, X8, X9]:((~r3_lattices(X7,X8,X9)|r1_lattices(X7,X8,X9)|(v2_struct_0(X7)|~v6_lattices(X7)|~v8_lattices(X7)|~v9_lattices(X7)|~l3_lattices(X7)|~m1_subset_1(X8,u1_struct_0(X7))|~m1_subset_1(X9,u1_struct_0(X7))))&(~r1_lattices(X7,X8,X9)|r3_lattices(X7,X8,X9)|(v2_struct_0(X7)|~v6_lattices(X7)|~v8_lattices(X7)|~v9_lattices(X7)|~l3_lattices(X7)|~m1_subset_1(X8,u1_struct_0(X7))|~m1_subset_1(X9,u1_struct_0(X7))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).
% 0.19/0.46  fof(c_0_34, plain, ![X6]:(((((((~v2_struct_0(X6)|(v2_struct_0(X6)|~v10_lattices(X6))|~l3_lattices(X6))&(v4_lattices(X6)|(v2_struct_0(X6)|~v10_lattices(X6))|~l3_lattices(X6)))&(v5_lattices(X6)|(v2_struct_0(X6)|~v10_lattices(X6))|~l3_lattices(X6)))&(v6_lattices(X6)|(v2_struct_0(X6)|~v10_lattices(X6))|~l3_lattices(X6)))&(v7_lattices(X6)|(v2_struct_0(X6)|~v10_lattices(X6))|~l3_lattices(X6)))&(v8_lattices(X6)|(v2_struct_0(X6)|~v10_lattices(X6))|~l3_lattices(X6)))&(v9_lattices(X6)|(v2_struct_0(X6)|~v10_lattices(X6))|~l3_lattices(X6))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).
% 0.19/0.46  cnf(c_0_35, plain, (v2_struct_0(X2)|r3_lattices(X2,X1,X5)|X5!=k4_filter_0(X2,X3,X4)|~l3_lattices(X2)|~v10_lattices(X2)|~v3_filter_0(X2)|~m1_subset_1(X5,u1_struct_0(X2))|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X3,u1_struct_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))|~r3_lattices(X2,k4_lattices(X2,X3,X1),X4)), inference(cn,[status(thm)],[c_0_28])).
% 0.19/0.46  cnf(c_0_36, negated_conjecture, (r1_lattices(esk5_0,k4_filter_0(esk5_0,X1,X2),X3)|~r4_lattice3(esk5_0,X3,a_3_6_lattice3(esk5_0,X1,X2))|~m1_subset_1(X3,u1_struct_0(esk5_0))|~m1_subset_1(X2,u1_struct_0(esk5_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31]), c_0_24]), c_0_25])]), c_0_26])).
% 0.19/0.46  cnf(c_0_37, plain, (X3=k15_lattice3(X1,X2)|v2_struct_0(X1)|r4_lattice3(X1,esk3_3(X1,X2,X3),X2)|~l3_lattices(X1)|~v10_lattices(X1)|~v4_lattice3(X1)|~r4_lattice3(X1,X3,X2)|~m1_subset_1(X3,u1_struct_0(X1))), inference(cn,[status(thm)],[c_0_32])).
% 0.19/0.46  cnf(c_0_38, plain, (m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X1))|X3=k15_lattice3(X1,X2)|v2_struct_0(X1)|v2_struct_0(X1)|~r4_lattice3(X1,X3,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.46  cnf(c_0_39, plain, (r1_lattices(X1,X2,X3)|v2_struct_0(X1)|~r3_lattices(X1,X2,X3)|~v6_lattices(X1)|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.46  cnf(c_0_40, plain, (v6_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.46  cnf(c_0_41, plain, (v8_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.46  cnf(c_0_42, plain, (v9_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.46  cnf(c_0_43, plain, (r3_lattices(X1,X2,k4_filter_0(X1,X3,X4))|v2_struct_0(X1)|~v3_filter_0(X1)|~r3_lattices(X1,k4_lattices(X1,X3,X2),X4)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_35]), c_0_16])).
% 0.19/0.46  cnf(c_0_44, plain, (r3_lattices(X1,k4_lattices(X1,X2,esk4_4(X3,X1,X2,X4)),X4)|v2_struct_0(X1)|~r2_hidden(X3,a_3_6_lattice3(X1,X2,X4))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.46  cnf(c_0_45, plain, (m1_subset_1(esk4_4(X1,X2,X3,X4),u1_struct_0(X2))|v2_struct_0(X2)|~r2_hidden(X1,a_3_6_lattice3(X2,X3,X4))|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)|~m1_subset_1(X3,u1_struct_0(X2))|~m1_subset_1(X4,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.46  cnf(c_0_46, plain, (X2=k15_lattice3(X1,X3)|v2_struct_0(X1)|v2_struct_0(X1)|~r1_lattices(X1,X2,esk3_3(X1,X3,X2))|~r4_lattice3(X1,X2,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.46  cnf(c_0_47, negated_conjecture, (X1=k15_lattice3(esk5_0,a_3_6_lattice3(esk5_0,X2,X3))|r1_lattices(esk5_0,k4_filter_0(esk5_0,X2,X3),esk3_3(esk5_0,a_3_6_lattice3(esk5_0,X2,X3),X1))|~r4_lattice3(esk5_0,X1,a_3_6_lattice3(esk5_0,X2,X3))|~m1_subset_1(esk3_3(esk5_0,a_3_6_lattice3(esk5_0,X2,X3),X1),u1_struct_0(esk5_0))|~m1_subset_1(X3,u1_struct_0(esk5_0))|~m1_subset_1(X2,u1_struct_0(esk5_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_31]), c_0_24]), c_0_25])]), c_0_26])).
% 0.19/0.46  cnf(c_0_48, plain, (X3=k15_lattice3(X1,X2)|v2_struct_0(X1)|m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X1))|~l3_lattices(X1)|~v10_lattices(X1)|~v4_lattice3(X1)|~r4_lattice3(X1,X3,X2)|~m1_subset_1(X3,u1_struct_0(X1))), inference(cn,[status(thm)],[c_0_38])).
% 0.19/0.46  cnf(c_0_49, plain, (r1_lattices(X1,X2,k4_filter_0(X1,X3,X4))|v2_struct_0(X1)|~r3_lattices(X1,X2,k4_filter_0(X1,X3,X4))|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_16]), c_0_40]), c_0_41]), c_0_42])).
% 0.19/0.46  cnf(c_0_50, plain, (m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X1))|r4_lattice3(X1,X2,X3)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.46  cnf(c_0_51, plain, (r3_lattices(X1,esk4_4(X2,X1,X3,X4),k4_filter_0(X1,X3,X4))|v2_struct_0(X1)|~v4_lattice3(X1)|~r2_hidden(X2,a_3_6_lattice3(X1,X3,X4))|~v3_filter_0(X1)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45])).
% 0.19/0.46  cnf(c_0_52, plain, (X1=esk4_4(X1,X2,X3,X4)|v2_struct_0(X2)|~r2_hidden(X1,a_3_6_lattice3(X2,X3,X4))|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)|~m1_subset_1(X3,u1_struct_0(X2))|~m1_subset_1(X4,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.46  cnf(c_0_53, plain, (X2=k15_lattice3(X1,X3)|v2_struct_0(X1)|~l3_lattices(X1)|~v10_lattices(X1)|~v4_lattice3(X1)|~r4_lattice3(X1,X2,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~r1_lattices(X1,X2,esk3_3(X1,X3,X2))), inference(cn,[status(thm)],[c_0_46])).
% 0.19/0.46  cnf(c_0_54, negated_conjecture, (X1=k15_lattice3(esk5_0,a_3_6_lattice3(esk5_0,X2,X3))|r1_lattices(esk5_0,k4_filter_0(esk5_0,X2,X3),esk3_3(esk5_0,a_3_6_lattice3(esk5_0,X2,X3),X1))|~r4_lattice3(esk5_0,X1,a_3_6_lattice3(esk5_0,X2,X3))|~m1_subset_1(X3,u1_struct_0(esk5_0))|~m1_subset_1(X2,u1_struct_0(esk5_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_31]), c_0_24]), c_0_25])]), c_0_26])).
% 0.19/0.46  cnf(c_0_55, plain, (r4_lattice3(X1,X2,X3)|v2_struct_0(X1)|~r1_lattices(X1,esk2_3(X1,X2,X3),X2)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.46  cnf(c_0_56, plain, (r4_lattice3(X1,X2,X3)|r1_lattices(X1,esk2_3(X1,X2,X3),k4_filter_0(X1,X4,X5))|v2_struct_0(X1)|~r3_lattices(X1,esk2_3(X1,X2,X3),k4_filter_0(X1,X4,X5))|~m1_subset_1(X5,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.19/0.46  cnf(c_0_57, plain, (r3_lattices(X1,X2,k4_filter_0(X1,X3,X4))|v2_struct_0(X1)|~v4_lattice3(X1)|~r2_hidden(X2,a_3_6_lattice3(X1,X3,X4))|~v3_filter_0(X1)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.19/0.46  cnf(c_0_58, plain, (r2_hidden(esk2_3(X1,X2,X3),X3)|r4_lattice3(X1,X2,X3)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.46  cnf(c_0_59, negated_conjecture, (k4_filter_0(esk5_0,esk6_0,esk7_0)!=k15_lattice3(esk5_0,a_3_6_lattice3(esk5_0,esk6_0,esk7_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.46  cnf(c_0_60, negated_conjecture, (k15_lattice3(esk5_0,a_3_6_lattice3(esk5_0,X1,X2))=k4_filter_0(esk5_0,X1,X2)|~r4_lattice3(esk5_0,k4_filter_0(esk5_0,X1,X2),a_3_6_lattice3(esk5_0,X1,X2))|~m1_subset_1(k4_filter_0(esk5_0,X1,X2),u1_struct_0(esk5_0))|~m1_subset_1(X2,u1_struct_0(esk5_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_31]), c_0_24]), c_0_25])]), c_0_26])).
% 0.19/0.46  cnf(c_0_61, negated_conjecture, (m1_subset_1(esk7_0,u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.46  cnf(c_0_62, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.46  cnf(c_0_63, plain, (r4_lattice3(X1,k4_filter_0(X1,X2,X3),X4)|v2_struct_0(X1)|~r3_lattices(X1,esk2_3(X1,k4_filter_0(X1,X2,X3),X4),k4_filter_0(X1,X2,X3))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_16])).
% 0.19/0.46  cnf(c_0_64, plain, (r4_lattice3(X1,X2,a_3_6_lattice3(X3,X4,X5))|r3_lattices(X3,esk2_3(X1,X2,a_3_6_lattice3(X3,X4,X5)),k4_filter_0(X3,X4,X5))|v2_struct_0(X1)|v2_struct_0(X3)|~v4_lattice3(X3)|~v3_filter_0(X3)|~m1_subset_1(X5,u1_struct_0(X3))|~m1_subset_1(X4,u1_struct_0(X3))|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X3)|~l3_lattices(X3)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.19/0.46  cnf(c_0_65, negated_conjecture, (~r4_lattice3(esk5_0,k4_filter_0(esk5_0,esk6_0,esk7_0),a_3_6_lattice3(esk5_0,esk6_0,esk7_0))|~m1_subset_1(k4_filter_0(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_61]), c_0_62])])).
% 0.19/0.46  cnf(c_0_66, plain, (r4_lattice3(X1,k4_filter_0(X1,X2,X3),a_3_6_lattice3(X1,X2,X3))|v2_struct_0(X1)|~v4_lattice3(X1)|~v3_filter_0(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_16])).
% 0.19/0.46  cnf(c_0_67, negated_conjecture, (~m1_subset_1(k4_filter_0(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_31]), c_0_23]), c_0_61]), c_0_62]), c_0_24]), c_0_25])]), c_0_26])).
% 0.19/0.46  cnf(c_0_68, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_16]), c_0_61]), c_0_62]), c_0_24]), c_0_25])]), c_0_26]), ['proof']).
% 0.19/0.46  # SZS output end CNFRefutation
% 0.19/0.46  # Proof object total steps             : 69
% 0.19/0.46  # Proof object clause steps            : 52
% 0.19/0.46  # Proof object formula steps           : 17
% 0.19/0.46  # Proof object conjectures             : 19
% 0.19/0.46  # Proof object clause conjectures      : 16
% 0.19/0.46  # Proof object formula conjectures     : 3
% 0.19/0.46  # Proof object initial clauses used    : 26
% 0.19/0.46  # Proof object initial formulas used   : 8
% 0.19/0.46  # Proof object generating inferences   : 18
% 0.19/0.46  # Proof object simplifying inferences  : 57
% 0.19/0.46  # Training examples: 0 positive, 0 negative
% 0.19/0.46  # Parsed axioms                        : 8
% 0.19/0.46  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.46  # Initial clauses                      : 39
% 0.19/0.46  # Removed in clause preprocessing      : 1
% 0.19/0.46  # Initial clauses in saturation        : 38
% 0.19/0.46  # Processed clauses                    : 316
% 0.19/0.46  # ...of these trivial                  : 2
% 0.19/0.46  # ...subsumed                          : 72
% 0.19/0.46  # ...remaining for further processing  : 242
% 0.19/0.46  # Other redundant clauses eliminated   : 5
% 0.19/0.46  # Clauses deleted for lack of memory   : 0
% 0.19/0.46  # Backward-subsumed                    : 7
% 0.19/0.46  # Backward-rewritten                   : 0
% 0.19/0.46  # Generated clauses                    : 383
% 0.19/0.46  # ...of the previous two non-trivial   : 324
% 0.19/0.46  # Contextual simplify-reflections      : 36
% 0.19/0.46  # Paramodulations                      : 378
% 0.19/0.46  # Factorizations                       : 0
% 0.19/0.46  # Equation resolutions                 : 5
% 0.19/0.46  # Propositional unsat checks           : 0
% 0.19/0.46  #    Propositional check models        : 0
% 0.19/0.46  #    Propositional check unsatisfiable : 0
% 0.19/0.46  #    Propositional clauses             : 0
% 0.19/0.46  #    Propositional clauses after purity: 0
% 0.19/0.46  #    Propositional unsat core size     : 0
% 0.19/0.46  #    Propositional preprocessing time  : 0.000
% 0.19/0.46  #    Propositional encoding time       : 0.000
% 0.19/0.46  #    Propositional solver time         : 0.000
% 0.19/0.46  #    Success case prop preproc time    : 0.000
% 0.19/0.46  #    Success case prop encoding time   : 0.000
% 0.19/0.46  #    Success case prop solver time     : 0.000
% 0.19/0.46  # Current number of processed clauses  : 195
% 0.19/0.46  #    Positive orientable unit clauses  : 12
% 0.19/0.46  #    Positive unorientable unit clauses: 0
% 0.19/0.46  #    Negative unit clauses             : 3
% 0.19/0.46  #    Non-unit-clauses                  : 180
% 0.19/0.46  # Current number of unprocessed clauses: 81
% 0.19/0.46  # ...number of literals in the above   : 1119
% 0.19/0.46  # Current number of archived formulas  : 0
% 0.19/0.46  # Current number of archived clauses   : 42
% 0.19/0.46  # Clause-clause subsumption calls (NU) : 10076
% 0.19/0.46  # Rec. Clause-clause subsumption calls : 767
% 0.19/0.46  # Non-unit clause-clause subsumptions  : 114
% 0.19/0.46  # Unit Clause-clause subsumption calls : 61
% 0.19/0.46  # Rewrite failures with RHS unbound    : 0
% 0.19/0.46  # BW rewrite match attempts            : 0
% 0.19/0.46  # BW rewrite match successes           : 0
% 0.19/0.46  # Condensation attempts                : 0
% 0.19/0.46  # Condensation successes               : 0
% 0.19/0.46  # Termbank termtop insertions          : 23052
% 0.19/0.46  
% 0.19/0.46  # -------------------------------------------------
% 0.19/0.46  # User time                : 0.112 s
% 0.19/0.46  # System time              : 0.008 s
% 0.19/0.46  # Total time               : 0.120 s
% 0.19/0.46  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
