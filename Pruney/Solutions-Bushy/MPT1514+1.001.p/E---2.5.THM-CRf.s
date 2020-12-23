%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1514+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:19 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   81 (1879 expanded)
%              Number of clauses        :   64 ( 630 expanded)
%              Number of leaves         :    8 ( 462 expanded)
%              Depth                    :   31
%              Number of atoms          :  443 (15778 expanded)
%              Number of equality atoms :   10 (  96 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal clause size      :   50 (   3 average)
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

fof(t25_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v5_lattices(X1)
        & l2_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( ( r1_lattices(X1,X2,X3)
                      & r1_lattices(X1,X3,X4) )
                   => r1_lattices(X1,X2,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_lattices)).

fof(dt_l3_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( l1_lattices(X1)
        & l2_lattices(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(c_0_8,negated_conjecture,(
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

fof(c_0_9,plain,(
    ! [X13,X14,X15,X16] :
      ( ( r4_lattice3(X13,X15,X14)
        | X15 != k15_lattice3(X13,X14)
        | ~ m1_subset_1(X15,u1_struct_0(X13))
        | v2_struct_0(X13)
        | ~ v10_lattices(X13)
        | ~ v4_lattice3(X13)
        | ~ l3_lattices(X13)
        | v2_struct_0(X13)
        | ~ l3_lattices(X13) )
      & ( ~ m1_subset_1(X16,u1_struct_0(X13))
        | ~ r4_lattice3(X13,X16,X14)
        | r1_lattices(X13,X15,X16)
        | X15 != k15_lattice3(X13,X14)
        | ~ m1_subset_1(X15,u1_struct_0(X13))
        | v2_struct_0(X13)
        | ~ v10_lattices(X13)
        | ~ v4_lattice3(X13)
        | ~ l3_lattices(X13)
        | v2_struct_0(X13)
        | ~ l3_lattices(X13) )
      & ( m1_subset_1(esk2_3(X13,X14,X15),u1_struct_0(X13))
        | ~ r4_lattice3(X13,X15,X14)
        | X15 = k15_lattice3(X13,X14)
        | ~ m1_subset_1(X15,u1_struct_0(X13))
        | v2_struct_0(X13)
        | ~ v10_lattices(X13)
        | ~ v4_lattice3(X13)
        | ~ l3_lattices(X13)
        | v2_struct_0(X13)
        | ~ l3_lattices(X13) )
      & ( r4_lattice3(X13,esk2_3(X13,X14,X15),X14)
        | ~ r4_lattice3(X13,X15,X14)
        | X15 = k15_lattice3(X13,X14)
        | ~ m1_subset_1(X15,u1_struct_0(X13))
        | v2_struct_0(X13)
        | ~ v10_lattices(X13)
        | ~ v4_lattice3(X13)
        | ~ l3_lattices(X13)
        | v2_struct_0(X13)
        | ~ l3_lattices(X13) )
      & ( ~ r1_lattices(X13,X15,esk2_3(X13,X14,X15))
        | ~ r4_lattice3(X13,X15,X14)
        | X15 = k15_lattice3(X13,X14)
        | ~ m1_subset_1(X15,u1_struct_0(X13))
        | v2_struct_0(X13)
        | ~ v10_lattices(X13)
        | ~ v4_lattice3(X13)
        | ~ l3_lattices(X13)
        | v2_struct_0(X13)
        | ~ l3_lattices(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d21_lattice3])])])])])])).

fof(c_0_10,negated_conjecture,(
    ! [X34] :
      ( ~ v2_struct_0(esk3_0)
      & v10_lattices(esk3_0)
      & v4_lattice3(esk3_0)
      & l3_lattices(esk3_0)
      & ( m1_subset_1(esk6_1(X34),u1_struct_0(esk3_0))
        | ~ r2_hidden(X34,esk4_0)
        | ~ m1_subset_1(X34,u1_struct_0(esk3_0)) )
      & ( r3_lattices(esk3_0,X34,esk6_1(X34))
        | ~ r2_hidden(X34,esk4_0)
        | ~ m1_subset_1(X34,u1_struct_0(esk3_0)) )
      & ( r2_hidden(esk6_1(X34),esk5_0)
        | ~ r2_hidden(X34,esk4_0)
        | ~ m1_subset_1(X34,u1_struct_0(esk3_0)) )
      & ~ r3_lattices(esk3_0,k15_lattice3(esk3_0,esk4_0),k15_lattice3(esk3_0,esk5_0)) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])])])).

fof(c_0_11,plain,(
    ! [X18,X19] :
      ( v2_struct_0(X18)
      | ~ l3_lattices(X18)
      | m1_subset_1(k15_lattice3(X18,X19),u1_struct_0(X18)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k15_lattice3])])])).

cnf(c_0_12,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_13,plain,(
    ! [X7,X8,X9,X10,X11] :
      ( ( ~ r4_lattice3(X7,X8,X9)
        | ~ m1_subset_1(X10,u1_struct_0(X7))
        | ~ r2_hidden(X10,X9)
        | r1_lattices(X7,X10,X8)
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | v2_struct_0(X7)
        | ~ l3_lattices(X7) )
      & ( m1_subset_1(esk1_3(X7,X8,X11),u1_struct_0(X7))
        | r4_lattice3(X7,X8,X11)
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | v2_struct_0(X7)
        | ~ l3_lattices(X7) )
      & ( r2_hidden(esk1_3(X7,X8,X11),X11)
        | r4_lattice3(X7,X8,X11)
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | v2_struct_0(X7)
        | ~ l3_lattices(X7) )
      & ( ~ r1_lattices(X7,esk1_3(X7,X8,X11),X8)
        | r4_lattice3(X7,X8,X11)
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | v2_struct_0(X7)
        | ~ l3_lattices(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_lattice3])])])])])])])).

cnf(c_0_14,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( l3_lattices(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( v2_struct_0(X2)
    | r1_lattices(X2,X4,X1)
    | X4 != k15_lattice3(X2,X3)
    | ~ l3_lattices(X2)
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ r4_lattice3(X2,X1,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2)) ),
    inference(cn,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))
    | r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(k15_lattice3(esk3_0,X1),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16])])).

fof(c_0_20,plain,(
    ! [X21,X22,X23] :
      ( ( ~ r3_lattices(X21,X22,X23)
        | r1_lattices(X21,X22,X23)
        | v2_struct_0(X21)
        | ~ v6_lattices(X21)
        | ~ v8_lattices(X21)
        | ~ v9_lattices(X21)
        | ~ l3_lattices(X21)
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | ~ m1_subset_1(X23,u1_struct_0(X21)) )
      & ( ~ r1_lattices(X21,X22,X23)
        | r3_lattices(X21,X22,X23)
        | v2_struct_0(X21)
        | ~ v6_lattices(X21)
        | ~ v8_lattices(X21)
        | ~ v9_lattices(X21)
        | ~ l3_lattices(X21)
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | ~ m1_subset_1(X23,u1_struct_0(X21)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).

cnf(c_0_21,plain,
    ( r1_lattices(X1,k15_lattice3(X1,X2),X3)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ r4_lattice3(X1,X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_17]),c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( r4_lattice3(esk3_0,k15_lattice3(esk3_0,X1),X2)
    | m1_subset_1(esk1_3(esk3_0,k15_lattice3(esk3_0,X1),X2),u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_16])]),c_0_14])).

cnf(c_0_23,negated_conjecture,
    ( v4_lattice3(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_24,negated_conjecture,
    ( v10_lattices(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_25,plain,
    ( r3_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( r1_lattices(esk3_0,k15_lattice3(esk3_0,X1),k15_lattice3(esk3_0,X2))
    | m1_subset_1(esk1_3(esk3_0,k15_lattice3(esk3_0,X2),X1),u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23]),c_0_19]),c_0_24]),c_0_16])]),c_0_14])).

fof(c_0_27,plain,(
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

cnf(c_0_28,negated_conjecture,
    ( r3_lattices(esk3_0,k15_lattice3(esk3_0,X1),k15_lattice3(esk3_0,X2))
    | m1_subset_1(esk1_3(esk3_0,k15_lattice3(esk3_0,X2),X1),u1_struct_0(esk3_0))
    | ~ v9_lattices(esk3_0)
    | ~ v8_lattices(esk3_0)
    | ~ v6_lattices(esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_19]),c_0_19]),c_0_16])]),c_0_14])).

cnf(c_0_29,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_30,negated_conjecture,
    ( r3_lattices(esk3_0,k15_lattice3(esk3_0,X1),k15_lattice3(esk3_0,X2))
    | m1_subset_1(esk1_3(esk3_0,k15_lattice3(esk3_0,X2),X1),u1_struct_0(esk3_0))
    | ~ v9_lattices(esk3_0)
    | ~ v8_lattices(esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_24]),c_0_16])]),c_0_14])).

cnf(c_0_31,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( r3_lattices(esk3_0,k15_lattice3(esk3_0,X1),k15_lattice3(esk3_0,X2))
    | m1_subset_1(esk1_3(esk3_0,k15_lattice3(esk3_0,X2),X1),u1_struct_0(esk3_0))
    | ~ v9_lattices(esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_24]),c_0_16])]),c_0_14])).

cnf(c_0_33,plain,
    ( v9_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( ~ r3_lattices(esk3_0,k15_lattice3(esk3_0,esk4_0),k15_lattice3(esk3_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_35,negated_conjecture,
    ( r3_lattices(esk3_0,k15_lattice3(esk3_0,X1),k15_lattice3(esk3_0,X2))
    | m1_subset_1(esk1_3(esk3_0,k15_lattice3(esk3_0,X2),X1),u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_24]),c_0_16])]),c_0_14])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(esk6_1(X1),u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(esk1_3(esk3_0,k15_lattice3(esk3_0,esk5_0),esk4_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_38,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X3)
    | r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(esk6_1(esk1_3(esk3_0,k15_lattice3(esk3_0,esk5_0),esk4_0)),u1_struct_0(esk3_0))
    | ~ r2_hidden(esk1_3(esk3_0,k15_lattice3(esk3_0,esk5_0),esk4_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk1_3(esk3_0,k15_lattice3(esk3_0,X1),X2),X2)
    | r4_lattice3(esk3_0,k15_lattice3(esk3_0,X1),X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_19]),c_0_16])]),c_0_14])).

cnf(c_0_41,negated_conjecture,
    ( r4_lattice3(esk3_0,k15_lattice3(esk3_0,esk5_0),esk4_0)
    | m1_subset_1(esk6_1(esk1_3(esk3_0,k15_lattice3(esk3_0,esk5_0),esk4_0)),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

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
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_43,negated_conjecture,
    ( r1_lattices(esk3_0,k15_lattice3(esk3_0,esk4_0),k15_lattice3(esk3_0,esk5_0))
    | m1_subset_1(esk6_1(esk1_3(esk3_0,k15_lattice3(esk3_0,esk5_0),esk4_0)),u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_41]),c_0_23]),c_0_19]),c_0_24]),c_0_16])]),c_0_14])).

cnf(c_0_44,plain,
    ( v2_struct_0(X1)
    | r4_lattice3(X1,X2,X3)
    | X2 != k15_lattice3(X1,X3)
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(cn,[status(thm)],[c_0_42])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(esk6_1(esk1_3(esk3_0,k15_lattice3(esk3_0,esk5_0),esk4_0)),u1_struct_0(esk3_0))
    | ~ v9_lattices(esk3_0)
    | ~ v8_lattices(esk3_0)
    | ~ v6_lattices(esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_43]),c_0_19]),c_0_19]),c_0_16])]),c_0_34]),c_0_14])).

cnf(c_0_46,plain,
    ( r4_lattice3(X1,k15_lattice3(X1,X2),X2)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_44]),c_0_15])).

cnf(c_0_47,negated_conjecture,
    ( m1_subset_1(esk6_1(esk1_3(esk3_0,k15_lattice3(esk3_0,esk5_0),esk4_0)),u1_struct_0(esk3_0))
    | ~ v9_lattices(esk3_0)
    | ~ v8_lattices(esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_29]),c_0_24]),c_0_16])]),c_0_14])).

cnf(c_0_48,negated_conjecture,
    ( r3_lattices(esk3_0,X1,esk6_1(X1))
    | ~ r2_hidden(X1,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_49,plain,
    ( r1_lattices(X1,X4,X2)
    | v2_struct_0(X1)
    | ~ r4_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_50,negated_conjecture,
    ( r4_lattice3(esk3_0,k15_lattice3(esk3_0,X1),X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_23]),c_0_24]),c_0_16])]),c_0_14])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(esk6_1(esk1_3(esk3_0,k15_lattice3(esk3_0,esk5_0),esk4_0)),u1_struct_0(esk3_0))
    | ~ v9_lattices(esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_31]),c_0_24]),c_0_16])]),c_0_14])).

cnf(c_0_52,negated_conjecture,
    ( r3_lattices(esk3_0,esk1_3(esk3_0,k15_lattice3(esk3_0,esk5_0),esk4_0),esk6_1(esk1_3(esk3_0,k15_lattice3(esk3_0,esk5_0),esk4_0)))
    | ~ r2_hidden(esk1_3(esk3_0,k15_lattice3(esk3_0,esk5_0),esk4_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_37])).

cnf(c_0_53,negated_conjecture,
    ( r1_lattices(esk3_0,X1,k15_lattice3(esk3_0,X2))
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_19]),c_0_16])]),c_0_14])).

cnf(c_0_54,negated_conjecture,
    ( m1_subset_1(esk6_1(esk1_3(esk3_0,k15_lattice3(esk3_0,esk5_0),esk4_0)),u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_33]),c_0_24]),c_0_16])]),c_0_14])).

cnf(c_0_55,plain,
    ( r1_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_56,negated_conjecture,
    ( r3_lattices(esk3_0,esk1_3(esk3_0,k15_lattice3(esk3_0,esk5_0),esk4_0),esk6_1(esk1_3(esk3_0,k15_lattice3(esk3_0,esk5_0),esk4_0)))
    | r4_lattice3(esk3_0,k15_lattice3(esk3_0,esk5_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_40])).

cnf(c_0_57,negated_conjecture,
    ( r1_lattices(esk3_0,esk6_1(esk1_3(esk3_0,k15_lattice3(esk3_0,esk5_0),esk4_0)),k15_lattice3(esk3_0,X1))
    | ~ r2_hidden(esk6_1(esk1_3(esk3_0,k15_lattice3(esk3_0,esk5_0),esk4_0)),X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(esk6_1(X1),esk5_0)
    | ~ r2_hidden(X1,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_59,negated_conjecture,
    ( r1_lattices(esk3_0,esk1_3(esk3_0,k15_lattice3(esk3_0,esk5_0),esk4_0),esk6_1(esk1_3(esk3_0,k15_lattice3(esk3_0,esk5_0),esk4_0)))
    | r4_lattice3(esk3_0,k15_lattice3(esk3_0,esk5_0),esk4_0)
    | ~ v9_lattices(esk3_0)
    | ~ v8_lattices(esk3_0)
    | ~ v6_lattices(esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_54]),c_0_37]),c_0_16])]),c_0_14])).

fof(c_0_60,plain,(
    ! [X24,X25,X26,X27] :
      ( v2_struct_0(X24)
      | ~ v5_lattices(X24)
      | ~ l2_lattices(X24)
      | ~ m1_subset_1(X25,u1_struct_0(X24))
      | ~ m1_subset_1(X26,u1_struct_0(X24))
      | ~ m1_subset_1(X27,u1_struct_0(X24))
      | ~ r1_lattices(X24,X25,X26)
      | ~ r1_lattices(X24,X26,X27)
      | r1_lattices(X24,X25,X27) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t25_lattices])])])])).

cnf(c_0_61,negated_conjecture,
    ( r1_lattices(esk3_0,esk6_1(esk1_3(esk3_0,k15_lattice3(esk3_0,esk5_0),esk4_0)),k15_lattice3(esk3_0,esk5_0))
    | ~ r2_hidden(esk1_3(esk3_0,k15_lattice3(esk3_0,esk5_0),esk4_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_37])])).

cnf(c_0_62,negated_conjecture,
    ( r1_lattices(esk3_0,esk1_3(esk3_0,k15_lattice3(esk3_0,esk5_0),esk4_0),esk6_1(esk1_3(esk3_0,k15_lattice3(esk3_0,esk5_0),esk4_0)))
    | r4_lattice3(esk3_0,k15_lattice3(esk3_0,esk5_0),esk4_0)
    | ~ v9_lattices(esk3_0)
    | ~ v8_lattices(esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_29]),c_0_24]),c_0_16])]),c_0_14])).

cnf(c_0_63,plain,
    ( v2_struct_0(X1)
    | r1_lattices(X1,X2,X4)
    | ~ v5_lattices(X1)
    | ~ l2_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r1_lattices(X1,X2,X3)
    | ~ r1_lattices(X1,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_64,negated_conjecture,
    ( r1_lattices(esk3_0,esk6_1(esk1_3(esk3_0,k15_lattice3(esk3_0,esk5_0),esk4_0)),k15_lattice3(esk3_0,esk5_0))
    | r4_lattice3(esk3_0,k15_lattice3(esk3_0,esk5_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_40])).

cnf(c_0_65,negated_conjecture,
    ( r1_lattices(esk3_0,esk1_3(esk3_0,k15_lattice3(esk3_0,esk5_0),esk4_0),esk6_1(esk1_3(esk3_0,k15_lattice3(esk3_0,esk5_0),esk4_0)))
    | r4_lattice3(esk3_0,k15_lattice3(esk3_0,esk5_0),esk4_0)
    | ~ v9_lattices(esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_31]),c_0_24]),c_0_16])]),c_0_14])).

cnf(c_0_66,negated_conjecture,
    ( r1_lattices(esk3_0,X1,k15_lattice3(esk3_0,esk5_0))
    | r4_lattice3(esk3_0,k15_lattice3(esk3_0,esk5_0),esk4_0)
    | ~ l2_lattices(esk3_0)
    | ~ r1_lattices(esk3_0,X1,esk6_1(esk1_3(esk3_0,k15_lattice3(esk3_0,esk5_0),esk4_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ v5_lattices(esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_19]),c_0_54])]),c_0_14])).

cnf(c_0_67,negated_conjecture,
    ( r1_lattices(esk3_0,esk1_3(esk3_0,k15_lattice3(esk3_0,esk5_0),esk4_0),esk6_1(esk1_3(esk3_0,k15_lattice3(esk3_0,esk5_0),esk4_0)))
    | r4_lattice3(esk3_0,k15_lattice3(esk3_0,esk5_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_33]),c_0_24]),c_0_16])]),c_0_14])).

fof(c_0_68,plain,(
    ! [X20] :
      ( ( l1_lattices(X20)
        | ~ l3_lattices(X20) )
      & ( l2_lattices(X20)
        | ~ l3_lattices(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).

cnf(c_0_69,negated_conjecture,
    ( r1_lattices(esk3_0,esk1_3(esk3_0,k15_lattice3(esk3_0,esk5_0),esk4_0),k15_lattice3(esk3_0,esk5_0))
    | r4_lattice3(esk3_0,k15_lattice3(esk3_0,esk5_0),esk4_0)
    | ~ l2_lattices(esk3_0)
    | ~ v5_lattices(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_37])])).

cnf(c_0_70,plain,
    ( l2_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_71,negated_conjecture,
    ( r1_lattices(esk3_0,esk1_3(esk3_0,k15_lattice3(esk3_0,esk5_0),esk4_0),k15_lattice3(esk3_0,esk5_0))
    | r4_lattice3(esk3_0,k15_lattice3(esk3_0,esk5_0),esk4_0)
    | ~ v5_lattices(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_16])])).

cnf(c_0_72,plain,
    ( v5_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_73,plain,
    ( r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,esk1_3(X1,X2,X3),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_74,negated_conjecture,
    ( r1_lattices(esk3_0,esk1_3(esk3_0,k15_lattice3(esk3_0,esk5_0),esk4_0),k15_lattice3(esk3_0,esk5_0))
    | r4_lattice3(esk3_0,k15_lattice3(esk3_0,esk5_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_24]),c_0_16])]),c_0_14])).

cnf(c_0_75,negated_conjecture,
    ( r4_lattice3(esk3_0,k15_lattice3(esk3_0,esk5_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_19]),c_0_16])]),c_0_14])).

cnf(c_0_76,negated_conjecture,
    ( r1_lattices(esk3_0,k15_lattice3(esk3_0,esk4_0),k15_lattice3(esk3_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_75]),c_0_23]),c_0_19]),c_0_24]),c_0_16])]),c_0_14])).

cnf(c_0_77,negated_conjecture,
    ( ~ v9_lattices(esk3_0)
    | ~ v8_lattices(esk3_0)
    | ~ v6_lattices(esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_76]),c_0_19]),c_0_19]),c_0_16])]),c_0_34]),c_0_14])).

cnf(c_0_78,negated_conjecture,
    ( ~ v9_lattices(esk3_0)
    | ~ v8_lattices(esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_29]),c_0_24]),c_0_16])]),c_0_14])).

cnf(c_0_79,negated_conjecture,
    ( ~ v9_lattices(esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_31]),c_0_24]),c_0_16])]),c_0_14])).

cnf(c_0_80,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_33]),c_0_24]),c_0_16])]),c_0_14]),
    [proof]).

%------------------------------------------------------------------------------
