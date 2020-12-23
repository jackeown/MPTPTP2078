%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:10 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 162 expanded)
%              Number of clauses        :   42 (  60 expanded)
%              Number of leaves         :    8 (  41 expanded)
%              Depth                    :   12
%              Number of atoms          :  538 (1631 expanded)
%              Number of equality atoms :   24 (  96 expanded)
%              Maximal formula depth    :   23 (   9 average)
%              Maximal clause size      :   65 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(dt_k4_filter_0,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & l3_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k4_filter_0(X1,X2,X3),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_filter_0)).

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

fof(t41_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v4_lattice3(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( ( r2_hidden(X2,X3)
                & r4_lattice3(X1,X2,X3) )
             => k15_lattice3(X1,X3) = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_lattice3)).

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

fof(c_0_8,plain,(
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

cnf(c_0_9,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_10,plain,(
    ! [X16,X17,X18] :
      ( v2_struct_0(X16)
      | ~ v10_lattices(X16)
      | ~ l3_lattices(X16)
      | ~ m1_subset_1(X17,u1_struct_0(X16))
      | ~ m1_subset_1(X18,u1_struct_0(X16))
      | m1_subset_1(k4_filter_0(X16,X17,X18),u1_struct_0(X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_filter_0])])])).

fof(c_0_11,plain,(
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

fof(c_0_12,plain,(
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

cnf(c_0_13,plain,
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
    inference(cn,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k4_filter_0(X1,X2,X3),u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_15,plain,(
    ! [X25,X26,X27,X28,X30] :
      ( ( m1_subset_1(esk3_4(X25,X26,X27,X28),u1_struct_0(X26))
        | ~ r2_hidden(X25,a_3_6_lattice3(X26,X27,X28))
        | v2_struct_0(X26)
        | ~ v10_lattices(X26)
        | ~ v4_lattice3(X26)
        | ~ l3_lattices(X26)
        | ~ m1_subset_1(X27,u1_struct_0(X26))
        | ~ m1_subset_1(X28,u1_struct_0(X26)) )
      & ( X25 = esk3_4(X25,X26,X27,X28)
        | ~ r2_hidden(X25,a_3_6_lattice3(X26,X27,X28))
        | v2_struct_0(X26)
        | ~ v10_lattices(X26)
        | ~ v4_lattice3(X26)
        | ~ l3_lattices(X26)
        | ~ m1_subset_1(X27,u1_struct_0(X26))
        | ~ m1_subset_1(X28,u1_struct_0(X26)) )
      & ( r3_lattices(X26,k4_lattices(X26,X27,esk3_4(X25,X26,X27,X28)),X28)
        | ~ r2_hidden(X25,a_3_6_lattice3(X26,X27,X28))
        | v2_struct_0(X26)
        | ~ v10_lattices(X26)
        | ~ v4_lattice3(X26)
        | ~ l3_lattices(X26)
        | ~ m1_subset_1(X27,u1_struct_0(X26))
        | ~ m1_subset_1(X28,u1_struct_0(X26)) )
      & ( ~ m1_subset_1(X30,u1_struct_0(X26))
        | X25 != X30
        | ~ r3_lattices(X26,k4_lattices(X26,X27,X30),X28)
        | r2_hidden(X25,a_3_6_lattice3(X26,X27,X28))
        | v2_struct_0(X26)
        | ~ v10_lattices(X26)
        | ~ v4_lattice3(X26)
        | ~ l3_lattices(X26)
        | ~ m1_subset_1(X27,u1_struct_0(X26))
        | ~ m1_subset_1(X28,u1_struct_0(X26)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_3_6_lattice3])])])])])])).

cnf(c_0_16,plain,
    ( r1_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( v9_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_20,plain,(
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

cnf(c_0_21,plain,
    ( r3_lattices(X1,X2,k4_filter_0(X1,X3,X4))
    | v2_struct_0(X1)
    | ~ v3_filter_0(X1)
    | ~ r3_lattices(X1,k4_lattices(X1,X3,X2),X4)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_13]),c_0_14])).

cnf(c_0_22,plain,
    ( r3_lattices(X1,k4_lattices(X1,X2,esk3_4(X3,X1,X2,X4)),X4)
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,a_3_6_lattice3(X1,X2,X4))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( m1_subset_1(esk3_4(X1,X2,X3,X4),u1_struct_0(X2))
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_3_6_lattice3(X2,X3,X4))
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( r1_lattices(X1,X2,k4_filter_0(X1,X3,X4))
    | v2_struct_0(X1)
    | ~ r3_lattices(X1,X2,k4_filter_0(X1,X3,X4))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_14]),c_0_17]),c_0_18]),c_0_19])).

cnf(c_0_25,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X1))
    | r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( r3_lattices(X1,esk3_4(X2,X1,X3,X4),k4_filter_0(X1,X3,X4))
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ r2_hidden(X2,a_3_6_lattice3(X1,X3,X4))
    | ~ v3_filter_0(X1)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])).

cnf(c_0_27,plain,
    ( X1 = esk3_4(X1,X2,X3,X4)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_3_6_lattice3(X2,X3,X4))
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_28,plain,(
    ! [X31,X32,X33] :
      ( v2_struct_0(X31)
      | ~ v10_lattices(X31)
      | ~ v4_lattice3(X31)
      | ~ l3_lattices(X31)
      | ~ m1_subset_1(X32,u1_struct_0(X31))
      | ~ r2_hidden(X32,X33)
      | ~ r4_lattice3(X31,X32,X33)
      | k15_lattice3(X31,X33) = X32 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t41_lattice3])])])])).

cnf(c_0_29,plain,
    ( r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,esk2_3(X1,X2,X3),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( r4_lattice3(X1,X2,X3)
    | r1_lattices(X1,esk2_3(X1,X2,X3),k4_filter_0(X1,X4,X5))
    | v2_struct_0(X1)
    | ~ r3_lattices(X1,esk2_3(X1,X2,X3),k4_filter_0(X1,X4,X5))
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_31,plain,
    ( r3_lattices(X1,X2,k4_filter_0(X1,X3,X4))
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ r2_hidden(X2,a_3_6_lattice3(X1,X3,X4))
    | ~ v3_filter_0(X1)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_32,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X3)
    | r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_33,negated_conjecture,(
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

cnf(c_0_34,plain,
    ( v2_struct_0(X1)
    | k15_lattice3(X1,X3) = X2
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,X3)
    | ~ r4_lattice3(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,plain,
    ( r4_lattice3(X1,k4_filter_0(X1,X2,X3),X4)
    | v2_struct_0(X1)
    | ~ r3_lattices(X1,esk2_3(X1,k4_filter_0(X1,X2,X3),X4),k4_filter_0(X1,X2,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_14])).

cnf(c_0_36,plain,
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
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

fof(c_0_37,negated_conjecture,
    ( ~ v2_struct_0(esk4_0)
    & v10_lattices(esk4_0)
    & v4_lattice3(esk4_0)
    & l3_lattices(esk4_0)
    & m1_subset_1(esk5_0,u1_struct_0(esk4_0))
    & m1_subset_1(esk6_0,u1_struct_0(esk4_0))
    & ~ v2_struct_0(esk4_0)
    & v10_lattices(esk4_0)
    & v3_filter_0(esk4_0)
    & l3_lattices(esk4_0)
    & k4_filter_0(esk4_0,esk5_0,esk6_0) != k15_lattice3(esk4_0,a_3_6_lattice3(esk4_0,esk5_0,esk6_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_33])])])])).

cnf(c_0_38,plain,
    ( k15_lattice3(X1,X2) = k4_filter_0(X1,X3,X4)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ r2_hidden(k4_filter_0(X1,X3,X4),X2)
    | ~ r4_lattice3(X1,k4_filter_0(X1,X3,X4),X2)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_14])).

cnf(c_0_39,plain,
    ( r4_lattice3(X1,k4_filter_0(X1,X2,X3),a_3_6_lattice3(X1,X2,X3))
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v3_filter_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_14])).

cnf(c_0_40,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_41,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_42,negated_conjecture,
    ( k4_filter_0(esk4_0,esk5_0,esk6_0) != k15_lattice3(esk4_0,a_3_6_lattice3(esk4_0,esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_43,plain,
    ( k15_lattice3(X1,a_3_6_lattice3(X1,X2,X3)) = k4_filter_0(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ r2_hidden(k4_filter_0(X1,X2,X3),a_3_6_lattice3(X1,X2,X3))
    | ~ v3_filter_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( v4_lattice3(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_45,negated_conjecture,
    ( v3_filter_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_47,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_48,negated_conjecture,
    ( v10_lattices(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_49,negated_conjecture,
    ( l3_lattices(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_50,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_51,plain,
    ( r2_hidden(X1,a_3_6_lattice3(X2,X3,X4))
    | v2_struct_0(X2)
    | ~ v4_lattice3(X2)
    | ~ r3_lattices(X2,k4_lattices(X2,X3,X1),X4)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(er,[status(thm)],[c_0_40])).

cnf(c_0_52,plain,
    ( v2_struct_0(X1)
    | r3_lattices(X1,k4_lattices(X1,X2,X3),X4)
    | X3 != k4_filter_0(X1,X2,X4)
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1)
    | ~ v3_filter_0(X1)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(cn,[status(thm)],[c_0_41])).

cnf(c_0_53,negated_conjecture,
    ( ~ r2_hidden(k4_filter_0(esk4_0,esk5_0,esk6_0),a_3_6_lattice3(esk4_0,esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44]),c_0_45]),c_0_46]),c_0_47]),c_0_48]),c_0_49])]),c_0_50])).

cnf(c_0_54,plain,
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
    inference(spm,[status(thm)],[c_0_51,c_0_14])).

cnf(c_0_55,plain,
    ( r3_lattices(X1,k4_lattices(X1,X2,k4_filter_0(X1,X2,X3)),X3)
    | v2_struct_0(X1)
    | ~ v3_filter_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_52]),c_0_14])).

cnf(c_0_56,negated_conjecture,
    ( ~ r3_lattices(esk4_0,k4_lattices(esk4_0,esk5_0,k4_filter_0(esk4_0,esk5_0,esk6_0)),esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_44]),c_0_46]),c_0_47]),c_0_48]),c_0_49])]),c_0_50])).

cnf(c_0_57,negated_conjecture,
    ( r3_lattices(esk4_0,k4_lattices(esk4_0,X1,k4_filter_0(esk4_0,X1,X2)),X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_45]),c_0_48]),c_0_49])]),c_0_50])).

cnf(c_0_58,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_46]),c_0_47])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:00:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.40  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S5PRR_S0Y
% 0.19/0.40  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.40  #
% 0.19/0.40  # Preprocessing time       : 0.030 s
% 0.19/0.40  # Presaturation interreduction done
% 0.19/0.40  
% 0.19/0.40  # Proof found!
% 0.19/0.40  # SZS status Theorem
% 0.19/0.40  # SZS output start CNFRefutation
% 0.19/0.40  fof(d8_filter_0, axiom, ![X1]:(((~(v2_struct_0(X1))&v10_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>((((~(v2_struct_0(X1))&v10_lattices(X1))&v3_filter_0(X1))&l3_lattices(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(X4=k4_filter_0(X1,X2,X3)<=>(r3_lattices(X1,k4_lattices(X1,X2,X4),X3)&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>(r3_lattices(X1,k4_lattices(X1,X2,X5),X3)=>r3_lattices(X1,X5,X4)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_filter_0)).
% 0.19/0.40  fof(dt_k4_filter_0, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v10_lattices(X1))&l3_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>m1_subset_1(k4_filter_0(X1,X2,X3),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_filter_0)).
% 0.19/0.40  fof(redefinition_r3_lattices, axiom, ![X1, X2, X3]:(((((((~(v2_struct_0(X1))&v6_lattices(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>(r3_lattices(X1,X2,X3)<=>r1_lattices(X1,X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 0.19/0.40  fof(cc1_lattices, axiom, ![X1]:(l3_lattices(X1)=>((~(v2_struct_0(X1))&v10_lattices(X1))=>((((((~(v2_struct_0(X1))&v4_lattices(X1))&v5_lattices(X1))&v6_lattices(X1))&v7_lattices(X1))&v8_lattices(X1))&v9_lattices(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattices)).
% 0.19/0.40  fof(fraenkel_a_3_6_lattice3, axiom, ![X1, X2, X3, X4]:((((((~(v2_struct_0(X2))&v10_lattices(X2))&v4_lattice3(X2))&l3_lattices(X2))&m1_subset_1(X3,u1_struct_0(X2)))&m1_subset_1(X4,u1_struct_0(X2)))=>(r2_hidden(X1,a_3_6_lattice3(X2,X3,X4))<=>?[X5]:((m1_subset_1(X5,u1_struct_0(X2))&X1=X5)&r3_lattices(X2,k4_lattices(X2,X3,X5),X4)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_3_6_lattice3)).
% 0.19/0.40  fof(d17_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(r4_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X3)=>r1_lattices(X1,X4,X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d17_lattice3)).
% 0.19/0.40  fof(t41_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:((r2_hidden(X2,X3)&r4_lattice3(X1,X2,X3))=>k15_lattice3(X1,X3)=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_lattice3)).
% 0.19/0.40  fof(t52_lattice3, conjecture, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>((((~(v2_struct_0(X1))&v10_lattices(X1))&v3_filter_0(X1))&l3_lattices(X1))=>k4_filter_0(X1,X2,X3)=k15_lattice3(X1,a_3_6_lattice3(X1,X2,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_lattice3)).
% 0.19/0.40  fof(c_0_8, plain, ![X10, X11, X12, X13, X14]:(((r3_lattices(X10,k4_lattices(X10,X11,X13),X12)|X13!=k4_filter_0(X10,X11,X12)|~m1_subset_1(X13,u1_struct_0(X10))|(v2_struct_0(X10)|~v10_lattices(X10)|~v3_filter_0(X10)|~l3_lattices(X10))|~m1_subset_1(X12,u1_struct_0(X10))|~m1_subset_1(X11,u1_struct_0(X10))|(v2_struct_0(X10)|~v10_lattices(X10)|~l3_lattices(X10)))&(~m1_subset_1(X14,u1_struct_0(X10))|(~r3_lattices(X10,k4_lattices(X10,X11,X14),X12)|r3_lattices(X10,X14,X13))|X13!=k4_filter_0(X10,X11,X12)|~m1_subset_1(X13,u1_struct_0(X10))|(v2_struct_0(X10)|~v10_lattices(X10)|~v3_filter_0(X10)|~l3_lattices(X10))|~m1_subset_1(X12,u1_struct_0(X10))|~m1_subset_1(X11,u1_struct_0(X10))|(v2_struct_0(X10)|~v10_lattices(X10)|~l3_lattices(X10))))&((m1_subset_1(esk1_4(X10,X11,X12,X13),u1_struct_0(X10))|~r3_lattices(X10,k4_lattices(X10,X11,X13),X12)|X13=k4_filter_0(X10,X11,X12)|~m1_subset_1(X13,u1_struct_0(X10))|(v2_struct_0(X10)|~v10_lattices(X10)|~v3_filter_0(X10)|~l3_lattices(X10))|~m1_subset_1(X12,u1_struct_0(X10))|~m1_subset_1(X11,u1_struct_0(X10))|(v2_struct_0(X10)|~v10_lattices(X10)|~l3_lattices(X10)))&((r3_lattices(X10,k4_lattices(X10,X11,esk1_4(X10,X11,X12,X13)),X12)|~r3_lattices(X10,k4_lattices(X10,X11,X13),X12)|X13=k4_filter_0(X10,X11,X12)|~m1_subset_1(X13,u1_struct_0(X10))|(v2_struct_0(X10)|~v10_lattices(X10)|~v3_filter_0(X10)|~l3_lattices(X10))|~m1_subset_1(X12,u1_struct_0(X10))|~m1_subset_1(X11,u1_struct_0(X10))|(v2_struct_0(X10)|~v10_lattices(X10)|~l3_lattices(X10)))&(~r3_lattices(X10,esk1_4(X10,X11,X12,X13),X13)|~r3_lattices(X10,k4_lattices(X10,X11,X13),X12)|X13=k4_filter_0(X10,X11,X12)|~m1_subset_1(X13,u1_struct_0(X10))|(v2_struct_0(X10)|~v10_lattices(X10)|~v3_filter_0(X10)|~l3_lattices(X10))|~m1_subset_1(X12,u1_struct_0(X10))|~m1_subset_1(X11,u1_struct_0(X10))|(v2_struct_0(X10)|~v10_lattices(X10)|~l3_lattices(X10)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d8_filter_0])])])])])])).
% 0.19/0.40  cnf(c_0_9, plain, (r3_lattices(X2,X1,X5)|v2_struct_0(X2)|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~r3_lattices(X2,k4_lattices(X2,X3,X1),X4)|X5!=k4_filter_0(X2,X3,X4)|~m1_subset_1(X5,u1_struct_0(X2))|~v10_lattices(X2)|~v3_filter_0(X2)|~l3_lattices(X2)|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X3,u1_struct_0(X2))|~v10_lattices(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.40  fof(c_0_10, plain, ![X16, X17, X18]:(v2_struct_0(X16)|~v10_lattices(X16)|~l3_lattices(X16)|~m1_subset_1(X17,u1_struct_0(X16))|~m1_subset_1(X18,u1_struct_0(X16))|m1_subset_1(k4_filter_0(X16,X17,X18),u1_struct_0(X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_filter_0])])])).
% 0.19/0.40  fof(c_0_11, plain, ![X7, X8, X9]:((~r3_lattices(X7,X8,X9)|r1_lattices(X7,X8,X9)|(v2_struct_0(X7)|~v6_lattices(X7)|~v8_lattices(X7)|~v9_lattices(X7)|~l3_lattices(X7)|~m1_subset_1(X8,u1_struct_0(X7))|~m1_subset_1(X9,u1_struct_0(X7))))&(~r1_lattices(X7,X8,X9)|r3_lattices(X7,X8,X9)|(v2_struct_0(X7)|~v6_lattices(X7)|~v8_lattices(X7)|~v9_lattices(X7)|~l3_lattices(X7)|~m1_subset_1(X8,u1_struct_0(X7))|~m1_subset_1(X9,u1_struct_0(X7))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).
% 0.19/0.40  fof(c_0_12, plain, ![X6]:(((((((~v2_struct_0(X6)|(v2_struct_0(X6)|~v10_lattices(X6))|~l3_lattices(X6))&(v4_lattices(X6)|(v2_struct_0(X6)|~v10_lattices(X6))|~l3_lattices(X6)))&(v5_lattices(X6)|(v2_struct_0(X6)|~v10_lattices(X6))|~l3_lattices(X6)))&(v6_lattices(X6)|(v2_struct_0(X6)|~v10_lattices(X6))|~l3_lattices(X6)))&(v7_lattices(X6)|(v2_struct_0(X6)|~v10_lattices(X6))|~l3_lattices(X6)))&(v8_lattices(X6)|(v2_struct_0(X6)|~v10_lattices(X6))|~l3_lattices(X6)))&(v9_lattices(X6)|(v2_struct_0(X6)|~v10_lattices(X6))|~l3_lattices(X6))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).
% 0.19/0.40  cnf(c_0_13, plain, (v2_struct_0(X2)|r3_lattices(X2,X1,X5)|X5!=k4_filter_0(X2,X3,X4)|~l3_lattices(X2)|~v10_lattices(X2)|~v3_filter_0(X2)|~m1_subset_1(X5,u1_struct_0(X2))|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X3,u1_struct_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))|~r3_lattices(X2,k4_lattices(X2,X3,X1),X4)), inference(cn,[status(thm)],[c_0_9])).
% 0.19/0.40  cnf(c_0_14, plain, (v2_struct_0(X1)|m1_subset_1(k4_filter_0(X1,X2,X3),u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.40  fof(c_0_15, plain, ![X25, X26, X27, X28, X30]:((((m1_subset_1(esk3_4(X25,X26,X27,X28),u1_struct_0(X26))|~r2_hidden(X25,a_3_6_lattice3(X26,X27,X28))|(v2_struct_0(X26)|~v10_lattices(X26)|~v4_lattice3(X26)|~l3_lattices(X26)|~m1_subset_1(X27,u1_struct_0(X26))|~m1_subset_1(X28,u1_struct_0(X26))))&(X25=esk3_4(X25,X26,X27,X28)|~r2_hidden(X25,a_3_6_lattice3(X26,X27,X28))|(v2_struct_0(X26)|~v10_lattices(X26)|~v4_lattice3(X26)|~l3_lattices(X26)|~m1_subset_1(X27,u1_struct_0(X26))|~m1_subset_1(X28,u1_struct_0(X26)))))&(r3_lattices(X26,k4_lattices(X26,X27,esk3_4(X25,X26,X27,X28)),X28)|~r2_hidden(X25,a_3_6_lattice3(X26,X27,X28))|(v2_struct_0(X26)|~v10_lattices(X26)|~v4_lattice3(X26)|~l3_lattices(X26)|~m1_subset_1(X27,u1_struct_0(X26))|~m1_subset_1(X28,u1_struct_0(X26)))))&(~m1_subset_1(X30,u1_struct_0(X26))|X25!=X30|~r3_lattices(X26,k4_lattices(X26,X27,X30),X28)|r2_hidden(X25,a_3_6_lattice3(X26,X27,X28))|(v2_struct_0(X26)|~v10_lattices(X26)|~v4_lattice3(X26)|~l3_lattices(X26)|~m1_subset_1(X27,u1_struct_0(X26))|~m1_subset_1(X28,u1_struct_0(X26))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_3_6_lattice3])])])])])])).
% 0.19/0.40  cnf(c_0_16, plain, (r1_lattices(X1,X2,X3)|v2_struct_0(X1)|~r3_lattices(X1,X2,X3)|~v6_lattices(X1)|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.40  cnf(c_0_17, plain, (v6_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.40  cnf(c_0_18, plain, (v8_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.40  cnf(c_0_19, plain, (v9_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.40  fof(c_0_20, plain, ![X19, X20, X21, X22, X23]:((~r4_lattice3(X19,X20,X21)|(~m1_subset_1(X22,u1_struct_0(X19))|(~r2_hidden(X22,X21)|r1_lattices(X19,X22,X20)))|~m1_subset_1(X20,u1_struct_0(X19))|(v2_struct_0(X19)|~l3_lattices(X19)))&((m1_subset_1(esk2_3(X19,X20,X23),u1_struct_0(X19))|r4_lattice3(X19,X20,X23)|~m1_subset_1(X20,u1_struct_0(X19))|(v2_struct_0(X19)|~l3_lattices(X19)))&((r2_hidden(esk2_3(X19,X20,X23),X23)|r4_lattice3(X19,X20,X23)|~m1_subset_1(X20,u1_struct_0(X19))|(v2_struct_0(X19)|~l3_lattices(X19)))&(~r1_lattices(X19,esk2_3(X19,X20,X23),X20)|r4_lattice3(X19,X20,X23)|~m1_subset_1(X20,u1_struct_0(X19))|(v2_struct_0(X19)|~l3_lattices(X19)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_lattice3])])])])])])])).
% 0.19/0.40  cnf(c_0_21, plain, (r3_lattices(X1,X2,k4_filter_0(X1,X3,X4))|v2_struct_0(X1)|~v3_filter_0(X1)|~r3_lattices(X1,k4_lattices(X1,X3,X2),X4)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_13]), c_0_14])).
% 0.19/0.40  cnf(c_0_22, plain, (r3_lattices(X1,k4_lattices(X1,X2,esk3_4(X3,X1,X2,X4)),X4)|v2_struct_0(X1)|~r2_hidden(X3,a_3_6_lattice3(X1,X2,X4))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.40  cnf(c_0_23, plain, (m1_subset_1(esk3_4(X1,X2,X3,X4),u1_struct_0(X2))|v2_struct_0(X2)|~r2_hidden(X1,a_3_6_lattice3(X2,X3,X4))|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)|~m1_subset_1(X3,u1_struct_0(X2))|~m1_subset_1(X4,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.40  cnf(c_0_24, plain, (r1_lattices(X1,X2,k4_filter_0(X1,X3,X4))|v2_struct_0(X1)|~r3_lattices(X1,X2,k4_filter_0(X1,X3,X4))|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_14]), c_0_17]), c_0_18]), c_0_19])).
% 0.19/0.40  cnf(c_0_25, plain, (m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X1))|r4_lattice3(X1,X2,X3)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.40  cnf(c_0_26, plain, (r3_lattices(X1,esk3_4(X2,X1,X3,X4),k4_filter_0(X1,X3,X4))|v2_struct_0(X1)|~v4_lattice3(X1)|~r2_hidden(X2,a_3_6_lattice3(X1,X3,X4))|~v3_filter_0(X1)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23])).
% 0.19/0.40  cnf(c_0_27, plain, (X1=esk3_4(X1,X2,X3,X4)|v2_struct_0(X2)|~r2_hidden(X1,a_3_6_lattice3(X2,X3,X4))|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)|~m1_subset_1(X3,u1_struct_0(X2))|~m1_subset_1(X4,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.40  fof(c_0_28, plain, ![X31, X32, X33]:(v2_struct_0(X31)|~v10_lattices(X31)|~v4_lattice3(X31)|~l3_lattices(X31)|(~m1_subset_1(X32,u1_struct_0(X31))|(~r2_hidden(X32,X33)|~r4_lattice3(X31,X32,X33)|k15_lattice3(X31,X33)=X32))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t41_lattice3])])])])).
% 0.19/0.40  cnf(c_0_29, plain, (r4_lattice3(X1,X2,X3)|v2_struct_0(X1)|~r1_lattices(X1,esk2_3(X1,X2,X3),X2)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.40  cnf(c_0_30, plain, (r4_lattice3(X1,X2,X3)|r1_lattices(X1,esk2_3(X1,X2,X3),k4_filter_0(X1,X4,X5))|v2_struct_0(X1)|~r3_lattices(X1,esk2_3(X1,X2,X3),k4_filter_0(X1,X4,X5))|~m1_subset_1(X5,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.19/0.40  cnf(c_0_31, plain, (r3_lattices(X1,X2,k4_filter_0(X1,X3,X4))|v2_struct_0(X1)|~v4_lattice3(X1)|~r2_hidden(X2,a_3_6_lattice3(X1,X3,X4))|~v3_filter_0(X1)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.19/0.40  cnf(c_0_32, plain, (r2_hidden(esk2_3(X1,X2,X3),X3)|r4_lattice3(X1,X2,X3)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.40  fof(c_0_33, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>((((~(v2_struct_0(X1))&v10_lattices(X1))&v3_filter_0(X1))&l3_lattices(X1))=>k4_filter_0(X1,X2,X3)=k15_lattice3(X1,a_3_6_lattice3(X1,X2,X3))))))), inference(assume_negation,[status(cth)],[t52_lattice3])).
% 0.19/0.40  cnf(c_0_34, plain, (v2_struct_0(X1)|k15_lattice3(X1,X3)=X2|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~r2_hidden(X2,X3)|~r4_lattice3(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.40  cnf(c_0_35, plain, (r4_lattice3(X1,k4_filter_0(X1,X2,X3),X4)|v2_struct_0(X1)|~r3_lattices(X1,esk2_3(X1,k4_filter_0(X1,X2,X3),X4),k4_filter_0(X1,X2,X3))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_14])).
% 0.19/0.40  cnf(c_0_36, plain, (r4_lattice3(X1,X2,a_3_6_lattice3(X3,X4,X5))|r3_lattices(X3,esk2_3(X1,X2,a_3_6_lattice3(X3,X4,X5)),k4_filter_0(X3,X4,X5))|v2_struct_0(X1)|v2_struct_0(X3)|~v4_lattice3(X3)|~v3_filter_0(X3)|~m1_subset_1(X5,u1_struct_0(X3))|~m1_subset_1(X4,u1_struct_0(X3))|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X3)|~l3_lattices(X3)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.19/0.40  fof(c_0_37, negated_conjecture, ((((~v2_struct_0(esk4_0)&v10_lattices(esk4_0))&v4_lattice3(esk4_0))&l3_lattices(esk4_0))&(m1_subset_1(esk5_0,u1_struct_0(esk4_0))&(m1_subset_1(esk6_0,u1_struct_0(esk4_0))&((((~v2_struct_0(esk4_0)&v10_lattices(esk4_0))&v3_filter_0(esk4_0))&l3_lattices(esk4_0))&k4_filter_0(esk4_0,esk5_0,esk6_0)!=k15_lattice3(esk4_0,a_3_6_lattice3(esk4_0,esk5_0,esk6_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_33])])])])).
% 0.19/0.40  cnf(c_0_38, plain, (k15_lattice3(X1,X2)=k4_filter_0(X1,X3,X4)|v2_struct_0(X1)|~v4_lattice3(X1)|~r2_hidden(k4_filter_0(X1,X3,X4),X2)|~r4_lattice3(X1,k4_filter_0(X1,X3,X4),X2)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_34, c_0_14])).
% 0.19/0.40  cnf(c_0_39, plain, (r4_lattice3(X1,k4_filter_0(X1,X2,X3),a_3_6_lattice3(X1,X2,X3))|v2_struct_0(X1)|~v4_lattice3(X1)|~v3_filter_0(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_14])).
% 0.19/0.40  cnf(c_0_40, plain, (r2_hidden(X3,a_3_6_lattice3(X2,X4,X5))|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|X3!=X1|~r3_lattices(X2,k4_lattices(X2,X4,X1),X5)|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X5,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.40  cnf(c_0_41, plain, (r3_lattices(X1,k4_lattices(X1,X2,X3),X4)|v2_struct_0(X1)|v2_struct_0(X1)|X3!=k4_filter_0(X1,X2,X4)|~m1_subset_1(X3,u1_struct_0(X1))|~v10_lattices(X1)|~v3_filter_0(X1)|~l3_lattices(X1)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.40  cnf(c_0_42, negated_conjecture, (k4_filter_0(esk4_0,esk5_0,esk6_0)!=k15_lattice3(esk4_0,a_3_6_lattice3(esk4_0,esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.40  cnf(c_0_43, plain, (k15_lattice3(X1,a_3_6_lattice3(X1,X2,X3))=k4_filter_0(X1,X2,X3)|v2_struct_0(X1)|~v4_lattice3(X1)|~r2_hidden(k4_filter_0(X1,X2,X3),a_3_6_lattice3(X1,X2,X3))|~v3_filter_0(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.19/0.40  cnf(c_0_44, negated_conjecture, (v4_lattice3(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.40  cnf(c_0_45, negated_conjecture, (v3_filter_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.40  cnf(c_0_46, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.40  cnf(c_0_47, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.40  cnf(c_0_48, negated_conjecture, (v10_lattices(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.40  cnf(c_0_49, negated_conjecture, (l3_lattices(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.40  cnf(c_0_50, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.40  cnf(c_0_51, plain, (r2_hidden(X1,a_3_6_lattice3(X2,X3,X4))|v2_struct_0(X2)|~v4_lattice3(X2)|~r3_lattices(X2,k4_lattices(X2,X3,X1),X4)|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X3,u1_struct_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))|~v10_lattices(X2)|~l3_lattices(X2)), inference(er,[status(thm)],[c_0_40])).
% 0.19/0.40  cnf(c_0_52, plain, (v2_struct_0(X1)|r3_lattices(X1,k4_lattices(X1,X2,X3),X4)|X3!=k4_filter_0(X1,X2,X4)|~l3_lattices(X1)|~v10_lattices(X1)|~v3_filter_0(X1)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))), inference(cn,[status(thm)],[c_0_41])).
% 0.19/0.40  cnf(c_0_53, negated_conjecture, (~r2_hidden(k4_filter_0(esk4_0,esk5_0,esk6_0),a_3_6_lattice3(esk4_0,esk5_0,esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44]), c_0_45]), c_0_46]), c_0_47]), c_0_48]), c_0_49])]), c_0_50])).
% 0.19/0.40  cnf(c_0_54, plain, (r2_hidden(k4_filter_0(X1,X2,X3),a_3_6_lattice3(X1,X4,X5))|v2_struct_0(X1)|~v4_lattice3(X1)|~r3_lattices(X1,k4_lattices(X1,X4,k4_filter_0(X1,X2,X3)),X5)|~m1_subset_1(X5,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_51, c_0_14])).
% 0.19/0.40  cnf(c_0_55, plain, (r3_lattices(X1,k4_lattices(X1,X2,k4_filter_0(X1,X2,X3)),X3)|v2_struct_0(X1)|~v3_filter_0(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_52]), c_0_14])).
% 0.19/0.40  cnf(c_0_56, negated_conjecture, (~r3_lattices(esk4_0,k4_lattices(esk4_0,esk5_0,k4_filter_0(esk4_0,esk5_0,esk6_0)),esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_44]), c_0_46]), c_0_47]), c_0_48]), c_0_49])]), c_0_50])).
% 0.19/0.40  cnf(c_0_57, negated_conjecture, (r3_lattices(esk4_0,k4_lattices(esk4_0,X1,k4_filter_0(esk4_0,X1,X2)),X2)|~m1_subset_1(X2,u1_struct_0(esk4_0))|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_45]), c_0_48]), c_0_49])]), c_0_50])).
% 0.19/0.40  cnf(c_0_58, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_46]), c_0_47])]), ['proof']).
% 0.19/0.40  # SZS output end CNFRefutation
% 0.19/0.40  # Proof object total steps             : 59
% 0.19/0.40  # Proof object clause steps            : 42
% 0.19/0.40  # Proof object formula steps           : 17
% 0.19/0.40  # Proof object conjectures             : 15
% 0.19/0.40  # Proof object clause conjectures      : 12
% 0.19/0.40  # Proof object formula conjectures     : 3
% 0.19/0.40  # Proof object initial clauses used    : 23
% 0.19/0.40  # Proof object initial formulas used   : 8
% 0.19/0.40  # Proof object generating inferences   : 14
% 0.19/0.40  # Proof object simplifying inferences  : 35
% 0.19/0.40  # Training examples: 0 positive, 0 negative
% 0.19/0.40  # Parsed axioms                        : 8
% 0.19/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.40  # Initial clauses                      : 35
% 0.19/0.40  # Removed in clause preprocessing      : 1
% 0.19/0.40  # Initial clauses in saturation        : 34
% 0.19/0.40  # Processed clauses                    : 226
% 0.19/0.40  # ...of these trivial                  : 2
% 0.19/0.40  # ...subsumed                          : 42
% 0.19/0.40  # ...remaining for further processing  : 182
% 0.19/0.40  # Other redundant clauses eliminated   : 3
% 0.19/0.40  # Clauses deleted for lack of memory   : 0
% 0.19/0.40  # Backward-subsumed                    : 3
% 0.19/0.40  # Backward-rewritten                   : 0
% 0.19/0.40  # Generated clauses                    : 273
% 0.19/0.40  # ...of the previous two non-trivial   : 235
% 0.19/0.40  # Contextual simplify-reflections      : 23
% 0.19/0.40  # Paramodulations                      : 270
% 0.19/0.40  # Factorizations                       : 0
% 0.19/0.40  # Equation resolutions                 : 3
% 0.19/0.40  # Propositional unsat checks           : 0
% 0.19/0.40  #    Propositional check models        : 0
% 0.19/0.40  #    Propositional check unsatisfiable : 0
% 0.19/0.40  #    Propositional clauses             : 0
% 0.19/0.40  #    Propositional clauses after purity: 0
% 0.19/0.40  #    Propositional unsat core size     : 0
% 0.19/0.40  #    Propositional preprocessing time  : 0.000
% 0.19/0.40  #    Propositional encoding time       : 0.000
% 0.19/0.40  #    Propositional solver time         : 0.000
% 0.19/0.40  #    Success case prop preproc time    : 0.000
% 0.19/0.40  #    Success case prop encoding time   : 0.000
% 0.19/0.40  #    Success case prop solver time     : 0.000
% 0.19/0.40  # Current number of processed clauses  : 145
% 0.19/0.40  #    Positive orientable unit clauses  : 12
% 0.19/0.40  #    Positive unorientable unit clauses: 0
% 0.19/0.40  #    Negative unit clauses             : 4
% 0.19/0.40  #    Non-unit-clauses                  : 129
% 0.19/0.40  # Current number of unprocessed clauses: 74
% 0.19/0.40  # ...number of literals in the above   : 926
% 0.19/0.40  # Current number of archived formulas  : 0
% 0.19/0.40  # Current number of archived clauses   : 34
% 0.19/0.40  # Clause-clause subsumption calls (NU) : 7486
% 0.19/0.40  # Rec. Clause-clause subsumption calls : 585
% 0.19/0.40  # Non-unit clause-clause subsumptions  : 67
% 0.19/0.40  # Unit Clause-clause subsumption calls : 5
% 0.19/0.40  # Rewrite failures with RHS unbound    : 0
% 0.19/0.40  # BW rewrite match attempts            : 0
% 0.19/0.40  # BW rewrite match successes           : 0
% 0.19/0.40  # Condensation attempts                : 0
% 0.19/0.40  # Condensation successes               : 0
% 0.19/0.40  # Termbank termtop insertions          : 16276
% 0.19/0.41  
% 0.19/0.41  # -------------------------------------------------
% 0.19/0.41  # User time                : 0.061 s
% 0.19/0.41  # System time              : 0.004 s
% 0.19/0.41  # Total time               : 0.065 s
% 0.19/0.41  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
