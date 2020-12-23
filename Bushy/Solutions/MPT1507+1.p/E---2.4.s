%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : lattice3__t41_lattice3.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:54 EDT 2019

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 191 expanded)
%              Number of clauses        :   32 (  62 expanded)
%              Number of leaves         :    8 (  47 expanded)
%              Depth                    :   13
%              Number of atoms          :  304 (1280 expanded)
%              Number of equality atoms :   15 ( 117 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal clause size      :   50 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t41_lattice3,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/lattice3__t41_lattice3.p',t41_lattice3)).

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
    file('/export/starexec/sandbox2/benchmark/lattice3__t41_lattice3.p',t38_lattice3)).

fof(dt_k15_lattice3,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t41_lattice3.p',dt_k15_lattice3)).

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
    file('/export/starexec/sandbox2/benchmark/lattice3__t41_lattice3.p',redefinition_r3_lattices)).

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
    file('/export/starexec/sandbox2/benchmark/lattice3__t41_lattice3.p',cc1_lattices)).

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
    file('/export/starexec/sandbox2/benchmark/lattice3__t41_lattice3.p',d21_lattice3)).

fof(t26_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v4_lattices(X1)
        & l2_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( ( r1_lattices(X1,X2,X3)
                  & r1_lattices(X1,X3,X2) )
               => X2 = X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t41_lattice3.p',t26_lattices)).

fof(dt_l3_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( l1_lattices(X1)
        & l2_lattices(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t41_lattice3.p',dt_l3_lattices)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
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
    inference(assume_negation,[status(cth)],[t41_lattice3])).

fof(c_0_9,plain,(
    ! [X50,X51,X52] :
      ( ( r3_lattices(X50,X51,k15_lattice3(X50,X52))
        | ~ r2_hidden(X51,X52)
        | ~ m1_subset_1(X51,u1_struct_0(X50))
        | v2_struct_0(X50)
        | ~ v10_lattices(X50)
        | ~ v4_lattice3(X50)
        | ~ l3_lattices(X50) )
      & ( r3_lattices(X50,k16_lattice3(X50,X52),X51)
        | ~ r2_hidden(X51,X52)
        | ~ m1_subset_1(X51,u1_struct_0(X50))
        | v2_struct_0(X50)
        | ~ v10_lattices(X50)
        | ~ v4_lattice3(X50)
        | ~ l3_lattices(X50) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t38_lattice3])])])])])).

fof(c_0_10,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v10_lattices(esk1_0)
    & v4_lattice3(esk1_0)
    & l3_lattices(esk1_0)
    & m1_subset_1(esk2_0,u1_struct_0(esk1_0))
    & r2_hidden(esk2_0,esk3_0)
    & r4_lattice3(esk1_0,esk2_0,esk3_0)
    & k15_lattice3(esk1_0,esk3_0) != esk2_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).

cnf(c_0_11,plain,
    ( r3_lattices(X1,X2,k15_lattice3(X1,X3))
    | v2_struct_0(X1)
    | ~ r2_hidden(X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( l3_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( v4_lattice3(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( v10_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_17,plain,(
    ! [X15,X16] :
      ( v2_struct_0(X15)
      | ~ l3_lattices(X15)
      | m1_subset_1(k15_lattice3(X15,X16),u1_struct_0(X15)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k15_lattice3])])])).

fof(c_0_18,plain,(
    ! [X34,X35,X36] :
      ( ( ~ r3_lattices(X34,X35,X36)
        | r1_lattices(X34,X35,X36)
        | v2_struct_0(X34)
        | ~ v6_lattices(X34)
        | ~ v8_lattices(X34)
        | ~ v9_lattices(X34)
        | ~ l3_lattices(X34)
        | ~ m1_subset_1(X35,u1_struct_0(X34))
        | ~ m1_subset_1(X36,u1_struct_0(X34)) )
      & ( ~ r1_lattices(X34,X35,X36)
        | r3_lattices(X34,X35,X36)
        | v2_struct_0(X34)
        | ~ v6_lattices(X34)
        | ~ v8_lattices(X34)
        | ~ v9_lattices(X34)
        | ~ l3_lattices(X34)
        | ~ m1_subset_1(X35,u1_struct_0(X34))
        | ~ m1_subset_1(X36,u1_struct_0(X34)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).

cnf(c_0_19,negated_conjecture,
    ( r3_lattices(esk1_0,esk2_0,k15_lattice3(esk1_0,X1))
    | ~ r2_hidden(esk2_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13]),c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_21,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( r1_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( r3_lattices(esk1_0,esk2_0,k15_lattice3(esk1_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(k15_lattice3(esk1_0,X1),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_21]),c_0_13])])).

fof(c_0_25,plain,(
    ! [X58] :
      ( ( ~ v2_struct_0(X58)
        | v2_struct_0(X58)
        | ~ v10_lattices(X58)
        | ~ l3_lattices(X58) )
      & ( v4_lattices(X58)
        | v2_struct_0(X58)
        | ~ v10_lattices(X58)
        | ~ l3_lattices(X58) )
      & ( v5_lattices(X58)
        | v2_struct_0(X58)
        | ~ v10_lattices(X58)
        | ~ l3_lattices(X58) )
      & ( v6_lattices(X58)
        | v2_struct_0(X58)
        | ~ v10_lattices(X58)
        | ~ l3_lattices(X58) )
      & ( v7_lattices(X58)
        | v2_struct_0(X58)
        | ~ v10_lattices(X58)
        | ~ l3_lattices(X58) )
      & ( v8_lattices(X58)
        | v2_struct_0(X58)
        | ~ v10_lattices(X58)
        | ~ l3_lattices(X58) )
      & ( v9_lattices(X58)
        | v2_struct_0(X58)
        | ~ v10_lattices(X58)
        | ~ l3_lattices(X58) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).

cnf(c_0_26,negated_conjecture,
    ( r1_lattices(esk1_0,esk2_0,k15_lattice3(esk1_0,esk3_0))
    | ~ v9_lattices(esk1_0)
    | ~ v8_lattices(esk1_0)
    | ~ v6_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_12]),c_0_13])]),c_0_16])).

cnf(c_0_27,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_28,plain,(
    ! [X10,X11,X12,X13] :
      ( ( r4_lattice3(X10,X12,X11)
        | X12 != k15_lattice3(X10,X11)
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | v2_struct_0(X10)
        | ~ v10_lattices(X10)
        | ~ v4_lattice3(X10)
        | ~ l3_lattices(X10)
        | v2_struct_0(X10)
        | ~ l3_lattices(X10) )
      & ( ~ m1_subset_1(X13,u1_struct_0(X10))
        | ~ r4_lattice3(X10,X13,X11)
        | r1_lattices(X10,X12,X13)
        | X12 != k15_lattice3(X10,X11)
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | v2_struct_0(X10)
        | ~ v10_lattices(X10)
        | ~ v4_lattice3(X10)
        | ~ l3_lattices(X10)
        | v2_struct_0(X10)
        | ~ l3_lattices(X10) )
      & ( m1_subset_1(esk4_3(X10,X11,X12),u1_struct_0(X10))
        | ~ r4_lattice3(X10,X12,X11)
        | X12 = k15_lattice3(X10,X11)
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | v2_struct_0(X10)
        | ~ v10_lattices(X10)
        | ~ v4_lattice3(X10)
        | ~ l3_lattices(X10)
        | v2_struct_0(X10)
        | ~ l3_lattices(X10) )
      & ( r4_lattice3(X10,esk4_3(X10,X11,X12),X11)
        | ~ r4_lattice3(X10,X12,X11)
        | X12 = k15_lattice3(X10,X11)
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | v2_struct_0(X10)
        | ~ v10_lattices(X10)
        | ~ v4_lattice3(X10)
        | ~ l3_lattices(X10)
        | v2_struct_0(X10)
        | ~ l3_lattices(X10) )
      & ( ~ r1_lattices(X10,X12,esk4_3(X10,X11,X12))
        | ~ r4_lattice3(X10,X12,X11)
        | X12 = k15_lattice3(X10,X11)
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | v2_struct_0(X10)
        | ~ v10_lattices(X10)
        | ~ v4_lattice3(X10)
        | ~ l3_lattices(X10)
        | v2_struct_0(X10)
        | ~ l3_lattices(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d21_lattice3])])])])])])).

cnf(c_0_29,negated_conjecture,
    ( r1_lattices(esk1_0,esk2_0,k15_lattice3(esk1_0,esk3_0))
    | ~ v9_lattices(esk1_0)
    | ~ v8_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_13]),c_0_15])]),c_0_16])).

cnf(c_0_30,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_32,plain,(
    ! [X42,X43,X44] :
      ( v2_struct_0(X42)
      | ~ v4_lattices(X42)
      | ~ l2_lattices(X42)
      | ~ m1_subset_1(X43,u1_struct_0(X42))
      | ~ m1_subset_1(X44,u1_struct_0(X42))
      | ~ r1_lattices(X42,X43,X44)
      | ~ r1_lattices(X42,X44,X43)
      | X43 = X44 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t26_lattices])])])])).

cnf(c_0_33,negated_conjecture,
    ( r1_lattices(esk1_0,esk2_0,k15_lattice3(esk1_0,esk3_0))
    | ~ v9_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_13]),c_0_15])]),c_0_16])).

cnf(c_0_34,plain,
    ( v9_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,plain,
    ( v2_struct_0(X2)
    | r1_lattices(X2,X4,X1)
    | X4 != k15_lattice3(X2,X3)
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2)
    | ~ r4_lattice3(X2,X1,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2)) ),
    inference(cn,[status(thm)],[c_0_31])).

cnf(c_0_36,plain,
    ( v2_struct_0(X1)
    | X2 = X3
    | ~ v4_lattices(X1)
    | ~ l2_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_lattices(X1,X2,X3)
    | ~ r1_lattices(X1,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_37,negated_conjecture,
    ( r1_lattices(esk1_0,esk2_0,k15_lattice3(esk1_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_13]),c_0_15])]),c_0_16])).

cnf(c_0_38,negated_conjecture,
    ( k15_lattice3(esk1_0,esk3_0) != esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_39,plain,
    ( r1_lattices(X1,k15_lattice3(X1,X2),X3)
    | v2_struct_0(X1)
    | ~ r4_lattice3(X1,X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_35]),c_0_21])).

cnf(c_0_40,negated_conjecture,
    ( r4_lattice3(esk1_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_41,negated_conjecture,
    ( ~ v4_lattices(esk1_0)
    | ~ l2_lattices(esk1_0)
    | ~ r1_lattices(esk1_0,k15_lattice3(esk1_0,esk3_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_12]),c_0_24])]),c_0_38]),c_0_16])).

cnf(c_0_42,negated_conjecture,
    ( r1_lattices(esk1_0,k15_lattice3(esk1_0,esk3_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_12]),c_0_13]),c_0_14]),c_0_15])]),c_0_16])).

fof(c_0_43,plain,(
    ! [X21] :
      ( ( l1_lattices(X21)
        | ~ l3_lattices(X21) )
      & ( l2_lattices(X21)
        | ~ l3_lattices(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).

cnf(c_0_44,negated_conjecture,
    ( ~ v4_lattices(esk1_0)
    | ~ l2_lattices(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_42])])).

cnf(c_0_45,plain,
    ( l2_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_46,negated_conjecture,
    ( ~ v4_lattices(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_13])])).

cnf(c_0_47,plain,
    ( v4_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_48,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_13]),c_0_15])]),c_0_16]),
    [proof]).
%------------------------------------------------------------------------------
