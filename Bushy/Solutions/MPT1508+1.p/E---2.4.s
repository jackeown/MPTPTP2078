%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : lattice3__t42_lattice3.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:55 EDT 2019

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 272 expanded)
%              Number of clauses        :   42 (  89 expanded)
%              Number of leaves         :   10 (  67 expanded)
%              Depth                    :   11
%              Number of atoms          :  302 (1789 expanded)
%              Number of equality atoms :   14 ( 161 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   28 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t42_lattice3,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v4_lattice3(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( ( r2_hidden(X2,X3)
                & r3_lattice3(X1,X2,X3) )
             => k16_lattice3(X1,X3) = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t42_lattice3.p',t42_lattice3)).

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
    file('/export/starexec/sandbox2/benchmark/lattice3__t42_lattice3.p',redefinition_r3_lattices)).

fof(dt_k15_lattice3,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t42_lattice3.p',dt_k15_lattice3)).

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
    file('/export/starexec/sandbox2/benchmark/lattice3__t42_lattice3.p',cc1_lattices)).

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
    file('/export/starexec/sandbox2/benchmark/lattice3__t42_lattice3.p',t26_lattices)).

fof(dt_l3_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( l1_lattices(X1)
        & l2_lattices(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t42_lattice3.p',dt_l3_lattices)).

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
    file('/export/starexec/sandbox2/benchmark/lattice3__t42_lattice3.p',t38_lattice3)).

fof(t40_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v4_lattice3(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( r3_lattice3(X1,X2,X3)
             => r3_lattices(X1,X2,k16_lattice3(X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t42_lattice3.p',t40_lattice3)).

fof(d22_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => ! [X2] : k16_lattice3(X1,X2) = k15_lattice3(X1,a_2_1_lattice3(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t42_lattice3.p',d22_lattice3)).

fof(dt_k16_lattice3,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => m1_subset_1(k16_lattice3(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t42_lattice3.p',dt_k16_lattice3)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v10_lattices(X1)
          & v4_lattice3(X1)
          & l3_lattices(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( ( r2_hidden(X2,X3)
                  & r3_lattice3(X1,X2,X3) )
               => k16_lattice3(X1,X3) = X2 ) ) ) ),
    inference(assume_negation,[status(cth)],[t42_lattice3])).

fof(c_0_11,plain,(
    ! [X31,X32,X33] :
      ( ( ~ r3_lattices(X31,X32,X33)
        | r1_lattices(X31,X32,X33)
        | v2_struct_0(X31)
        | ~ v6_lattices(X31)
        | ~ v8_lattices(X31)
        | ~ v9_lattices(X31)
        | ~ l3_lattices(X31)
        | ~ m1_subset_1(X32,u1_struct_0(X31))
        | ~ m1_subset_1(X33,u1_struct_0(X31)) )
      & ( ~ r1_lattices(X31,X32,X33)
        | r3_lattices(X31,X32,X33)
        | v2_struct_0(X31)
        | ~ v6_lattices(X31)
        | ~ v8_lattices(X31)
        | ~ v9_lattices(X31)
        | ~ l3_lattices(X31)
        | ~ m1_subset_1(X32,u1_struct_0(X31))
        | ~ m1_subset_1(X33,u1_struct_0(X31)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).

fof(c_0_12,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v10_lattices(esk1_0)
    & v4_lattice3(esk1_0)
    & l3_lattices(esk1_0)
    & m1_subset_1(esk2_0,u1_struct_0(esk1_0))
    & r2_hidden(esk2_0,esk3_0)
    & r3_lattice3(esk1_0,esk2_0,esk3_0)
    & k16_lattice3(esk1_0,esk3_0) != esk2_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).

fof(c_0_13,plain,(
    ! [X12,X13] :
      ( v2_struct_0(X12)
      | ~ l3_lattices(X12)
      | m1_subset_1(k15_lattice3(X12,X13),u1_struct_0(X12)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k15_lattice3])])])).

cnf(c_0_14,plain,
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

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( l3_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_18,plain,(
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

cnf(c_0_19,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_20,plain,(
    ! [X39,X40,X41] :
      ( v2_struct_0(X39)
      | ~ v4_lattices(X39)
      | ~ l2_lattices(X39)
      | ~ m1_subset_1(X40,u1_struct_0(X39))
      | ~ m1_subset_1(X41,u1_struct_0(X39))
      | ~ r1_lattices(X39,X40,X41)
      | ~ r1_lattices(X39,X41,X40)
      | X40 = X41 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t26_lattices])])])])).

fof(c_0_21,plain,(
    ! [X18] :
      ( ( l1_lattices(X18)
        | ~ l3_lattices(X18) )
      & ( l2_lattices(X18)
        | ~ l3_lattices(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).

cnf(c_0_22,negated_conjecture,
    ( r1_lattices(esk1_0,X1,esk2_0)
    | ~ r3_lattices(esk1_0,X1,esk2_0)
    | ~ v9_lattices(esk1_0)
    | ~ v8_lattices(esk1_0)
    | ~ v6_lattices(esk1_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16])]),c_0_17])).

cnf(c_0_23,plain,
    ( v9_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( v10_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_25,plain,(
    ! [X47,X48,X49] :
      ( ( r3_lattices(X47,X48,k15_lattice3(X47,X49))
        | ~ r2_hidden(X48,X49)
        | ~ m1_subset_1(X48,u1_struct_0(X47))
        | v2_struct_0(X47)
        | ~ v10_lattices(X47)
        | ~ v4_lattice3(X47)
        | ~ l3_lattices(X47) )
      & ( r3_lattices(X47,k16_lattice3(X47,X49),X48)
        | ~ r2_hidden(X48,X49)
        | ~ m1_subset_1(X48,u1_struct_0(X47))
        | v2_struct_0(X47)
        | ~ v10_lattices(X47)
        | ~ v4_lattice3(X47)
        | ~ l3_lattices(X47) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t38_lattice3])])])])])).

cnf(c_0_26,plain,
    ( r1_lattices(X1,X2,k15_lattice3(X1,X3))
    | v2_struct_0(X1)
    | ~ r3_lattices(X1,X2,k15_lattice3(X1,X3))
    | ~ v9_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v6_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_19])).

cnf(c_0_27,plain,
    ( v2_struct_0(X1)
    | X2 = X3
    | ~ v4_lattices(X1)
    | ~ l2_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_lattices(X1,X2,X3)
    | ~ r1_lattices(X1,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( l2_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,negated_conjecture,
    ( r1_lattices(esk1_0,X1,esk2_0)
    | ~ r3_lattices(esk1_0,X1,esk2_0)
    | ~ v8_lattices(esk1_0)
    | ~ v6_lattices(esk1_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_16]),c_0_24])]),c_0_17])).

cnf(c_0_30,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_31,plain,
    ( r3_lattices(X1,k16_lattice3(X1,X2),X3)
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( v4_lattice3(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_33,negated_conjecture,
    ( r1_lattices(esk1_0,esk2_0,k15_lattice3(esk1_0,X1))
    | ~ r3_lattices(esk1_0,esk2_0,k15_lattice3(esk1_0,X1))
    | ~ v9_lattices(esk1_0)
    | ~ v8_lattices(esk1_0)
    | ~ v6_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_15]),c_0_16])]),c_0_17])).

cnf(c_0_34,plain,
    ( X1 = k15_lattice3(X2,X3)
    | v2_struct_0(X2)
    | ~ v4_lattices(X2)
    | ~ r1_lattices(X2,k15_lattice3(X2,X3),X1)
    | ~ r1_lattices(X2,X1,k15_lattice3(X2,X3))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l3_lattices(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_19]),c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( r1_lattices(esk1_0,X1,esk2_0)
    | ~ r3_lattices(esk1_0,X1,esk2_0)
    | ~ v6_lattices(esk1_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_16]),c_0_24])]),c_0_17])).

cnf(c_0_36,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_37,negated_conjecture,
    ( r3_lattices(esk1_0,k16_lattice3(esk1_0,X1),esk2_0)
    | ~ r2_hidden(esk2_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_15]),c_0_16]),c_0_32]),c_0_24])]),c_0_17])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_39,negated_conjecture,
    ( r1_lattices(esk1_0,esk2_0,k15_lattice3(esk1_0,X1))
    | ~ r3_lattices(esk1_0,esk2_0,k15_lattice3(esk1_0,X1))
    | ~ v8_lattices(esk1_0)
    | ~ v6_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_23]),c_0_16]),c_0_24])]),c_0_17])).

fof(c_0_40,plain,(
    ! [X50,X51,X52] :
      ( v2_struct_0(X50)
      | ~ v10_lattices(X50)
      | ~ v4_lattice3(X50)
      | ~ l3_lattices(X50)
      | ~ m1_subset_1(X51,u1_struct_0(X50))
      | ~ r3_lattice3(X50,X51,X52)
      | r3_lattices(X50,X51,k16_lattice3(X50,X52)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t40_lattice3])])])])).

cnf(c_0_41,negated_conjecture,
    ( k15_lattice3(esk1_0,X1) = esk2_0
    | ~ v4_lattices(esk1_0)
    | ~ r1_lattices(esk1_0,k15_lattice3(esk1_0,X1),esk2_0)
    | ~ r1_lattices(esk1_0,esk2_0,k15_lattice3(esk1_0,X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_15]),c_0_16])]),c_0_17])).

cnf(c_0_42,plain,
    ( v4_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_43,plain,(
    ! [X10,X11] :
      ( v2_struct_0(X10)
      | ~ l3_lattices(X10)
      | k16_lattice3(X10,X11) = k15_lattice3(X10,a_2_1_lattice3(X10,X11)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d22_lattice3])])])])).

cnf(c_0_44,negated_conjecture,
    ( r1_lattices(esk1_0,X1,esk2_0)
    | ~ r3_lattices(esk1_0,X1,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_16]),c_0_24])]),c_0_17])).

cnf(c_0_45,negated_conjecture,
    ( r3_lattices(esk1_0,k16_lattice3(esk1_0,esk3_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

fof(c_0_46,plain,(
    ! [X14,X15] :
      ( v2_struct_0(X14)
      | ~ l3_lattices(X14)
      | m1_subset_1(k16_lattice3(X14,X15),u1_struct_0(X14)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k16_lattice3])])])).

cnf(c_0_47,negated_conjecture,
    ( r1_lattices(esk1_0,esk2_0,k15_lattice3(esk1_0,X1))
    | ~ r3_lattices(esk1_0,esk2_0,k15_lattice3(esk1_0,X1))
    | ~ v6_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_30]),c_0_16]),c_0_24])]),c_0_17])).

cnf(c_0_48,plain,
    ( v2_struct_0(X1)
    | r3_lattices(X1,X2,k16_lattice3(X1,X3))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r3_lattice3(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_49,negated_conjecture,
    ( k15_lattice3(esk1_0,X1) = esk2_0
    | ~ r1_lattices(esk1_0,k15_lattice3(esk1_0,X1),esk2_0)
    | ~ r1_lattices(esk1_0,esk2_0,k15_lattice3(esk1_0,X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_16]),c_0_24])]),c_0_17])).

cnf(c_0_50,plain,
    ( v2_struct_0(X1)
    | k16_lattice3(X1,X2) = k15_lattice3(X1,a_2_1_lattice3(X1,X2))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_51,negated_conjecture,
    ( r1_lattices(esk1_0,k16_lattice3(esk1_0,esk3_0),esk2_0)
    | ~ m1_subset_1(k16_lattice3(esk1_0,esk3_0),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_52,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k16_lattice3(X1,X2),u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_53,negated_conjecture,
    ( r1_lattices(esk1_0,esk2_0,k15_lattice3(esk1_0,X1))
    | ~ r3_lattices(esk1_0,esk2_0,k15_lattice3(esk1_0,X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_36]),c_0_16]),c_0_24])]),c_0_17])).

cnf(c_0_54,negated_conjecture,
    ( r3_lattices(esk1_0,esk2_0,k16_lattice3(esk1_0,X1))
    | ~ r3_lattice3(esk1_0,esk2_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_15]),c_0_16]),c_0_32]),c_0_24])]),c_0_17])).

cnf(c_0_55,negated_conjecture,
    ( r3_lattice3(esk1_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_56,negated_conjecture,
    ( k16_lattice3(esk1_0,X1) = esk2_0
    | ~ r1_lattices(esk1_0,k16_lattice3(esk1_0,X1),esk2_0)
    | ~ r1_lattices(esk1_0,esk2_0,k16_lattice3(esk1_0,X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_16])]),c_0_17])).

cnf(c_0_57,negated_conjecture,
    ( r1_lattices(esk1_0,k16_lattice3(esk1_0,esk3_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_16])]),c_0_17])).

cnf(c_0_58,negated_conjecture,
    ( k16_lattice3(esk1_0,esk3_0) != esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_59,negated_conjecture,
    ( r1_lattices(esk1_0,esk2_0,k16_lattice3(esk1_0,X1))
    | ~ r3_lattices(esk1_0,esk2_0,k16_lattice3(esk1_0,X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_50]),c_0_16])]),c_0_17])).

cnf(c_0_60,negated_conjecture,
    ( r3_lattices(esk1_0,esk2_0,k16_lattice3(esk1_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_61,negated_conjecture,
    ( ~ r1_lattices(esk1_0,esk2_0,k16_lattice3(esk1_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58])).

cnf(c_0_62,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61]),
    [proof]).
%------------------------------------------------------------------------------
