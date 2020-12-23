%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1508+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:05 EST 2020

% Result     : Theorem 18.26s
% Output     : CNFRefutation 18.26s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 261 expanded)
%              Number of clauses        :   30 (  82 expanded)
%              Number of leaves         :    8 (  65 expanded)
%              Depth                    :    7
%              Number of atoms          :  227 (1719 expanded)
%              Number of equality atoms :    7 ( 151 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    2 (   1 average)

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_lattice3)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_lattice3)).

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
    file('/export/starexec/sandbox/benchmark/Axioms/MPT018+2.ax',cc1_lattices)).

fof(dt_k16_lattice3,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => m1_subset_1(k16_lattice3(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k16_lattice3)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_lattice3)).

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
    file('/export/starexec/sandbox/benchmark/Axioms/MPT018+2.ax',redefinition_r3_lattices)).

fof(dt_l3_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( l1_lattices(X1)
        & l2_lattices(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT018+2.ax',dt_l3_lattices)).

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
    file('/export/starexec/sandbox/benchmark/Axioms/MPT018+2.ax',t26_lattices)).

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
                  & r3_lattice3(X1,X2,X3) )
               => k16_lattice3(X1,X3) = X2 ) ) ) ),
    inference(assume_negation,[status(cth)],[t42_lattice3])).

fof(c_0_9,plain,(
    ! [X9279,X9280,X9281] :
      ( v2_struct_0(X9279)
      | ~ v10_lattices(X9279)
      | ~ v4_lattice3(X9279)
      | ~ l3_lattices(X9279)
      | ~ m1_subset_1(X9280,u1_struct_0(X9279))
      | ~ r3_lattice3(X9279,X9280,X9281)
      | r3_lattices(X9279,X9280,k16_lattice3(X9279,X9281)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t40_lattice3])])])])).

fof(c_0_10,negated_conjecture,
    ( ~ v2_struct_0(esk1043_0)
    & v10_lattices(esk1043_0)
    & v4_lattice3(esk1043_0)
    & l3_lattices(esk1043_0)
    & m1_subset_1(esk1044_0,u1_struct_0(esk1043_0))
    & r2_hidden(esk1044_0,esk1045_0)
    & r3_lattice3(esk1043_0,esk1044_0,esk1045_0)
    & k16_lattice3(esk1043_0,esk1045_0) != esk1044_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).

fof(c_0_11,plain,(
    ! [X6519] :
      ( ( ~ v2_struct_0(X6519)
        | v2_struct_0(X6519)
        | ~ v10_lattices(X6519)
        | ~ l3_lattices(X6519) )
      & ( v4_lattices(X6519)
        | v2_struct_0(X6519)
        | ~ v10_lattices(X6519)
        | ~ l3_lattices(X6519) )
      & ( v5_lattices(X6519)
        | v2_struct_0(X6519)
        | ~ v10_lattices(X6519)
        | ~ l3_lattices(X6519) )
      & ( v6_lattices(X6519)
        | v2_struct_0(X6519)
        | ~ v10_lattices(X6519)
        | ~ l3_lattices(X6519) )
      & ( v7_lattices(X6519)
        | v2_struct_0(X6519)
        | ~ v10_lattices(X6519)
        | ~ l3_lattices(X6519) )
      & ( v8_lattices(X6519)
        | v2_struct_0(X6519)
        | ~ v10_lattices(X6519)
        | ~ l3_lattices(X6519) )
      & ( v9_lattices(X6519)
        | v2_struct_0(X6519)
        | ~ v10_lattices(X6519)
        | ~ l3_lattices(X6519) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).

fof(c_0_12,plain,(
    ! [X8973,X8974] :
      ( v2_struct_0(X8973)
      | ~ l3_lattices(X8973)
      | m1_subset_1(k16_lattice3(X8973,X8974),u1_struct_0(X8973)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k16_lattice3])])])).

fof(c_0_13,plain,(
    ! [X9275,X9276,X9277] :
      ( ( r3_lattices(X9275,X9276,k15_lattice3(X9275,X9277))
        | ~ r2_hidden(X9276,X9277)
        | ~ m1_subset_1(X9276,u1_struct_0(X9275))
        | v2_struct_0(X9275)
        | ~ v10_lattices(X9275)
        | ~ v4_lattice3(X9275)
        | ~ l3_lattices(X9275) )
      & ( r3_lattices(X9275,k16_lattice3(X9275,X9277),X9276)
        | ~ r2_hidden(X9276,X9277)
        | ~ m1_subset_1(X9276,u1_struct_0(X9275))
        | v2_struct_0(X9275)
        | ~ v10_lattices(X9275)
        | ~ v4_lattice3(X9275)
        | ~ l3_lattices(X9275) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t38_lattice3])])])])])).

fof(c_0_14,plain,(
    ! [X6643,X6644,X6645] :
      ( ( ~ r3_lattices(X6643,X6644,X6645)
        | r1_lattices(X6643,X6644,X6645)
        | v2_struct_0(X6643)
        | ~ v6_lattices(X6643)
        | ~ v8_lattices(X6643)
        | ~ v9_lattices(X6643)
        | ~ l3_lattices(X6643)
        | ~ m1_subset_1(X6644,u1_struct_0(X6643))
        | ~ m1_subset_1(X6645,u1_struct_0(X6643)) )
      & ( ~ r1_lattices(X6643,X6644,X6645)
        | r3_lattices(X6643,X6644,X6645)
        | v2_struct_0(X6643)
        | ~ v6_lattices(X6643)
        | ~ v8_lattices(X6643)
        | ~ v9_lattices(X6643)
        | ~ l3_lattices(X6643)
        | ~ m1_subset_1(X6644,u1_struct_0(X6643))
        | ~ m1_subset_1(X6645,u1_struct_0(X6643)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).

cnf(c_0_15,plain,
    ( v2_struct_0(X1)
    | r3_lattices(X1,X2,k16_lattice3(X1,X3))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r3_lattice3(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,negated_conjecture,
    ( r3_lattice3(esk1043_0,esk1044_0,esk1045_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,negated_conjecture,
    ( v4_lattice3(esk1043_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,negated_conjecture,
    ( l3_lattices(esk1043_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_19,negated_conjecture,
    ( v10_lattices(esk1043_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk1044_0,u1_struct_0(esk1043_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_21,negated_conjecture,
    ( ~ v2_struct_0(esk1043_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_22,plain,
    ( v9_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_23,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_24,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_25,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k16_lattice3(X1,X2),u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_26,plain,(
    ! [X6624] :
      ( ( l1_lattices(X6624)
        | ~ l3_lattices(X6624) )
      & ( l2_lattices(X6624)
        | ~ l3_lattices(X6624) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).

cnf(c_0_27,plain,
    ( r3_lattices(X1,k16_lattice3(X1,X2),X3)
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_28,plain,(
    ! [X6679,X6680,X6681] :
      ( v2_struct_0(X6679)
      | ~ v4_lattices(X6679)
      | ~ l2_lattices(X6679)
      | ~ m1_subset_1(X6680,u1_struct_0(X6679))
      | ~ m1_subset_1(X6681,u1_struct_0(X6679))
      | ~ r1_lattices(X6679,X6680,X6681)
      | ~ r1_lattices(X6679,X6681,X6680)
      | X6680 = X6681 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t26_lattices])])])])).

cnf(c_0_29,plain,
    ( r1_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_30,negated_conjecture,
    ( r3_lattices(esk1043_0,esk1044_0,k16_lattice3(esk1043_0,esk1045_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_18]),c_0_19]),c_0_20])]),c_0_21])).

cnf(c_0_31,negated_conjecture,
    ( v9_lattices(esk1043_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_18]),c_0_19])]),c_0_21])).

cnf(c_0_32,negated_conjecture,
    ( v8_lattices(esk1043_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_18]),c_0_19])]),c_0_21])).

cnf(c_0_33,negated_conjecture,
    ( v6_lattices(esk1043_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_18]),c_0_19])]),c_0_21])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(k16_lattice3(esk1043_0,X1),u1_struct_0(esk1043_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_18]),c_0_21])).

cnf(c_0_35,plain,
    ( l2_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,plain,
    ( v4_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_37,negated_conjecture,
    ( r3_lattices(esk1043_0,k16_lattice3(esk1043_0,X1),esk1044_0)
    | ~ r2_hidden(esk1044_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_20]),c_0_17]),c_0_18]),c_0_19])]),c_0_21])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk1044_0,esk1045_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_39,plain,
    ( v2_struct_0(X1)
    | X2 = X3
    | ~ v4_lattices(X1)
    | ~ l2_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_lattices(X1,X2,X3)
    | ~ r1_lattices(X1,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_40,negated_conjecture,
    ( r1_lattices(esk1043_0,esk1044_0,k16_lattice3(esk1043_0,esk1045_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31]),c_0_32]),c_0_33]),c_0_18]),c_0_34]),c_0_20])]),c_0_21])).

cnf(c_0_41,negated_conjecture,
    ( l2_lattices(esk1043_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_18])).

cnf(c_0_42,negated_conjecture,
    ( v4_lattices(esk1043_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_18]),c_0_19])]),c_0_21])).

cnf(c_0_43,negated_conjecture,
    ( k16_lattice3(esk1043_0,esk1045_0) != esk1044_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_44,negated_conjecture,
    ( r3_lattices(esk1043_0,k16_lattice3(esk1043_0,esk1045_0),esk1044_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_45,negated_conjecture,
    ( ~ r1_lattices(esk1043_0,k16_lattice3(esk1043_0,esk1045_0),esk1044_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41]),c_0_42]),c_0_20]),c_0_34])]),c_0_43]),c_0_21])).

cnf(c_0_46,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_44]),c_0_31]),c_0_32]),c_0_33]),c_0_18]),c_0_20]),c_0_34])]),c_0_21]),c_0_45]),
    [proof]).
%------------------------------------------------------------------------------
