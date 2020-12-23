%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:14:53 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  116 (2636 expanded)
%              Number of clauses        :   95 ( 823 expanded)
%              Number of leaves         :    8 ( 660 expanded)
%              Depth                    :   21
%              Number of atoms          :  944 (65035 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   40 (   7 average)
%              Maximal clause size      :  130 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t39_filter_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v10_lattices(X2)
            & l3_lattices(X2) )
         => ( ( ~ v2_struct_0(X1)
              & v10_lattices(X1)
              & v11_lattices(X1)
              & l3_lattices(X1)
              & ~ v2_struct_0(X2)
              & v10_lattices(X2)
              & v11_lattices(X2)
              & l3_lattices(X2) )
          <=> ( ~ v2_struct_0(k7_filter_1(X1,X2))
              & v10_lattices(k7_filter_1(X1,X2))
              & v11_lattices(k7_filter_1(X1,X2))
              & l3_lattices(k7_filter_1(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_filter_1)).

fof(cc5_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( ( ~ v2_struct_0(X1)
          & v17_lattices(X1) )
       => ( ~ v2_struct_0(X1)
          & v11_lattices(X1)
          & v15_lattices(X1)
          & v16_lattices(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_lattices)).

fof(t47_filter_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v10_lattices(X2)
            & l3_lattices(X2) )
         => ( ( ~ v2_struct_0(X1)
              & v10_lattices(X1)
              & v17_lattices(X1)
              & l3_lattices(X1)
              & ~ v2_struct_0(X2)
              & v10_lattices(X2)
              & v17_lattices(X2)
              & l3_lattices(X2) )
          <=> ( ~ v2_struct_0(k7_filter_1(X1,X2))
              & v10_lattices(k7_filter_1(X1,X2))
              & v17_lattices(k7_filter_1(X1,X2))
              & l3_lattices(k7_filter_1(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_filter_1)).

fof(t46_filter_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v10_lattices(X2)
            & l3_lattices(X2) )
         => ( ( ~ v2_struct_0(X1)
              & v10_lattices(X1)
              & v15_lattices(X1)
              & v16_lattices(X1)
              & l3_lattices(X1)
              & ~ v2_struct_0(X2)
              & v10_lattices(X2)
              & v15_lattices(X2)
              & v16_lattices(X2)
              & l3_lattices(X2) )
          <=> ( ~ v2_struct_0(k7_filter_1(X1,X2))
              & v10_lattices(k7_filter_1(X1,X2))
              & v15_lattices(k7_filter_1(X1,X2))
              & v16_lattices(k7_filter_1(X1,X2))
              & l3_lattices(k7_filter_1(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_filter_1)).

fof(dt_k7_filter_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1)
        & ~ v2_struct_0(X2)
        & l3_lattices(X2) )
     => ( v3_lattices(k7_filter_1(X1,X2))
        & l3_lattices(k7_filter_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_filter_1)).

fof(cc6_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( ( ~ v2_struct_0(X1)
          & v11_lattices(X1)
          & v15_lattices(X1)
          & v16_lattices(X1) )
       => ( ~ v2_struct_0(X1)
          & v17_lattices(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_lattices)).

fof(c_0_6,plain,(
    ! [X1,X2] :
      ( epred1_2(X2,X1)
    <=> ( ( ~ v2_struct_0(X1)
          & v10_lattices(X1)
          & v11_lattices(X1)
          & l3_lattices(X1)
          & ~ v2_struct_0(X2)
          & v10_lattices(X2)
          & v11_lattices(X2)
          & l3_lattices(X2) )
      <=> ( ~ v2_struct_0(k7_filter_1(X1,X2))
          & v10_lattices(k7_filter_1(X1,X2))
          & v11_lattices(k7_filter_1(X1,X2))
          & l3_lattices(k7_filter_1(X1,X2)) ) ) ) ),
    introduced(definition)).

fof(c_0_7,plain,(
    ! [X1,X2] :
      ( epred1_2(X2,X1)
     => ( ( ~ v2_struct_0(X1)
          & v10_lattices(X1)
          & v11_lattices(X1)
          & l3_lattices(X1)
          & ~ v2_struct_0(X2)
          & v10_lattices(X2)
          & v11_lattices(X2)
          & l3_lattices(X2) )
      <=> ( ~ v2_struct_0(k7_filter_1(X1,X2))
          & v10_lattices(k7_filter_1(X1,X2))
          & v11_lattices(k7_filter_1(X1,X2))
          & l3_lattices(k7_filter_1(X1,X2)) ) ) ) ),
    inference(split_equiv,[status(thm)],[c_0_6])).

fof(c_0_8,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v10_lattices(X2)
            & l3_lattices(X2) )
         => epred1_2(X2,X1) ) ) ),
    inference(apply_def,[status(thm)],[t39_filter_1,c_0_6])).

fof(c_0_9,plain,(
    ! [X13,X14] :
      ( ( ~ v2_struct_0(k7_filter_1(X13,X14))
        | v2_struct_0(X13)
        | ~ v10_lattices(X13)
        | ~ v11_lattices(X13)
        | ~ l3_lattices(X13)
        | v2_struct_0(X14)
        | ~ v10_lattices(X14)
        | ~ v11_lattices(X14)
        | ~ l3_lattices(X14)
        | ~ epred1_2(X14,X13) )
      & ( v10_lattices(k7_filter_1(X13,X14))
        | v2_struct_0(X13)
        | ~ v10_lattices(X13)
        | ~ v11_lattices(X13)
        | ~ l3_lattices(X13)
        | v2_struct_0(X14)
        | ~ v10_lattices(X14)
        | ~ v11_lattices(X14)
        | ~ l3_lattices(X14)
        | ~ epred1_2(X14,X13) )
      & ( v11_lattices(k7_filter_1(X13,X14))
        | v2_struct_0(X13)
        | ~ v10_lattices(X13)
        | ~ v11_lattices(X13)
        | ~ l3_lattices(X13)
        | v2_struct_0(X14)
        | ~ v10_lattices(X14)
        | ~ v11_lattices(X14)
        | ~ l3_lattices(X14)
        | ~ epred1_2(X14,X13) )
      & ( l3_lattices(k7_filter_1(X13,X14))
        | v2_struct_0(X13)
        | ~ v10_lattices(X13)
        | ~ v11_lattices(X13)
        | ~ l3_lattices(X13)
        | v2_struct_0(X14)
        | ~ v10_lattices(X14)
        | ~ v11_lattices(X14)
        | ~ l3_lattices(X14)
        | ~ epred1_2(X14,X13) )
      & ( ~ v2_struct_0(X13)
        | v2_struct_0(k7_filter_1(X13,X14))
        | ~ v10_lattices(k7_filter_1(X13,X14))
        | ~ v11_lattices(k7_filter_1(X13,X14))
        | ~ l3_lattices(k7_filter_1(X13,X14))
        | ~ epred1_2(X14,X13) )
      & ( v10_lattices(X13)
        | v2_struct_0(k7_filter_1(X13,X14))
        | ~ v10_lattices(k7_filter_1(X13,X14))
        | ~ v11_lattices(k7_filter_1(X13,X14))
        | ~ l3_lattices(k7_filter_1(X13,X14))
        | ~ epred1_2(X14,X13) )
      & ( v11_lattices(X13)
        | v2_struct_0(k7_filter_1(X13,X14))
        | ~ v10_lattices(k7_filter_1(X13,X14))
        | ~ v11_lattices(k7_filter_1(X13,X14))
        | ~ l3_lattices(k7_filter_1(X13,X14))
        | ~ epred1_2(X14,X13) )
      & ( l3_lattices(X13)
        | v2_struct_0(k7_filter_1(X13,X14))
        | ~ v10_lattices(k7_filter_1(X13,X14))
        | ~ v11_lattices(k7_filter_1(X13,X14))
        | ~ l3_lattices(k7_filter_1(X13,X14))
        | ~ epred1_2(X14,X13) )
      & ( ~ v2_struct_0(X14)
        | v2_struct_0(k7_filter_1(X13,X14))
        | ~ v10_lattices(k7_filter_1(X13,X14))
        | ~ v11_lattices(k7_filter_1(X13,X14))
        | ~ l3_lattices(k7_filter_1(X13,X14))
        | ~ epred1_2(X14,X13) )
      & ( v10_lattices(X14)
        | v2_struct_0(k7_filter_1(X13,X14))
        | ~ v10_lattices(k7_filter_1(X13,X14))
        | ~ v11_lattices(k7_filter_1(X13,X14))
        | ~ l3_lattices(k7_filter_1(X13,X14))
        | ~ epred1_2(X14,X13) )
      & ( v11_lattices(X14)
        | v2_struct_0(k7_filter_1(X13,X14))
        | ~ v10_lattices(k7_filter_1(X13,X14))
        | ~ v11_lattices(k7_filter_1(X13,X14))
        | ~ l3_lattices(k7_filter_1(X13,X14))
        | ~ epred1_2(X14,X13) )
      & ( l3_lattices(X14)
        | v2_struct_0(k7_filter_1(X13,X14))
        | ~ v10_lattices(k7_filter_1(X13,X14))
        | ~ v11_lattices(k7_filter_1(X13,X14))
        | ~ l3_lattices(k7_filter_1(X13,X14))
        | ~ epred1_2(X14,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])).

fof(c_0_10,plain,(
    ! [X7,X8] :
      ( v2_struct_0(X7)
      | ~ v10_lattices(X7)
      | ~ l3_lattices(X7)
      | v2_struct_0(X8)
      | ~ v10_lattices(X8)
      | ~ l3_lattices(X8)
      | epred1_2(X8,X7) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).

cnf(c_0_11,plain,
    ( v10_lattices(k7_filter_1(X1,X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v10_lattices(X1)
    | ~ v11_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X2)
    | ~ v11_lattices(X2)
    | ~ l3_lattices(X2)
    | ~ epred1_2(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | epred1_2(X2,X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_13,plain,(
    ! [X3] :
      ( ( ~ v2_struct_0(X3)
        | v2_struct_0(X3)
        | ~ v17_lattices(X3)
        | ~ l3_lattices(X3) )
      & ( v11_lattices(X3)
        | v2_struct_0(X3)
        | ~ v17_lattices(X3)
        | ~ l3_lattices(X3) )
      & ( v15_lattices(X3)
        | v2_struct_0(X3)
        | ~ v17_lattices(X3)
        | ~ l3_lattices(X3) )
      & ( v16_lattices(X3)
        | v2_struct_0(X3)
        | ~ v17_lattices(X3)
        | ~ l3_lattices(X3) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_lattices])])])])).

cnf(c_0_14,plain,
    ( v10_lattices(k7_filter_1(X1,X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v10_lattices(X2)
    | ~ v10_lattices(X1)
    | ~ v11_lattices(X2)
    | ~ v11_lattices(X1)
    | ~ l3_lattices(X2)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_15,plain,
    ( v11_lattices(X1)
    | v2_struct_0(X1)
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v10_lattices(X1)
          & l3_lattices(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & v10_lattices(X2)
              & l3_lattices(X2) )
           => ( ( ~ v2_struct_0(X1)
                & v10_lattices(X1)
                & v17_lattices(X1)
                & l3_lattices(X1)
                & ~ v2_struct_0(X2)
                & v10_lattices(X2)
                & v17_lattices(X2)
                & l3_lattices(X2) )
            <=> ( ~ v2_struct_0(k7_filter_1(X1,X2))
                & v10_lattices(k7_filter_1(X1,X2))
                & v17_lattices(k7_filter_1(X1,X2))
                & l3_lattices(k7_filter_1(X1,X2)) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t47_filter_1])).

cnf(c_0_17,plain,
    ( v10_lattices(k7_filter_1(X1,X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v10_lattices(X2)
    | ~ v10_lattices(X1)
    | ~ v11_lattices(X2)
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X2)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

fof(c_0_18,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v10_lattices(esk1_0)
    & l3_lattices(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & v10_lattices(esk2_0)
    & l3_lattices(esk2_0)
    & ( v2_struct_0(esk1_0)
      | ~ v10_lattices(esk1_0)
      | ~ v17_lattices(esk1_0)
      | ~ l3_lattices(esk1_0)
      | v2_struct_0(esk2_0)
      | ~ v10_lattices(esk2_0)
      | ~ v17_lattices(esk2_0)
      | ~ l3_lattices(esk2_0)
      | v2_struct_0(k7_filter_1(esk1_0,esk2_0))
      | ~ v10_lattices(k7_filter_1(esk1_0,esk2_0))
      | ~ v17_lattices(k7_filter_1(esk1_0,esk2_0))
      | ~ l3_lattices(k7_filter_1(esk1_0,esk2_0)) )
    & ( ~ v2_struct_0(k7_filter_1(esk1_0,esk2_0))
      | ~ v2_struct_0(esk1_0) )
    & ( v10_lattices(k7_filter_1(esk1_0,esk2_0))
      | ~ v2_struct_0(esk1_0) )
    & ( v17_lattices(k7_filter_1(esk1_0,esk2_0))
      | ~ v2_struct_0(esk1_0) )
    & ( l3_lattices(k7_filter_1(esk1_0,esk2_0))
      | ~ v2_struct_0(esk1_0) )
    & ( ~ v2_struct_0(k7_filter_1(esk1_0,esk2_0))
      | v10_lattices(esk1_0) )
    & ( v10_lattices(k7_filter_1(esk1_0,esk2_0))
      | v10_lattices(esk1_0) )
    & ( v17_lattices(k7_filter_1(esk1_0,esk2_0))
      | v10_lattices(esk1_0) )
    & ( l3_lattices(k7_filter_1(esk1_0,esk2_0))
      | v10_lattices(esk1_0) )
    & ( ~ v2_struct_0(k7_filter_1(esk1_0,esk2_0))
      | v17_lattices(esk1_0) )
    & ( v10_lattices(k7_filter_1(esk1_0,esk2_0))
      | v17_lattices(esk1_0) )
    & ( v17_lattices(k7_filter_1(esk1_0,esk2_0))
      | v17_lattices(esk1_0) )
    & ( l3_lattices(k7_filter_1(esk1_0,esk2_0))
      | v17_lattices(esk1_0) )
    & ( ~ v2_struct_0(k7_filter_1(esk1_0,esk2_0))
      | l3_lattices(esk1_0) )
    & ( v10_lattices(k7_filter_1(esk1_0,esk2_0))
      | l3_lattices(esk1_0) )
    & ( v17_lattices(k7_filter_1(esk1_0,esk2_0))
      | l3_lattices(esk1_0) )
    & ( l3_lattices(k7_filter_1(esk1_0,esk2_0))
      | l3_lattices(esk1_0) )
    & ( ~ v2_struct_0(k7_filter_1(esk1_0,esk2_0))
      | ~ v2_struct_0(esk2_0) )
    & ( v10_lattices(k7_filter_1(esk1_0,esk2_0))
      | ~ v2_struct_0(esk2_0) )
    & ( v17_lattices(k7_filter_1(esk1_0,esk2_0))
      | ~ v2_struct_0(esk2_0) )
    & ( l3_lattices(k7_filter_1(esk1_0,esk2_0))
      | ~ v2_struct_0(esk2_0) )
    & ( ~ v2_struct_0(k7_filter_1(esk1_0,esk2_0))
      | v10_lattices(esk2_0) )
    & ( v10_lattices(k7_filter_1(esk1_0,esk2_0))
      | v10_lattices(esk2_0) )
    & ( v17_lattices(k7_filter_1(esk1_0,esk2_0))
      | v10_lattices(esk2_0) )
    & ( l3_lattices(k7_filter_1(esk1_0,esk2_0))
      | v10_lattices(esk2_0) )
    & ( ~ v2_struct_0(k7_filter_1(esk1_0,esk2_0))
      | v17_lattices(esk2_0) )
    & ( v10_lattices(k7_filter_1(esk1_0,esk2_0))
      | v17_lattices(esk2_0) )
    & ( v17_lattices(k7_filter_1(esk1_0,esk2_0))
      | v17_lattices(esk2_0) )
    & ( l3_lattices(k7_filter_1(esk1_0,esk2_0))
      | v17_lattices(esk2_0) )
    & ( ~ v2_struct_0(k7_filter_1(esk1_0,esk2_0))
      | l3_lattices(esk2_0) )
    & ( v10_lattices(k7_filter_1(esk1_0,esk2_0))
      | l3_lattices(esk2_0) )
    & ( v17_lattices(k7_filter_1(esk1_0,esk2_0))
      | l3_lattices(esk2_0) )
    & ( l3_lattices(k7_filter_1(esk1_0,esk2_0))
      | l3_lattices(esk2_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])])).

cnf(c_0_19,plain,
    ( v10_lattices(k7_filter_1(X1,X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v10_lattices(X2)
    | ~ v10_lattices(X1)
    | ~ v17_lattices(X1)
    | ~ v17_lattices(X2)
    | ~ l3_lattices(X2)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( v10_lattices(k7_filter_1(esk1_0,esk2_0))
    | v17_lattices(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_21,negated_conjecture,
    ( v10_lattices(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( l3_lattices(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_24,plain,(
    ! [X1,X2] :
      ( epred2_2(X2,X1)
    <=> ( ( ~ v2_struct_0(X1)
          & v10_lattices(X1)
          & v15_lattices(X1)
          & v16_lattices(X1)
          & l3_lattices(X1)
          & ~ v2_struct_0(X2)
          & v10_lattices(X2)
          & v15_lattices(X2)
          & v16_lattices(X2)
          & l3_lattices(X2) )
      <=> ( ~ v2_struct_0(k7_filter_1(X1,X2))
          & v10_lattices(k7_filter_1(X1,X2))
          & v15_lattices(k7_filter_1(X1,X2))
          & v16_lattices(k7_filter_1(X1,X2))
          & l3_lattices(k7_filter_1(X1,X2)) ) ) ) ),
    introduced(definition)).

cnf(c_0_25,negated_conjecture,
    ( v10_lattices(k7_filter_1(esk1_0,esk2_0))
    | v10_lattices(k7_filter_1(X1,esk2_0))
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_22])]),c_0_23])).

cnf(c_0_26,negated_conjecture,
    ( v10_lattices(k7_filter_1(esk1_0,esk2_0))
    | v17_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,negated_conjecture,
    ( v10_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,negated_conjecture,
    ( l3_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_30,plain,(
    ! [X1,X2] :
      ( epred2_2(X2,X1)
     => ( ( ~ v2_struct_0(X1)
          & v10_lattices(X1)
          & v15_lattices(X1)
          & v16_lattices(X1)
          & l3_lattices(X1)
          & ~ v2_struct_0(X2)
          & v10_lattices(X2)
          & v15_lattices(X2)
          & v16_lattices(X2)
          & l3_lattices(X2) )
      <=> ( ~ v2_struct_0(k7_filter_1(X1,X2))
          & v10_lattices(k7_filter_1(X1,X2))
          & v15_lattices(k7_filter_1(X1,X2))
          & v16_lattices(k7_filter_1(X1,X2))
          & l3_lattices(k7_filter_1(X1,X2)) ) ) ) ),
    inference(split_equiv,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( v11_lattices(X1)
    | v2_struct_0(k7_filter_1(X1,X2))
    | ~ v10_lattices(k7_filter_1(X1,X2))
    | ~ v11_lattices(k7_filter_1(X1,X2))
    | ~ l3_lattices(k7_filter_1(X1,X2))
    | ~ epred1_2(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_32,negated_conjecture,
    ( v10_lattices(k7_filter_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_28])]),c_0_29])).

fof(c_0_33,plain,(
    ! [X15,X16] :
      ( ( ~ v2_struct_0(k7_filter_1(X15,X16))
        | v2_struct_0(X15)
        | ~ v10_lattices(X15)
        | ~ v15_lattices(X15)
        | ~ v16_lattices(X15)
        | ~ l3_lattices(X15)
        | v2_struct_0(X16)
        | ~ v10_lattices(X16)
        | ~ v15_lattices(X16)
        | ~ v16_lattices(X16)
        | ~ l3_lattices(X16)
        | ~ epred2_2(X16,X15) )
      & ( v10_lattices(k7_filter_1(X15,X16))
        | v2_struct_0(X15)
        | ~ v10_lattices(X15)
        | ~ v15_lattices(X15)
        | ~ v16_lattices(X15)
        | ~ l3_lattices(X15)
        | v2_struct_0(X16)
        | ~ v10_lattices(X16)
        | ~ v15_lattices(X16)
        | ~ v16_lattices(X16)
        | ~ l3_lattices(X16)
        | ~ epred2_2(X16,X15) )
      & ( v15_lattices(k7_filter_1(X15,X16))
        | v2_struct_0(X15)
        | ~ v10_lattices(X15)
        | ~ v15_lattices(X15)
        | ~ v16_lattices(X15)
        | ~ l3_lattices(X15)
        | v2_struct_0(X16)
        | ~ v10_lattices(X16)
        | ~ v15_lattices(X16)
        | ~ v16_lattices(X16)
        | ~ l3_lattices(X16)
        | ~ epred2_2(X16,X15) )
      & ( v16_lattices(k7_filter_1(X15,X16))
        | v2_struct_0(X15)
        | ~ v10_lattices(X15)
        | ~ v15_lattices(X15)
        | ~ v16_lattices(X15)
        | ~ l3_lattices(X15)
        | v2_struct_0(X16)
        | ~ v10_lattices(X16)
        | ~ v15_lattices(X16)
        | ~ v16_lattices(X16)
        | ~ l3_lattices(X16)
        | ~ epred2_2(X16,X15) )
      & ( l3_lattices(k7_filter_1(X15,X16))
        | v2_struct_0(X15)
        | ~ v10_lattices(X15)
        | ~ v15_lattices(X15)
        | ~ v16_lattices(X15)
        | ~ l3_lattices(X15)
        | v2_struct_0(X16)
        | ~ v10_lattices(X16)
        | ~ v15_lattices(X16)
        | ~ v16_lattices(X16)
        | ~ l3_lattices(X16)
        | ~ epred2_2(X16,X15) )
      & ( ~ v2_struct_0(X15)
        | v2_struct_0(k7_filter_1(X15,X16))
        | ~ v10_lattices(k7_filter_1(X15,X16))
        | ~ v15_lattices(k7_filter_1(X15,X16))
        | ~ v16_lattices(k7_filter_1(X15,X16))
        | ~ l3_lattices(k7_filter_1(X15,X16))
        | ~ epred2_2(X16,X15) )
      & ( v10_lattices(X15)
        | v2_struct_0(k7_filter_1(X15,X16))
        | ~ v10_lattices(k7_filter_1(X15,X16))
        | ~ v15_lattices(k7_filter_1(X15,X16))
        | ~ v16_lattices(k7_filter_1(X15,X16))
        | ~ l3_lattices(k7_filter_1(X15,X16))
        | ~ epred2_2(X16,X15) )
      & ( v15_lattices(X15)
        | v2_struct_0(k7_filter_1(X15,X16))
        | ~ v10_lattices(k7_filter_1(X15,X16))
        | ~ v15_lattices(k7_filter_1(X15,X16))
        | ~ v16_lattices(k7_filter_1(X15,X16))
        | ~ l3_lattices(k7_filter_1(X15,X16))
        | ~ epred2_2(X16,X15) )
      & ( v16_lattices(X15)
        | v2_struct_0(k7_filter_1(X15,X16))
        | ~ v10_lattices(k7_filter_1(X15,X16))
        | ~ v15_lattices(k7_filter_1(X15,X16))
        | ~ v16_lattices(k7_filter_1(X15,X16))
        | ~ l3_lattices(k7_filter_1(X15,X16))
        | ~ epred2_2(X16,X15) )
      & ( l3_lattices(X15)
        | v2_struct_0(k7_filter_1(X15,X16))
        | ~ v10_lattices(k7_filter_1(X15,X16))
        | ~ v15_lattices(k7_filter_1(X15,X16))
        | ~ v16_lattices(k7_filter_1(X15,X16))
        | ~ l3_lattices(k7_filter_1(X15,X16))
        | ~ epred2_2(X16,X15) )
      & ( ~ v2_struct_0(X16)
        | v2_struct_0(k7_filter_1(X15,X16))
        | ~ v10_lattices(k7_filter_1(X15,X16))
        | ~ v15_lattices(k7_filter_1(X15,X16))
        | ~ v16_lattices(k7_filter_1(X15,X16))
        | ~ l3_lattices(k7_filter_1(X15,X16))
        | ~ epred2_2(X16,X15) )
      & ( v10_lattices(X16)
        | v2_struct_0(k7_filter_1(X15,X16))
        | ~ v10_lattices(k7_filter_1(X15,X16))
        | ~ v15_lattices(k7_filter_1(X15,X16))
        | ~ v16_lattices(k7_filter_1(X15,X16))
        | ~ l3_lattices(k7_filter_1(X15,X16))
        | ~ epred2_2(X16,X15) )
      & ( v15_lattices(X16)
        | v2_struct_0(k7_filter_1(X15,X16))
        | ~ v10_lattices(k7_filter_1(X15,X16))
        | ~ v15_lattices(k7_filter_1(X15,X16))
        | ~ v16_lattices(k7_filter_1(X15,X16))
        | ~ l3_lattices(k7_filter_1(X15,X16))
        | ~ epred2_2(X16,X15) )
      & ( v16_lattices(X16)
        | v2_struct_0(k7_filter_1(X15,X16))
        | ~ v10_lattices(k7_filter_1(X15,X16))
        | ~ v15_lattices(k7_filter_1(X15,X16))
        | ~ v16_lattices(k7_filter_1(X15,X16))
        | ~ l3_lattices(k7_filter_1(X15,X16))
        | ~ epred2_2(X16,X15) )
      & ( l3_lattices(X16)
        | v2_struct_0(k7_filter_1(X15,X16))
        | ~ v10_lattices(k7_filter_1(X15,X16))
        | ~ v15_lattices(k7_filter_1(X15,X16))
        | ~ v16_lattices(k7_filter_1(X15,X16))
        | ~ l3_lattices(k7_filter_1(X15,X16))
        | ~ epred2_2(X16,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_30])])])])).

cnf(c_0_34,plain,
    ( v16_lattices(X1)
    | v2_struct_0(X1)
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_35,negated_conjecture,
    ( l3_lattices(k7_filter_1(esk1_0,esk2_0))
    | v17_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_36,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v10_lattices(X2)
            & l3_lattices(X2) )
         => epred2_2(X2,X1) ) ) ),
    inference(apply_def,[status(thm)],[t46_filter_1,c_0_24])).

cnf(c_0_37,plain,
    ( v15_lattices(X1)
    | v2_struct_0(X1)
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_38,plain,
    ( v11_lattices(esk1_0)
    | v2_struct_0(k7_filter_1(esk1_0,esk2_0))
    | ~ epred1_2(esk2_0,esk1_0)
    | ~ v11_lattices(k7_filter_1(esk1_0,esk2_0))
    | ~ l3_lattices(k7_filter_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

fof(c_0_39,plain,(
    ! [X5,X6] :
      ( ( v3_lattices(k7_filter_1(X5,X6))
        | v2_struct_0(X5)
        | ~ l3_lattices(X5)
        | v2_struct_0(X6)
        | ~ l3_lattices(X6) )
      & ( l3_lattices(k7_filter_1(X5,X6))
        | v2_struct_0(X5)
        | ~ l3_lattices(X5)
        | v2_struct_0(X6)
        | ~ l3_lattices(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_filter_1])])])])).

cnf(c_0_40,plain,
    ( v16_lattices(X1)
    | v2_struct_0(k7_filter_1(X1,X2))
    | ~ v10_lattices(k7_filter_1(X1,X2))
    | ~ v15_lattices(k7_filter_1(X1,X2))
    | ~ v16_lattices(k7_filter_1(X1,X2))
    | ~ l3_lattices(k7_filter_1(X1,X2))
    | ~ epred2_2(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,negated_conjecture,
    ( v10_lattices(k7_filter_1(esk1_0,esk2_0))
    | v16_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_26]),c_0_28])]),c_0_29])).

cnf(c_0_42,negated_conjecture,
    ( v16_lattices(esk1_0)
    | l3_lattices(k7_filter_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_28])]),c_0_29])).

fof(c_0_43,plain,(
    ! [X9,X10] :
      ( v2_struct_0(X9)
      | ~ v10_lattices(X9)
      | ~ l3_lattices(X9)
      | v2_struct_0(X10)
      | ~ v10_lattices(X10)
      | ~ l3_lattices(X10)
      | epred2_2(X10,X9) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_36])])])])).

cnf(c_0_44,plain,
    ( v15_lattices(X1)
    | v2_struct_0(k7_filter_1(X1,X2))
    | ~ v10_lattices(k7_filter_1(X1,X2))
    | ~ v15_lattices(k7_filter_1(X1,X2))
    | ~ v16_lattices(k7_filter_1(X1,X2))
    | ~ l3_lattices(k7_filter_1(X1,X2))
    | ~ epred2_2(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_45,negated_conjecture,
    ( v10_lattices(k7_filter_1(esk1_0,esk2_0))
    | v15_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_26]),c_0_28])]),c_0_29])).

cnf(c_0_46,negated_conjecture,
    ( v15_lattices(esk1_0)
    | l3_lattices(k7_filter_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_35]),c_0_28])]),c_0_29])).

cnf(c_0_47,plain,
    ( v11_lattices(X1)
    | v2_struct_0(k7_filter_1(X2,X1))
    | ~ v10_lattices(k7_filter_1(X2,X1))
    | ~ v11_lattices(k7_filter_1(X2,X1))
    | ~ l3_lattices(k7_filter_1(X2,X1))
    | ~ epred1_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_48,negated_conjecture,
    ( l3_lattices(k7_filter_1(esk1_0,esk2_0))
    | v17_lattices(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_49,plain,
    ( v11_lattices(esk1_0)
    | v2_struct_0(k7_filter_1(esk1_0,esk2_0))
    | ~ v11_lattices(k7_filter_1(esk1_0,esk2_0))
    | ~ l3_lattices(k7_filter_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_12]),c_0_21]),c_0_27]),c_0_22]),c_0_28])]),c_0_29]),c_0_23])).

cnf(c_0_50,plain,
    ( l3_lattices(k7_filter_1(X1,X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l3_lattices(X1)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_51,plain,
    ( v16_lattices(esk1_0)
    | v2_struct_0(k7_filter_1(esk1_0,esk2_0))
    | ~ epred2_2(esk2_0,esk1_0)
    | ~ v16_lattices(k7_filter_1(esk1_0,esk2_0))
    | ~ v15_lattices(k7_filter_1(esk1_0,esk2_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])).

cnf(c_0_52,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | epred2_2(X2,X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_53,negated_conjecture,
    ( v17_lattices(k7_filter_1(esk1_0,esk2_0))
    | v17_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_54,negated_conjecture,
    ( v17_lattices(esk1_0)
    | ~ v2_struct_0(k7_filter_1(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_55,plain,
    ( v15_lattices(esk1_0)
    | v2_struct_0(k7_filter_1(esk1_0,esk2_0))
    | ~ epred2_2(esk2_0,esk1_0)
    | ~ v16_lattices(k7_filter_1(esk1_0,esk2_0))
    | ~ v15_lattices(k7_filter_1(esk1_0,esk2_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46])).

cnf(c_0_56,plain,
    ( v11_lattices(esk2_0)
    | v2_struct_0(k7_filter_1(esk1_0,esk2_0))
    | ~ epred1_2(esk2_0,esk1_0)
    | ~ v11_lattices(k7_filter_1(esk1_0,esk2_0))
    | ~ l3_lattices(k7_filter_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_32])).

cnf(c_0_57,plain,
    ( v16_lattices(X1)
    | v2_struct_0(k7_filter_1(X2,X1))
    | ~ v10_lattices(k7_filter_1(X2,X1))
    | ~ v15_lattices(k7_filter_1(X2,X1))
    | ~ v16_lattices(k7_filter_1(X2,X1))
    | ~ l3_lattices(k7_filter_1(X2,X1))
    | ~ epred2_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_58,negated_conjecture,
    ( v10_lattices(k7_filter_1(esk1_0,esk2_0))
    | v16_lattices(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_20]),c_0_22])]),c_0_23])).

cnf(c_0_59,negated_conjecture,
    ( v16_lattices(esk2_0)
    | l3_lattices(k7_filter_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_48]),c_0_22])]),c_0_23])).

cnf(c_0_60,plain,
    ( v15_lattices(X1)
    | v2_struct_0(k7_filter_1(X2,X1))
    | ~ v10_lattices(k7_filter_1(X2,X1))
    | ~ v15_lattices(k7_filter_1(X2,X1))
    | ~ v16_lattices(k7_filter_1(X2,X1))
    | ~ l3_lattices(k7_filter_1(X2,X1))
    | ~ epred2_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_61,negated_conjecture,
    ( v10_lattices(k7_filter_1(esk1_0,esk2_0))
    | v15_lattices(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_20]),c_0_22])]),c_0_23])).

cnf(c_0_62,negated_conjecture,
    ( v15_lattices(esk2_0)
    | l3_lattices(k7_filter_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_48]),c_0_22])]),c_0_23])).

cnf(c_0_63,plain,
    ( v11_lattices(esk1_0)
    | v2_struct_0(k7_filter_1(esk1_0,esk2_0))
    | ~ v11_lattices(k7_filter_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_22]),c_0_28])]),c_0_29]),c_0_23])).

cnf(c_0_64,plain,
    ( v16_lattices(esk1_0)
    | v2_struct_0(k7_filter_1(esk1_0,esk2_0))
    | ~ v16_lattices(k7_filter_1(esk1_0,esk2_0))
    | ~ v15_lattices(k7_filter_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_21]),c_0_27]),c_0_22]),c_0_28])]),c_0_29]),c_0_23])).

cnf(c_0_65,negated_conjecture,
    ( v15_lattices(k7_filter_1(esk1_0,esk2_0))
    | v17_lattices(esk1_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_53]),c_0_35]),c_0_54])).

cnf(c_0_66,negated_conjecture,
    ( v16_lattices(k7_filter_1(esk1_0,esk2_0))
    | v17_lattices(esk1_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_53]),c_0_35]),c_0_54])).

cnf(c_0_67,plain,
    ( v15_lattices(esk1_0)
    | v2_struct_0(k7_filter_1(esk1_0,esk2_0))
    | ~ v16_lattices(k7_filter_1(esk1_0,esk2_0))
    | ~ v15_lattices(k7_filter_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_52]),c_0_21]),c_0_27]),c_0_22]),c_0_28])]),c_0_29]),c_0_23])).

cnf(c_0_68,plain,
    ( v11_lattices(esk2_0)
    | v2_struct_0(k7_filter_1(esk1_0,esk2_0))
    | ~ v11_lattices(k7_filter_1(esk1_0,esk2_0))
    | ~ l3_lattices(k7_filter_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_12]),c_0_21]),c_0_27]),c_0_22]),c_0_28])]),c_0_29]),c_0_23])).

cnf(c_0_69,plain,
    ( v16_lattices(esk2_0)
    | v2_struct_0(k7_filter_1(esk1_0,esk2_0))
    | ~ epred2_2(esk2_0,esk1_0)
    | ~ v16_lattices(k7_filter_1(esk1_0,esk2_0))
    | ~ v15_lattices(k7_filter_1(esk1_0,esk2_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59])).

cnf(c_0_70,negated_conjecture,
    ( v17_lattices(k7_filter_1(esk1_0,esk2_0))
    | v17_lattices(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_71,negated_conjecture,
    ( v17_lattices(esk2_0)
    | ~ v2_struct_0(k7_filter_1(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_72,plain,
    ( v15_lattices(esk2_0)
    | v2_struct_0(k7_filter_1(esk1_0,esk2_0))
    | ~ epred2_2(esk2_0,esk1_0)
    | ~ v16_lattices(k7_filter_1(esk1_0,esk2_0))
    | ~ v15_lattices(k7_filter_1(esk1_0,esk2_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_62])).

cnf(c_0_73,negated_conjecture,
    ( v2_struct_0(esk1_0)
    | v2_struct_0(esk2_0)
    | v2_struct_0(k7_filter_1(esk1_0,esk2_0))
    | ~ v10_lattices(esk1_0)
    | ~ v17_lattices(esk1_0)
    | ~ l3_lattices(esk1_0)
    | ~ v10_lattices(esk2_0)
    | ~ v17_lattices(esk2_0)
    | ~ l3_lattices(esk2_0)
    | ~ v10_lattices(k7_filter_1(esk1_0,esk2_0))
    | ~ v17_lattices(k7_filter_1(esk1_0,esk2_0))
    | ~ l3_lattices(k7_filter_1(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_74,plain,(
    ! [X4] :
      ( ( ~ v2_struct_0(X4)
        | v2_struct_0(X4)
        | ~ v11_lattices(X4)
        | ~ v15_lattices(X4)
        | ~ v16_lattices(X4)
        | ~ l3_lattices(X4) )
      & ( v17_lattices(X4)
        | v2_struct_0(X4)
        | ~ v11_lattices(X4)
        | ~ v15_lattices(X4)
        | ~ v16_lattices(X4)
        | ~ l3_lattices(X4) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc6_lattices])])])])).

cnf(c_0_75,plain,
    ( v11_lattices(esk1_0)
    | v2_struct_0(k7_filter_1(esk1_0,esk2_0))
    | ~ v17_lattices(k7_filter_1(esk1_0,esk2_0))
    | ~ l3_lattices(k7_filter_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_15])).

cnf(c_0_76,negated_conjecture,
    ( v16_lattices(esk1_0)
    | v17_lattices(esk1_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_66]),c_0_54])).

cnf(c_0_77,negated_conjecture,
    ( v15_lattices(esk1_0)
    | v17_lattices(esk1_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_66]),c_0_65]),c_0_54])).

cnf(c_0_78,plain,
    ( v11_lattices(esk2_0)
    | v2_struct_0(k7_filter_1(esk1_0,esk2_0))
    | ~ v11_lattices(k7_filter_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_50]),c_0_22]),c_0_28])]),c_0_29]),c_0_23])).

cnf(c_0_79,plain,
    ( v16_lattices(esk2_0)
    | v2_struct_0(k7_filter_1(esk1_0,esk2_0))
    | ~ v16_lattices(k7_filter_1(esk1_0,esk2_0))
    | ~ v15_lattices(k7_filter_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_52]),c_0_21]),c_0_27]),c_0_22]),c_0_28])]),c_0_29]),c_0_23])).

cnf(c_0_80,negated_conjecture,
    ( v15_lattices(k7_filter_1(esk1_0,esk2_0))
    | v17_lattices(esk2_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_70]),c_0_48]),c_0_71])).

cnf(c_0_81,negated_conjecture,
    ( v16_lattices(k7_filter_1(esk1_0,esk2_0))
    | v17_lattices(esk2_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_70]),c_0_48]),c_0_71])).

cnf(c_0_82,plain,
    ( v15_lattices(esk2_0)
    | v2_struct_0(k7_filter_1(esk1_0,esk2_0))
    | ~ v16_lattices(k7_filter_1(esk1_0,esk2_0))
    | ~ v15_lattices(k7_filter_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_52]),c_0_21]),c_0_27]),c_0_22]),c_0_28])]),c_0_29]),c_0_23])).

cnf(c_0_83,negated_conjecture,
    ( v2_struct_0(k7_filter_1(esk1_0,esk2_0))
    | ~ v10_lattices(k7_filter_1(esk1_0,esk2_0))
    | ~ v17_lattices(k7_filter_1(esk1_0,esk2_0))
    | ~ v17_lattices(esk1_0)
    | ~ v17_lattices(esk2_0)
    | ~ l3_lattices(k7_filter_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_28]),c_0_22]),c_0_27]),c_0_21])]),c_0_29]),c_0_23])).

cnf(c_0_84,plain,
    ( v17_lattices(X1)
    | v2_struct_0(X1)
    | ~ v11_lattices(X1)
    | ~ v15_lattices(X1)
    | ~ v16_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_85,negated_conjecture,
    ( v11_lattices(esk1_0)
    | v17_lattices(esk1_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_53]),c_0_35]),c_0_54])).

cnf(c_0_86,negated_conjecture,
    ( v16_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_76]),c_0_28])]),c_0_29])).

cnf(c_0_87,negated_conjecture,
    ( v15_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_77]),c_0_28])]),c_0_29])).

cnf(c_0_88,plain,
    ( v11_lattices(esk2_0)
    | v2_struct_0(k7_filter_1(esk1_0,esk2_0))
    | ~ v17_lattices(k7_filter_1(esk1_0,esk2_0))
    | ~ l3_lattices(k7_filter_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_78,c_0_15])).

cnf(c_0_89,negated_conjecture,
    ( v16_lattices(esk2_0)
    | v17_lattices(esk2_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_81]),c_0_71])).

cnf(c_0_90,negated_conjecture,
    ( v15_lattices(esk2_0)
    | v17_lattices(esk2_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_81]),c_0_80]),c_0_71])).

cnf(c_0_91,plain,
    ( v11_lattices(k7_filter_1(X1,X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v10_lattices(X1)
    | ~ v11_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X2)
    | ~ v11_lattices(X2)
    | ~ l3_lattices(X2)
    | ~ epred1_2(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_92,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_struct_0(k7_filter_1(X1,X2))
    | ~ v10_lattices(X1)
    | ~ v11_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X2)
    | ~ v11_lattices(X2)
    | ~ l3_lattices(X2)
    | ~ epred1_2(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_93,negated_conjecture,
    ( v2_struct_0(k7_filter_1(esk1_0,esk2_0))
    | ~ v17_lattices(k7_filter_1(esk1_0,esk2_0))
    | ~ v17_lattices(esk1_0)
    | ~ v17_lattices(esk2_0)
    | ~ l3_lattices(k7_filter_1(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_83,c_0_32])])).

cnf(c_0_94,negated_conjecture,
    ( v17_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_86]),c_0_87]),c_0_28])]),c_0_29])).

cnf(c_0_95,negated_conjecture,
    ( v11_lattices(esk2_0)
    | v17_lattices(esk2_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_70]),c_0_48]),c_0_71])).

cnf(c_0_96,negated_conjecture,
    ( v16_lattices(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_89]),c_0_22])]),c_0_23])).

cnf(c_0_97,negated_conjecture,
    ( v15_lattices(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_90]),c_0_22])]),c_0_23])).

cnf(c_0_98,plain,
    ( v11_lattices(k7_filter_1(X1,X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v10_lattices(X2)
    | ~ v10_lattices(X1)
    | ~ v11_lattices(X2)
    | ~ v11_lattices(X1)
    | ~ l3_lattices(X2)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[c_0_91,c_0_12])).

cnf(c_0_99,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v10_lattices(X2)
    | ~ v10_lattices(X1)
    | ~ v11_lattices(X2)
    | ~ v11_lattices(X1)
    | ~ v2_struct_0(k7_filter_1(X1,X2))
    | ~ l3_lattices(X2)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[c_0_92,c_0_12])).

cnf(c_0_100,plain,
    ( v16_lattices(k7_filter_1(X1,X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v10_lattices(X1)
    | ~ v15_lattices(X1)
    | ~ v16_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X2)
    | ~ v15_lattices(X2)
    | ~ v16_lattices(X2)
    | ~ l3_lattices(X2)
    | ~ epred2_2(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_101,plain,
    ( v15_lattices(k7_filter_1(X1,X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v10_lattices(X1)
    | ~ v15_lattices(X1)
    | ~ v16_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X2)
    | ~ v15_lattices(X2)
    | ~ v16_lattices(X2)
    | ~ l3_lattices(X2)
    | ~ epred2_2(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_102,negated_conjecture,
    ( v2_struct_0(k7_filter_1(esk1_0,esk2_0))
    | ~ v17_lattices(k7_filter_1(esk1_0,esk2_0))
    | ~ v17_lattices(esk2_0)
    | ~ l3_lattices(k7_filter_1(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_93,c_0_94])])).

cnf(c_0_103,negated_conjecture,
    ( v17_lattices(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_95]),c_0_96]),c_0_97]),c_0_22])]),c_0_23])).

cnf(c_0_104,plain,
    ( v17_lattices(k7_filter_1(X1,X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v10_lattices(X2)
    | ~ v10_lattices(X1)
    | ~ v16_lattices(k7_filter_1(X1,X2))
    | ~ v15_lattices(k7_filter_1(X1,X2))
    | ~ v11_lattices(X2)
    | ~ v11_lattices(X1)
    | ~ l3_lattices(X2)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_98]),c_0_50]),c_0_99])).

cnf(c_0_105,plain,
    ( v16_lattices(k7_filter_1(X1,X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v10_lattices(X2)
    | ~ v10_lattices(X1)
    | ~ v16_lattices(X2)
    | ~ v16_lattices(X1)
    | ~ v15_lattices(X2)
    | ~ v15_lattices(X1)
    | ~ l3_lattices(X2)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[c_0_100,c_0_52])).

cnf(c_0_106,plain,
    ( v15_lattices(k7_filter_1(X1,X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v10_lattices(X2)
    | ~ v10_lattices(X1)
    | ~ v16_lattices(X2)
    | ~ v16_lattices(X1)
    | ~ v15_lattices(X2)
    | ~ v15_lattices(X1)
    | ~ l3_lattices(X2)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[c_0_101,c_0_52])).

cnf(c_0_107,negated_conjecture,
    ( v2_struct_0(k7_filter_1(esk1_0,esk2_0))
    | ~ v17_lattices(k7_filter_1(esk1_0,esk2_0))
    | ~ l3_lattices(k7_filter_1(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_102,c_0_103])])).

cnf(c_0_108,plain,
    ( v17_lattices(k7_filter_1(X1,X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v10_lattices(X2)
    | ~ v10_lattices(X1)
    | ~ v16_lattices(X2)
    | ~ v16_lattices(X1)
    | ~ v15_lattices(X2)
    | ~ v15_lattices(X1)
    | ~ v11_lattices(X2)
    | ~ v11_lattices(X1)
    | ~ l3_lattices(X2)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_105]),c_0_106])).

cnf(c_0_109,negated_conjecture,
    ( v2_struct_0(k7_filter_1(esk1_0,esk2_0))
    | ~ v11_lattices(esk2_0)
    | ~ v11_lattices(esk1_0)
    | ~ l3_lattices(k7_filter_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_108]),c_0_21]),c_0_27]),c_0_96]),c_0_86]),c_0_97]),c_0_87]),c_0_22]),c_0_28])]),c_0_29]),c_0_23])).

cnf(c_0_110,negated_conjecture,
    ( v2_struct_0(k7_filter_1(esk1_0,esk2_0))
    | ~ v11_lattices(esk1_0)
    | ~ l3_lattices(k7_filter_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_15]),c_0_103]),c_0_22])]),c_0_23])).

cnf(c_0_111,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_struct_0(k7_filter_1(X1,X2))
    | ~ v10_lattices(X1)
    | ~ v15_lattices(X1)
    | ~ v16_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X2)
    | ~ v15_lattices(X2)
    | ~ v16_lattices(X2)
    | ~ l3_lattices(X2)
    | ~ epred2_2(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_112,negated_conjecture,
    ( v2_struct_0(k7_filter_1(esk1_0,esk2_0))
    | ~ l3_lattices(k7_filter_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_15]),c_0_94]),c_0_28])]),c_0_29])).

cnf(c_0_113,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v10_lattices(X2)
    | ~ v10_lattices(X1)
    | ~ v16_lattices(X2)
    | ~ v16_lattices(X1)
    | ~ v15_lattices(X2)
    | ~ v15_lattices(X1)
    | ~ v2_struct_0(k7_filter_1(X1,X2))
    | ~ l3_lattices(X2)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[c_0_111,c_0_52])).

cnf(c_0_114,negated_conjecture,
    ( v2_struct_0(k7_filter_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_50]),c_0_22]),c_0_28])]),c_0_29]),c_0_23])).

cnf(c_0_115,plain,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_114]),c_0_21]),c_0_27]),c_0_96]),c_0_86]),c_0_97]),c_0_87]),c_0_22]),c_0_28])]),c_0_29]),c_0_23]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 20:52:25 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.20/0.33  # Version: 2.5pre002
% 0.20/0.34  # No SInE strategy applied
% 0.20/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___008_C45_F1_PI_S5PRR_SE_Q4_CS_SP_S4S
% 0.20/0.38  # and selection function SelectNewComplexAHPNS.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.029 s
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(t39_filter_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v10_lattices(X1))&l3_lattices(X1))=>![X2]:(((~(v2_struct_0(X2))&v10_lattices(X2))&l3_lattices(X2))=>((((((((~(v2_struct_0(X1))&v10_lattices(X1))&v11_lattices(X1))&l3_lattices(X1))&~(v2_struct_0(X2)))&v10_lattices(X2))&v11_lattices(X2))&l3_lattices(X2))<=>(((~(v2_struct_0(k7_filter_1(X1,X2)))&v10_lattices(k7_filter_1(X1,X2)))&v11_lattices(k7_filter_1(X1,X2)))&l3_lattices(k7_filter_1(X1,X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_filter_1)).
% 0.20/0.38  fof(cc5_lattices, axiom, ![X1]:(l3_lattices(X1)=>((~(v2_struct_0(X1))&v17_lattices(X1))=>(((~(v2_struct_0(X1))&v11_lattices(X1))&v15_lattices(X1))&v16_lattices(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_lattices)).
% 0.20/0.38  fof(t47_filter_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v10_lattices(X1))&l3_lattices(X1))=>![X2]:(((~(v2_struct_0(X2))&v10_lattices(X2))&l3_lattices(X2))=>((((((((~(v2_struct_0(X1))&v10_lattices(X1))&v17_lattices(X1))&l3_lattices(X1))&~(v2_struct_0(X2)))&v10_lattices(X2))&v17_lattices(X2))&l3_lattices(X2))<=>(((~(v2_struct_0(k7_filter_1(X1,X2)))&v10_lattices(k7_filter_1(X1,X2)))&v17_lattices(k7_filter_1(X1,X2)))&l3_lattices(k7_filter_1(X1,X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_filter_1)).
% 0.20/0.38  fof(t46_filter_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v10_lattices(X1))&l3_lattices(X1))=>![X2]:(((~(v2_struct_0(X2))&v10_lattices(X2))&l3_lattices(X2))=>((((((((((~(v2_struct_0(X1))&v10_lattices(X1))&v15_lattices(X1))&v16_lattices(X1))&l3_lattices(X1))&~(v2_struct_0(X2)))&v10_lattices(X2))&v15_lattices(X2))&v16_lattices(X2))&l3_lattices(X2))<=>((((~(v2_struct_0(k7_filter_1(X1,X2)))&v10_lattices(k7_filter_1(X1,X2)))&v15_lattices(k7_filter_1(X1,X2)))&v16_lattices(k7_filter_1(X1,X2)))&l3_lattices(k7_filter_1(X1,X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_filter_1)).
% 0.20/0.38  fof(dt_k7_filter_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&l3_lattices(X1))&~(v2_struct_0(X2)))&l3_lattices(X2))=>(v3_lattices(k7_filter_1(X1,X2))&l3_lattices(k7_filter_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_filter_1)).
% 0.20/0.38  fof(cc6_lattices, axiom, ![X1]:(l3_lattices(X1)=>((((~(v2_struct_0(X1))&v11_lattices(X1))&v15_lattices(X1))&v16_lattices(X1))=>(~(v2_struct_0(X1))&v17_lattices(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc6_lattices)).
% 0.20/0.38  fof(c_0_6, plain, ![X1, X2]:(epred1_2(X2,X1)<=>((((((((~(v2_struct_0(X1))&v10_lattices(X1))&v11_lattices(X1))&l3_lattices(X1))&~(v2_struct_0(X2)))&v10_lattices(X2))&v11_lattices(X2))&l3_lattices(X2))<=>(((~(v2_struct_0(k7_filter_1(X1,X2)))&v10_lattices(k7_filter_1(X1,X2)))&v11_lattices(k7_filter_1(X1,X2)))&l3_lattices(k7_filter_1(X1,X2))))), introduced(definition)).
% 0.20/0.38  fof(c_0_7, plain, ![X1, X2]:(epred1_2(X2,X1)=>((((((((~(v2_struct_0(X1))&v10_lattices(X1))&v11_lattices(X1))&l3_lattices(X1))&~(v2_struct_0(X2)))&v10_lattices(X2))&v11_lattices(X2))&l3_lattices(X2))<=>(((~(v2_struct_0(k7_filter_1(X1,X2)))&v10_lattices(k7_filter_1(X1,X2)))&v11_lattices(k7_filter_1(X1,X2)))&l3_lattices(k7_filter_1(X1,X2))))), inference(split_equiv,[status(thm)],[c_0_6])).
% 0.20/0.38  fof(c_0_8, axiom, ![X1]:(((~(v2_struct_0(X1))&v10_lattices(X1))&l3_lattices(X1))=>![X2]:(((~(v2_struct_0(X2))&v10_lattices(X2))&l3_lattices(X2))=>epred1_2(X2,X1))), inference(apply_def,[status(thm)],[t39_filter_1, c_0_6])).
% 0.20/0.38  fof(c_0_9, plain, ![X13, X14]:(((((~v2_struct_0(k7_filter_1(X13,X14))|(v2_struct_0(X13)|~v10_lattices(X13)|~v11_lattices(X13)|~l3_lattices(X13)|v2_struct_0(X14)|~v10_lattices(X14)|~v11_lattices(X14)|~l3_lattices(X14))|~epred1_2(X14,X13))&(v10_lattices(k7_filter_1(X13,X14))|(v2_struct_0(X13)|~v10_lattices(X13)|~v11_lattices(X13)|~l3_lattices(X13)|v2_struct_0(X14)|~v10_lattices(X14)|~v11_lattices(X14)|~l3_lattices(X14))|~epred1_2(X14,X13)))&(v11_lattices(k7_filter_1(X13,X14))|(v2_struct_0(X13)|~v10_lattices(X13)|~v11_lattices(X13)|~l3_lattices(X13)|v2_struct_0(X14)|~v10_lattices(X14)|~v11_lattices(X14)|~l3_lattices(X14))|~epred1_2(X14,X13)))&(l3_lattices(k7_filter_1(X13,X14))|(v2_struct_0(X13)|~v10_lattices(X13)|~v11_lattices(X13)|~l3_lattices(X13)|v2_struct_0(X14)|~v10_lattices(X14)|~v11_lattices(X14)|~l3_lattices(X14))|~epred1_2(X14,X13)))&((((((((~v2_struct_0(X13)|(v2_struct_0(k7_filter_1(X13,X14))|~v10_lattices(k7_filter_1(X13,X14))|~v11_lattices(k7_filter_1(X13,X14))|~l3_lattices(k7_filter_1(X13,X14)))|~epred1_2(X14,X13))&(v10_lattices(X13)|(v2_struct_0(k7_filter_1(X13,X14))|~v10_lattices(k7_filter_1(X13,X14))|~v11_lattices(k7_filter_1(X13,X14))|~l3_lattices(k7_filter_1(X13,X14)))|~epred1_2(X14,X13)))&(v11_lattices(X13)|(v2_struct_0(k7_filter_1(X13,X14))|~v10_lattices(k7_filter_1(X13,X14))|~v11_lattices(k7_filter_1(X13,X14))|~l3_lattices(k7_filter_1(X13,X14)))|~epred1_2(X14,X13)))&(l3_lattices(X13)|(v2_struct_0(k7_filter_1(X13,X14))|~v10_lattices(k7_filter_1(X13,X14))|~v11_lattices(k7_filter_1(X13,X14))|~l3_lattices(k7_filter_1(X13,X14)))|~epred1_2(X14,X13)))&(~v2_struct_0(X14)|(v2_struct_0(k7_filter_1(X13,X14))|~v10_lattices(k7_filter_1(X13,X14))|~v11_lattices(k7_filter_1(X13,X14))|~l3_lattices(k7_filter_1(X13,X14)))|~epred1_2(X14,X13)))&(v10_lattices(X14)|(v2_struct_0(k7_filter_1(X13,X14))|~v10_lattices(k7_filter_1(X13,X14))|~v11_lattices(k7_filter_1(X13,X14))|~l3_lattices(k7_filter_1(X13,X14)))|~epred1_2(X14,X13)))&(v11_lattices(X14)|(v2_struct_0(k7_filter_1(X13,X14))|~v10_lattices(k7_filter_1(X13,X14))|~v11_lattices(k7_filter_1(X13,X14))|~l3_lattices(k7_filter_1(X13,X14)))|~epred1_2(X14,X13)))&(l3_lattices(X14)|(v2_struct_0(k7_filter_1(X13,X14))|~v10_lattices(k7_filter_1(X13,X14))|~v11_lattices(k7_filter_1(X13,X14))|~l3_lattices(k7_filter_1(X13,X14)))|~epred1_2(X14,X13)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])).
% 0.20/0.38  fof(c_0_10, plain, ![X7, X8]:(v2_struct_0(X7)|~v10_lattices(X7)|~l3_lattices(X7)|(v2_struct_0(X8)|~v10_lattices(X8)|~l3_lattices(X8)|epred1_2(X8,X7))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).
% 0.20/0.38  cnf(c_0_11, plain, (v10_lattices(k7_filter_1(X1,X2))|v2_struct_0(X1)|v2_struct_0(X2)|~v10_lattices(X1)|~v11_lattices(X1)|~l3_lattices(X1)|~v10_lattices(X2)|~v11_lattices(X2)|~l3_lattices(X2)|~epred1_2(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.38  cnf(c_0_12, plain, (v2_struct_0(X1)|v2_struct_0(X2)|epred1_2(X2,X1)|~v10_lattices(X1)|~l3_lattices(X1)|~v10_lattices(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.38  fof(c_0_13, plain, ![X3]:((((~v2_struct_0(X3)|(v2_struct_0(X3)|~v17_lattices(X3))|~l3_lattices(X3))&(v11_lattices(X3)|(v2_struct_0(X3)|~v17_lattices(X3))|~l3_lattices(X3)))&(v15_lattices(X3)|(v2_struct_0(X3)|~v17_lattices(X3))|~l3_lattices(X3)))&(v16_lattices(X3)|(v2_struct_0(X3)|~v17_lattices(X3))|~l3_lattices(X3))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_lattices])])])])).
% 0.20/0.38  cnf(c_0_14, plain, (v10_lattices(k7_filter_1(X1,X2))|v2_struct_0(X1)|v2_struct_0(X2)|~v10_lattices(X2)|~v10_lattices(X1)|~v11_lattices(X2)|~v11_lattices(X1)|~l3_lattices(X2)|~l3_lattices(X1)), inference(csr,[status(thm)],[c_0_11, c_0_12])).
% 0.20/0.38  cnf(c_0_15, plain, (v11_lattices(X1)|v2_struct_0(X1)|~v17_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.38  fof(c_0_16, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v10_lattices(X1))&l3_lattices(X1))=>![X2]:(((~(v2_struct_0(X2))&v10_lattices(X2))&l3_lattices(X2))=>((((((((~(v2_struct_0(X1))&v10_lattices(X1))&v17_lattices(X1))&l3_lattices(X1))&~(v2_struct_0(X2)))&v10_lattices(X2))&v17_lattices(X2))&l3_lattices(X2))<=>(((~(v2_struct_0(k7_filter_1(X1,X2)))&v10_lattices(k7_filter_1(X1,X2)))&v17_lattices(k7_filter_1(X1,X2)))&l3_lattices(k7_filter_1(X1,X2))))))), inference(assume_negation,[status(cth)],[t47_filter_1])).
% 0.20/0.38  cnf(c_0_17, plain, (v10_lattices(k7_filter_1(X1,X2))|v2_struct_0(X2)|v2_struct_0(X1)|~v10_lattices(X2)|~v10_lattices(X1)|~v11_lattices(X2)|~v17_lattices(X1)|~l3_lattices(X2)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.20/0.38  fof(c_0_18, negated_conjecture, (((~v2_struct_0(esk1_0)&v10_lattices(esk1_0))&l3_lattices(esk1_0))&(((~v2_struct_0(esk2_0)&v10_lattices(esk2_0))&l3_lattices(esk2_0))&((v2_struct_0(esk1_0)|~v10_lattices(esk1_0)|~v17_lattices(esk1_0)|~l3_lattices(esk1_0)|v2_struct_0(esk2_0)|~v10_lattices(esk2_0)|~v17_lattices(esk2_0)|~l3_lattices(esk2_0)|(v2_struct_0(k7_filter_1(esk1_0,esk2_0))|~v10_lattices(k7_filter_1(esk1_0,esk2_0))|~v17_lattices(k7_filter_1(esk1_0,esk2_0))|~l3_lattices(k7_filter_1(esk1_0,esk2_0))))&(((((((((((~v2_struct_0(k7_filter_1(esk1_0,esk2_0))|~v2_struct_0(esk1_0))&(v10_lattices(k7_filter_1(esk1_0,esk2_0))|~v2_struct_0(esk1_0)))&(v17_lattices(k7_filter_1(esk1_0,esk2_0))|~v2_struct_0(esk1_0)))&(l3_lattices(k7_filter_1(esk1_0,esk2_0))|~v2_struct_0(esk1_0)))&((((~v2_struct_0(k7_filter_1(esk1_0,esk2_0))|v10_lattices(esk1_0))&(v10_lattices(k7_filter_1(esk1_0,esk2_0))|v10_lattices(esk1_0)))&(v17_lattices(k7_filter_1(esk1_0,esk2_0))|v10_lattices(esk1_0)))&(l3_lattices(k7_filter_1(esk1_0,esk2_0))|v10_lattices(esk1_0))))&((((~v2_struct_0(k7_filter_1(esk1_0,esk2_0))|v17_lattices(esk1_0))&(v10_lattices(k7_filter_1(esk1_0,esk2_0))|v17_lattices(esk1_0)))&(v17_lattices(k7_filter_1(esk1_0,esk2_0))|v17_lattices(esk1_0)))&(l3_lattices(k7_filter_1(esk1_0,esk2_0))|v17_lattices(esk1_0))))&((((~v2_struct_0(k7_filter_1(esk1_0,esk2_0))|l3_lattices(esk1_0))&(v10_lattices(k7_filter_1(esk1_0,esk2_0))|l3_lattices(esk1_0)))&(v17_lattices(k7_filter_1(esk1_0,esk2_0))|l3_lattices(esk1_0)))&(l3_lattices(k7_filter_1(esk1_0,esk2_0))|l3_lattices(esk1_0))))&((((~v2_struct_0(k7_filter_1(esk1_0,esk2_0))|~v2_struct_0(esk2_0))&(v10_lattices(k7_filter_1(esk1_0,esk2_0))|~v2_struct_0(esk2_0)))&(v17_lattices(k7_filter_1(esk1_0,esk2_0))|~v2_struct_0(esk2_0)))&(l3_lattices(k7_filter_1(esk1_0,esk2_0))|~v2_struct_0(esk2_0))))&((((~v2_struct_0(k7_filter_1(esk1_0,esk2_0))|v10_lattices(esk2_0))&(v10_lattices(k7_filter_1(esk1_0,esk2_0))|v10_lattices(esk2_0)))&(v17_lattices(k7_filter_1(esk1_0,esk2_0))|v10_lattices(esk2_0)))&(l3_lattices(k7_filter_1(esk1_0,esk2_0))|v10_lattices(esk2_0))))&((((~v2_struct_0(k7_filter_1(esk1_0,esk2_0))|v17_lattices(esk2_0))&(v10_lattices(k7_filter_1(esk1_0,esk2_0))|v17_lattices(esk2_0)))&(v17_lattices(k7_filter_1(esk1_0,esk2_0))|v17_lattices(esk2_0)))&(l3_lattices(k7_filter_1(esk1_0,esk2_0))|v17_lattices(esk2_0))))&((((~v2_struct_0(k7_filter_1(esk1_0,esk2_0))|l3_lattices(esk2_0))&(v10_lattices(k7_filter_1(esk1_0,esk2_0))|l3_lattices(esk2_0)))&(v17_lattices(k7_filter_1(esk1_0,esk2_0))|l3_lattices(esk2_0)))&(l3_lattices(k7_filter_1(esk1_0,esk2_0))|l3_lattices(esk2_0))))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])])).
% 0.20/0.38  cnf(c_0_19, plain, (v10_lattices(k7_filter_1(X1,X2))|v2_struct_0(X1)|v2_struct_0(X2)|~v10_lattices(X2)|~v10_lattices(X1)|~v17_lattices(X1)|~v17_lattices(X2)|~l3_lattices(X2)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_17, c_0_15])).
% 0.20/0.38  cnf(c_0_20, negated_conjecture, (v10_lattices(k7_filter_1(esk1_0,esk2_0))|v17_lattices(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.38  cnf(c_0_21, negated_conjecture, (v10_lattices(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.38  cnf(c_0_22, negated_conjecture, (l3_lattices(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.38  cnf(c_0_23, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.38  fof(c_0_24, plain, ![X1, X2]:(epred2_2(X2,X1)<=>((((((((((~(v2_struct_0(X1))&v10_lattices(X1))&v15_lattices(X1))&v16_lattices(X1))&l3_lattices(X1))&~(v2_struct_0(X2)))&v10_lattices(X2))&v15_lattices(X2))&v16_lattices(X2))&l3_lattices(X2))<=>((((~(v2_struct_0(k7_filter_1(X1,X2)))&v10_lattices(k7_filter_1(X1,X2)))&v15_lattices(k7_filter_1(X1,X2)))&v16_lattices(k7_filter_1(X1,X2)))&l3_lattices(k7_filter_1(X1,X2))))), introduced(definition)).
% 0.20/0.38  cnf(c_0_25, negated_conjecture, (v10_lattices(k7_filter_1(esk1_0,esk2_0))|v10_lattices(k7_filter_1(X1,esk2_0))|v2_struct_0(X1)|~v10_lattices(X1)|~v17_lattices(X1)|~l3_lattices(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21]), c_0_22])]), c_0_23])).
% 0.20/0.38  cnf(c_0_26, negated_conjecture, (v10_lattices(k7_filter_1(esk1_0,esk2_0))|v17_lattices(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.38  cnf(c_0_27, negated_conjecture, (v10_lattices(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.38  cnf(c_0_28, negated_conjecture, (l3_lattices(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.38  cnf(c_0_29, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.38  fof(c_0_30, plain, ![X1, X2]:(epred2_2(X2,X1)=>((((((((((~(v2_struct_0(X1))&v10_lattices(X1))&v15_lattices(X1))&v16_lattices(X1))&l3_lattices(X1))&~(v2_struct_0(X2)))&v10_lattices(X2))&v15_lattices(X2))&v16_lattices(X2))&l3_lattices(X2))<=>((((~(v2_struct_0(k7_filter_1(X1,X2)))&v10_lattices(k7_filter_1(X1,X2)))&v15_lattices(k7_filter_1(X1,X2)))&v16_lattices(k7_filter_1(X1,X2)))&l3_lattices(k7_filter_1(X1,X2))))), inference(split_equiv,[status(thm)],[c_0_24])).
% 0.20/0.38  cnf(c_0_31, plain, (v11_lattices(X1)|v2_struct_0(k7_filter_1(X1,X2))|~v10_lattices(k7_filter_1(X1,X2))|~v11_lattices(k7_filter_1(X1,X2))|~l3_lattices(k7_filter_1(X1,X2))|~epred1_2(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.38  cnf(c_0_32, negated_conjecture, (v10_lattices(k7_filter_1(esk1_0,esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27]), c_0_28])]), c_0_29])).
% 0.20/0.38  fof(c_0_33, plain, ![X15, X16]:((((((~v2_struct_0(k7_filter_1(X15,X16))|(v2_struct_0(X15)|~v10_lattices(X15)|~v15_lattices(X15)|~v16_lattices(X15)|~l3_lattices(X15)|v2_struct_0(X16)|~v10_lattices(X16)|~v15_lattices(X16)|~v16_lattices(X16)|~l3_lattices(X16))|~epred2_2(X16,X15))&(v10_lattices(k7_filter_1(X15,X16))|(v2_struct_0(X15)|~v10_lattices(X15)|~v15_lattices(X15)|~v16_lattices(X15)|~l3_lattices(X15)|v2_struct_0(X16)|~v10_lattices(X16)|~v15_lattices(X16)|~v16_lattices(X16)|~l3_lattices(X16))|~epred2_2(X16,X15)))&(v15_lattices(k7_filter_1(X15,X16))|(v2_struct_0(X15)|~v10_lattices(X15)|~v15_lattices(X15)|~v16_lattices(X15)|~l3_lattices(X15)|v2_struct_0(X16)|~v10_lattices(X16)|~v15_lattices(X16)|~v16_lattices(X16)|~l3_lattices(X16))|~epred2_2(X16,X15)))&(v16_lattices(k7_filter_1(X15,X16))|(v2_struct_0(X15)|~v10_lattices(X15)|~v15_lattices(X15)|~v16_lattices(X15)|~l3_lattices(X15)|v2_struct_0(X16)|~v10_lattices(X16)|~v15_lattices(X16)|~v16_lattices(X16)|~l3_lattices(X16))|~epred2_2(X16,X15)))&(l3_lattices(k7_filter_1(X15,X16))|(v2_struct_0(X15)|~v10_lattices(X15)|~v15_lattices(X15)|~v16_lattices(X15)|~l3_lattices(X15)|v2_struct_0(X16)|~v10_lattices(X16)|~v15_lattices(X16)|~v16_lattices(X16)|~l3_lattices(X16))|~epred2_2(X16,X15)))&((((((((((~v2_struct_0(X15)|(v2_struct_0(k7_filter_1(X15,X16))|~v10_lattices(k7_filter_1(X15,X16))|~v15_lattices(k7_filter_1(X15,X16))|~v16_lattices(k7_filter_1(X15,X16))|~l3_lattices(k7_filter_1(X15,X16)))|~epred2_2(X16,X15))&(v10_lattices(X15)|(v2_struct_0(k7_filter_1(X15,X16))|~v10_lattices(k7_filter_1(X15,X16))|~v15_lattices(k7_filter_1(X15,X16))|~v16_lattices(k7_filter_1(X15,X16))|~l3_lattices(k7_filter_1(X15,X16)))|~epred2_2(X16,X15)))&(v15_lattices(X15)|(v2_struct_0(k7_filter_1(X15,X16))|~v10_lattices(k7_filter_1(X15,X16))|~v15_lattices(k7_filter_1(X15,X16))|~v16_lattices(k7_filter_1(X15,X16))|~l3_lattices(k7_filter_1(X15,X16)))|~epred2_2(X16,X15)))&(v16_lattices(X15)|(v2_struct_0(k7_filter_1(X15,X16))|~v10_lattices(k7_filter_1(X15,X16))|~v15_lattices(k7_filter_1(X15,X16))|~v16_lattices(k7_filter_1(X15,X16))|~l3_lattices(k7_filter_1(X15,X16)))|~epred2_2(X16,X15)))&(l3_lattices(X15)|(v2_struct_0(k7_filter_1(X15,X16))|~v10_lattices(k7_filter_1(X15,X16))|~v15_lattices(k7_filter_1(X15,X16))|~v16_lattices(k7_filter_1(X15,X16))|~l3_lattices(k7_filter_1(X15,X16)))|~epred2_2(X16,X15)))&(~v2_struct_0(X16)|(v2_struct_0(k7_filter_1(X15,X16))|~v10_lattices(k7_filter_1(X15,X16))|~v15_lattices(k7_filter_1(X15,X16))|~v16_lattices(k7_filter_1(X15,X16))|~l3_lattices(k7_filter_1(X15,X16)))|~epred2_2(X16,X15)))&(v10_lattices(X16)|(v2_struct_0(k7_filter_1(X15,X16))|~v10_lattices(k7_filter_1(X15,X16))|~v15_lattices(k7_filter_1(X15,X16))|~v16_lattices(k7_filter_1(X15,X16))|~l3_lattices(k7_filter_1(X15,X16)))|~epred2_2(X16,X15)))&(v15_lattices(X16)|(v2_struct_0(k7_filter_1(X15,X16))|~v10_lattices(k7_filter_1(X15,X16))|~v15_lattices(k7_filter_1(X15,X16))|~v16_lattices(k7_filter_1(X15,X16))|~l3_lattices(k7_filter_1(X15,X16)))|~epred2_2(X16,X15)))&(v16_lattices(X16)|(v2_struct_0(k7_filter_1(X15,X16))|~v10_lattices(k7_filter_1(X15,X16))|~v15_lattices(k7_filter_1(X15,X16))|~v16_lattices(k7_filter_1(X15,X16))|~l3_lattices(k7_filter_1(X15,X16)))|~epred2_2(X16,X15)))&(l3_lattices(X16)|(v2_struct_0(k7_filter_1(X15,X16))|~v10_lattices(k7_filter_1(X15,X16))|~v15_lattices(k7_filter_1(X15,X16))|~v16_lattices(k7_filter_1(X15,X16))|~l3_lattices(k7_filter_1(X15,X16)))|~epred2_2(X16,X15)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_30])])])])).
% 0.20/0.38  cnf(c_0_34, plain, (v16_lattices(X1)|v2_struct_0(X1)|~v17_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.38  cnf(c_0_35, negated_conjecture, (l3_lattices(k7_filter_1(esk1_0,esk2_0))|v17_lattices(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.38  fof(c_0_36, axiom, ![X1]:(((~(v2_struct_0(X1))&v10_lattices(X1))&l3_lattices(X1))=>![X2]:(((~(v2_struct_0(X2))&v10_lattices(X2))&l3_lattices(X2))=>epred2_2(X2,X1))), inference(apply_def,[status(thm)],[t46_filter_1, c_0_24])).
% 0.20/0.38  cnf(c_0_37, plain, (v15_lattices(X1)|v2_struct_0(X1)|~v17_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.38  cnf(c_0_38, plain, (v11_lattices(esk1_0)|v2_struct_0(k7_filter_1(esk1_0,esk2_0))|~epred1_2(esk2_0,esk1_0)|~v11_lattices(k7_filter_1(esk1_0,esk2_0))|~l3_lattices(k7_filter_1(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.20/0.38  fof(c_0_39, plain, ![X5, X6]:((v3_lattices(k7_filter_1(X5,X6))|(v2_struct_0(X5)|~l3_lattices(X5)|v2_struct_0(X6)|~l3_lattices(X6)))&(l3_lattices(k7_filter_1(X5,X6))|(v2_struct_0(X5)|~l3_lattices(X5)|v2_struct_0(X6)|~l3_lattices(X6)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_filter_1])])])])).
% 0.20/0.38  cnf(c_0_40, plain, (v16_lattices(X1)|v2_struct_0(k7_filter_1(X1,X2))|~v10_lattices(k7_filter_1(X1,X2))|~v15_lattices(k7_filter_1(X1,X2))|~v16_lattices(k7_filter_1(X1,X2))|~l3_lattices(k7_filter_1(X1,X2))|~epred2_2(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.38  cnf(c_0_41, negated_conjecture, (v10_lattices(k7_filter_1(esk1_0,esk2_0))|v16_lattices(esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_26]), c_0_28])]), c_0_29])).
% 0.20/0.38  cnf(c_0_42, negated_conjecture, (v16_lattices(esk1_0)|l3_lattices(k7_filter_1(esk1_0,esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_28])]), c_0_29])).
% 0.20/0.38  fof(c_0_43, plain, ![X9, X10]:(v2_struct_0(X9)|~v10_lattices(X9)|~l3_lattices(X9)|(v2_struct_0(X10)|~v10_lattices(X10)|~l3_lattices(X10)|epred2_2(X10,X9))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_36])])])])).
% 0.20/0.38  cnf(c_0_44, plain, (v15_lattices(X1)|v2_struct_0(k7_filter_1(X1,X2))|~v10_lattices(k7_filter_1(X1,X2))|~v15_lattices(k7_filter_1(X1,X2))|~v16_lattices(k7_filter_1(X1,X2))|~l3_lattices(k7_filter_1(X1,X2))|~epred2_2(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.38  cnf(c_0_45, negated_conjecture, (v10_lattices(k7_filter_1(esk1_0,esk2_0))|v15_lattices(esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_26]), c_0_28])]), c_0_29])).
% 0.20/0.38  cnf(c_0_46, negated_conjecture, (v15_lattices(esk1_0)|l3_lattices(k7_filter_1(esk1_0,esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_35]), c_0_28])]), c_0_29])).
% 0.20/0.38  cnf(c_0_47, plain, (v11_lattices(X1)|v2_struct_0(k7_filter_1(X2,X1))|~v10_lattices(k7_filter_1(X2,X1))|~v11_lattices(k7_filter_1(X2,X1))|~l3_lattices(k7_filter_1(X2,X1))|~epred1_2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.38  cnf(c_0_48, negated_conjecture, (l3_lattices(k7_filter_1(esk1_0,esk2_0))|v17_lattices(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.38  cnf(c_0_49, plain, (v11_lattices(esk1_0)|v2_struct_0(k7_filter_1(esk1_0,esk2_0))|~v11_lattices(k7_filter_1(esk1_0,esk2_0))|~l3_lattices(k7_filter_1(esk1_0,esk2_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_12]), c_0_21]), c_0_27]), c_0_22]), c_0_28])]), c_0_29]), c_0_23])).
% 0.20/0.38  cnf(c_0_50, plain, (l3_lattices(k7_filter_1(X1,X2))|v2_struct_0(X1)|v2_struct_0(X2)|~l3_lattices(X1)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.38  cnf(c_0_51, plain, (v16_lattices(esk1_0)|v2_struct_0(k7_filter_1(esk1_0,esk2_0))|~epred2_2(esk2_0,esk1_0)|~v16_lattices(k7_filter_1(esk1_0,esk2_0))|~v15_lattices(k7_filter_1(esk1_0,esk2_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42])).
% 0.20/0.38  cnf(c_0_52, plain, (v2_struct_0(X1)|v2_struct_0(X2)|epred2_2(X2,X1)|~v10_lattices(X1)|~l3_lattices(X1)|~v10_lattices(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.38  cnf(c_0_53, negated_conjecture, (v17_lattices(k7_filter_1(esk1_0,esk2_0))|v17_lattices(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.38  cnf(c_0_54, negated_conjecture, (v17_lattices(esk1_0)|~v2_struct_0(k7_filter_1(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.38  cnf(c_0_55, plain, (v15_lattices(esk1_0)|v2_struct_0(k7_filter_1(esk1_0,esk2_0))|~epred2_2(esk2_0,esk1_0)|~v16_lattices(k7_filter_1(esk1_0,esk2_0))|~v15_lattices(k7_filter_1(esk1_0,esk2_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46])).
% 0.20/0.38  cnf(c_0_56, plain, (v11_lattices(esk2_0)|v2_struct_0(k7_filter_1(esk1_0,esk2_0))|~epred1_2(esk2_0,esk1_0)|~v11_lattices(k7_filter_1(esk1_0,esk2_0))|~l3_lattices(k7_filter_1(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_47, c_0_32])).
% 0.20/0.38  cnf(c_0_57, plain, (v16_lattices(X1)|v2_struct_0(k7_filter_1(X2,X1))|~v10_lattices(k7_filter_1(X2,X1))|~v15_lattices(k7_filter_1(X2,X1))|~v16_lattices(k7_filter_1(X2,X1))|~l3_lattices(k7_filter_1(X2,X1))|~epred2_2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.38  cnf(c_0_58, negated_conjecture, (v10_lattices(k7_filter_1(esk1_0,esk2_0))|v16_lattices(esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_20]), c_0_22])]), c_0_23])).
% 0.20/0.38  cnf(c_0_59, negated_conjecture, (v16_lattices(esk2_0)|l3_lattices(k7_filter_1(esk1_0,esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_48]), c_0_22])]), c_0_23])).
% 0.20/0.38  cnf(c_0_60, plain, (v15_lattices(X1)|v2_struct_0(k7_filter_1(X2,X1))|~v10_lattices(k7_filter_1(X2,X1))|~v15_lattices(k7_filter_1(X2,X1))|~v16_lattices(k7_filter_1(X2,X1))|~l3_lattices(k7_filter_1(X2,X1))|~epred2_2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.38  cnf(c_0_61, negated_conjecture, (v10_lattices(k7_filter_1(esk1_0,esk2_0))|v15_lattices(esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_20]), c_0_22])]), c_0_23])).
% 0.20/0.38  cnf(c_0_62, negated_conjecture, (v15_lattices(esk2_0)|l3_lattices(k7_filter_1(esk1_0,esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_48]), c_0_22])]), c_0_23])).
% 0.20/0.38  cnf(c_0_63, plain, (v11_lattices(esk1_0)|v2_struct_0(k7_filter_1(esk1_0,esk2_0))|~v11_lattices(k7_filter_1(esk1_0,esk2_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_22]), c_0_28])]), c_0_29]), c_0_23])).
% 0.20/0.38  cnf(c_0_64, plain, (v16_lattices(esk1_0)|v2_struct_0(k7_filter_1(esk1_0,esk2_0))|~v16_lattices(k7_filter_1(esk1_0,esk2_0))|~v15_lattices(k7_filter_1(esk1_0,esk2_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_21]), c_0_27]), c_0_22]), c_0_28])]), c_0_29]), c_0_23])).
% 0.20/0.38  cnf(c_0_65, negated_conjecture, (v15_lattices(k7_filter_1(esk1_0,esk2_0))|v17_lattices(esk1_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_53]), c_0_35]), c_0_54])).
% 0.20/0.38  cnf(c_0_66, negated_conjecture, (v16_lattices(k7_filter_1(esk1_0,esk2_0))|v17_lattices(esk1_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_53]), c_0_35]), c_0_54])).
% 0.20/0.38  cnf(c_0_67, plain, (v15_lattices(esk1_0)|v2_struct_0(k7_filter_1(esk1_0,esk2_0))|~v16_lattices(k7_filter_1(esk1_0,esk2_0))|~v15_lattices(k7_filter_1(esk1_0,esk2_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_52]), c_0_21]), c_0_27]), c_0_22]), c_0_28])]), c_0_29]), c_0_23])).
% 0.20/0.38  cnf(c_0_68, plain, (v11_lattices(esk2_0)|v2_struct_0(k7_filter_1(esk1_0,esk2_0))|~v11_lattices(k7_filter_1(esk1_0,esk2_0))|~l3_lattices(k7_filter_1(esk1_0,esk2_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_12]), c_0_21]), c_0_27]), c_0_22]), c_0_28])]), c_0_29]), c_0_23])).
% 0.20/0.38  cnf(c_0_69, plain, (v16_lattices(esk2_0)|v2_struct_0(k7_filter_1(esk1_0,esk2_0))|~epred2_2(esk2_0,esk1_0)|~v16_lattices(k7_filter_1(esk1_0,esk2_0))|~v15_lattices(k7_filter_1(esk1_0,esk2_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_59])).
% 0.20/0.38  cnf(c_0_70, negated_conjecture, (v17_lattices(k7_filter_1(esk1_0,esk2_0))|v17_lattices(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.38  cnf(c_0_71, negated_conjecture, (v17_lattices(esk2_0)|~v2_struct_0(k7_filter_1(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.38  cnf(c_0_72, plain, (v15_lattices(esk2_0)|v2_struct_0(k7_filter_1(esk1_0,esk2_0))|~epred2_2(esk2_0,esk1_0)|~v16_lattices(k7_filter_1(esk1_0,esk2_0))|~v15_lattices(k7_filter_1(esk1_0,esk2_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_62])).
% 0.20/0.38  cnf(c_0_73, negated_conjecture, (v2_struct_0(esk1_0)|v2_struct_0(esk2_0)|v2_struct_0(k7_filter_1(esk1_0,esk2_0))|~v10_lattices(esk1_0)|~v17_lattices(esk1_0)|~l3_lattices(esk1_0)|~v10_lattices(esk2_0)|~v17_lattices(esk2_0)|~l3_lattices(esk2_0)|~v10_lattices(k7_filter_1(esk1_0,esk2_0))|~v17_lattices(k7_filter_1(esk1_0,esk2_0))|~l3_lattices(k7_filter_1(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.38  fof(c_0_74, plain, ![X4]:((~v2_struct_0(X4)|(v2_struct_0(X4)|~v11_lattices(X4)|~v15_lattices(X4)|~v16_lattices(X4))|~l3_lattices(X4))&(v17_lattices(X4)|(v2_struct_0(X4)|~v11_lattices(X4)|~v15_lattices(X4)|~v16_lattices(X4))|~l3_lattices(X4))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc6_lattices])])])])).
% 0.20/0.38  cnf(c_0_75, plain, (v11_lattices(esk1_0)|v2_struct_0(k7_filter_1(esk1_0,esk2_0))|~v17_lattices(k7_filter_1(esk1_0,esk2_0))|~l3_lattices(k7_filter_1(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_63, c_0_15])).
% 0.20/0.38  cnf(c_0_76, negated_conjecture, (v16_lattices(esk1_0)|v17_lattices(esk1_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_66]), c_0_54])).
% 0.20/0.38  cnf(c_0_77, negated_conjecture, (v15_lattices(esk1_0)|v17_lattices(esk1_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_66]), c_0_65]), c_0_54])).
% 0.20/0.38  cnf(c_0_78, plain, (v11_lattices(esk2_0)|v2_struct_0(k7_filter_1(esk1_0,esk2_0))|~v11_lattices(k7_filter_1(esk1_0,esk2_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_50]), c_0_22]), c_0_28])]), c_0_29]), c_0_23])).
% 0.20/0.38  cnf(c_0_79, plain, (v16_lattices(esk2_0)|v2_struct_0(k7_filter_1(esk1_0,esk2_0))|~v16_lattices(k7_filter_1(esk1_0,esk2_0))|~v15_lattices(k7_filter_1(esk1_0,esk2_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_52]), c_0_21]), c_0_27]), c_0_22]), c_0_28])]), c_0_29]), c_0_23])).
% 0.20/0.38  cnf(c_0_80, negated_conjecture, (v15_lattices(k7_filter_1(esk1_0,esk2_0))|v17_lattices(esk2_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_70]), c_0_48]), c_0_71])).
% 0.20/0.38  cnf(c_0_81, negated_conjecture, (v16_lattices(k7_filter_1(esk1_0,esk2_0))|v17_lattices(esk2_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_70]), c_0_48]), c_0_71])).
% 0.20/0.38  cnf(c_0_82, plain, (v15_lattices(esk2_0)|v2_struct_0(k7_filter_1(esk1_0,esk2_0))|~v16_lattices(k7_filter_1(esk1_0,esk2_0))|~v15_lattices(k7_filter_1(esk1_0,esk2_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_52]), c_0_21]), c_0_27]), c_0_22]), c_0_28])]), c_0_29]), c_0_23])).
% 0.20/0.38  cnf(c_0_83, negated_conjecture, (v2_struct_0(k7_filter_1(esk1_0,esk2_0))|~v10_lattices(k7_filter_1(esk1_0,esk2_0))|~v17_lattices(k7_filter_1(esk1_0,esk2_0))|~v17_lattices(esk1_0)|~v17_lattices(esk2_0)|~l3_lattices(k7_filter_1(esk1_0,esk2_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73, c_0_28]), c_0_22]), c_0_27]), c_0_21])]), c_0_29]), c_0_23])).
% 0.20/0.38  cnf(c_0_84, plain, (v17_lattices(X1)|v2_struct_0(X1)|~v11_lattices(X1)|~v15_lattices(X1)|~v16_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.20/0.38  cnf(c_0_85, negated_conjecture, (v11_lattices(esk1_0)|v17_lattices(esk1_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_53]), c_0_35]), c_0_54])).
% 0.20/0.38  cnf(c_0_86, negated_conjecture, (v16_lattices(esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_76]), c_0_28])]), c_0_29])).
% 0.20/0.38  cnf(c_0_87, negated_conjecture, (v15_lattices(esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_77]), c_0_28])]), c_0_29])).
% 0.20/0.38  cnf(c_0_88, plain, (v11_lattices(esk2_0)|v2_struct_0(k7_filter_1(esk1_0,esk2_0))|~v17_lattices(k7_filter_1(esk1_0,esk2_0))|~l3_lattices(k7_filter_1(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_78, c_0_15])).
% 0.20/0.38  cnf(c_0_89, negated_conjecture, (v16_lattices(esk2_0)|v17_lattices(esk2_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_81]), c_0_71])).
% 0.20/0.38  cnf(c_0_90, negated_conjecture, (v15_lattices(esk2_0)|v17_lattices(esk2_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_81]), c_0_80]), c_0_71])).
% 0.20/0.38  cnf(c_0_91, plain, (v11_lattices(k7_filter_1(X1,X2))|v2_struct_0(X1)|v2_struct_0(X2)|~v10_lattices(X1)|~v11_lattices(X1)|~l3_lattices(X1)|~v10_lattices(X2)|~v11_lattices(X2)|~l3_lattices(X2)|~epred1_2(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.38  cnf(c_0_92, plain, (v2_struct_0(X1)|v2_struct_0(X2)|~v2_struct_0(k7_filter_1(X1,X2))|~v10_lattices(X1)|~v11_lattices(X1)|~l3_lattices(X1)|~v10_lattices(X2)|~v11_lattices(X2)|~l3_lattices(X2)|~epred1_2(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.38  cnf(c_0_93, negated_conjecture, (v2_struct_0(k7_filter_1(esk1_0,esk2_0))|~v17_lattices(k7_filter_1(esk1_0,esk2_0))|~v17_lattices(esk1_0)|~v17_lattices(esk2_0)|~l3_lattices(k7_filter_1(esk1_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_83, c_0_32])])).
% 0.20/0.38  cnf(c_0_94, negated_conjecture, (v17_lattices(esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_86]), c_0_87]), c_0_28])]), c_0_29])).
% 0.20/0.38  cnf(c_0_95, negated_conjecture, (v11_lattices(esk2_0)|v17_lattices(esk2_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_70]), c_0_48]), c_0_71])).
% 0.20/0.38  cnf(c_0_96, negated_conjecture, (v16_lattices(esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_89]), c_0_22])]), c_0_23])).
% 0.20/0.38  cnf(c_0_97, negated_conjecture, (v15_lattices(esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_90]), c_0_22])]), c_0_23])).
% 0.20/0.38  cnf(c_0_98, plain, (v11_lattices(k7_filter_1(X1,X2))|v2_struct_0(X1)|v2_struct_0(X2)|~v10_lattices(X2)|~v10_lattices(X1)|~v11_lattices(X2)|~v11_lattices(X1)|~l3_lattices(X2)|~l3_lattices(X1)), inference(csr,[status(thm)],[c_0_91, c_0_12])).
% 0.20/0.38  cnf(c_0_99, plain, (v2_struct_0(X1)|v2_struct_0(X2)|~v10_lattices(X2)|~v10_lattices(X1)|~v11_lattices(X2)|~v11_lattices(X1)|~v2_struct_0(k7_filter_1(X1,X2))|~l3_lattices(X2)|~l3_lattices(X1)), inference(csr,[status(thm)],[c_0_92, c_0_12])).
% 0.20/0.38  cnf(c_0_100, plain, (v16_lattices(k7_filter_1(X1,X2))|v2_struct_0(X1)|v2_struct_0(X2)|~v10_lattices(X1)|~v15_lattices(X1)|~v16_lattices(X1)|~l3_lattices(X1)|~v10_lattices(X2)|~v15_lattices(X2)|~v16_lattices(X2)|~l3_lattices(X2)|~epred2_2(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.38  cnf(c_0_101, plain, (v15_lattices(k7_filter_1(X1,X2))|v2_struct_0(X1)|v2_struct_0(X2)|~v10_lattices(X1)|~v15_lattices(X1)|~v16_lattices(X1)|~l3_lattices(X1)|~v10_lattices(X2)|~v15_lattices(X2)|~v16_lattices(X2)|~l3_lattices(X2)|~epred2_2(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.38  cnf(c_0_102, negated_conjecture, (v2_struct_0(k7_filter_1(esk1_0,esk2_0))|~v17_lattices(k7_filter_1(esk1_0,esk2_0))|~v17_lattices(esk2_0)|~l3_lattices(k7_filter_1(esk1_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_93, c_0_94])])).
% 0.20/0.38  cnf(c_0_103, negated_conjecture, (v17_lattices(esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_95]), c_0_96]), c_0_97]), c_0_22])]), c_0_23])).
% 0.20/0.38  cnf(c_0_104, plain, (v17_lattices(k7_filter_1(X1,X2))|v2_struct_0(X2)|v2_struct_0(X1)|~v10_lattices(X2)|~v10_lattices(X1)|~v16_lattices(k7_filter_1(X1,X2))|~v15_lattices(k7_filter_1(X1,X2))|~v11_lattices(X2)|~v11_lattices(X1)|~l3_lattices(X2)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_98]), c_0_50]), c_0_99])).
% 0.20/0.38  cnf(c_0_105, plain, (v16_lattices(k7_filter_1(X1,X2))|v2_struct_0(X1)|v2_struct_0(X2)|~v10_lattices(X2)|~v10_lattices(X1)|~v16_lattices(X2)|~v16_lattices(X1)|~v15_lattices(X2)|~v15_lattices(X1)|~l3_lattices(X2)|~l3_lattices(X1)), inference(csr,[status(thm)],[c_0_100, c_0_52])).
% 0.20/0.38  cnf(c_0_106, plain, (v15_lattices(k7_filter_1(X1,X2))|v2_struct_0(X1)|v2_struct_0(X2)|~v10_lattices(X2)|~v10_lattices(X1)|~v16_lattices(X2)|~v16_lattices(X1)|~v15_lattices(X2)|~v15_lattices(X1)|~l3_lattices(X2)|~l3_lattices(X1)), inference(csr,[status(thm)],[c_0_101, c_0_52])).
% 0.20/0.38  cnf(c_0_107, negated_conjecture, (v2_struct_0(k7_filter_1(esk1_0,esk2_0))|~v17_lattices(k7_filter_1(esk1_0,esk2_0))|~l3_lattices(k7_filter_1(esk1_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_102, c_0_103])])).
% 0.20/0.38  cnf(c_0_108, plain, (v17_lattices(k7_filter_1(X1,X2))|v2_struct_0(X1)|v2_struct_0(X2)|~v10_lattices(X2)|~v10_lattices(X1)|~v16_lattices(X2)|~v16_lattices(X1)|~v15_lattices(X2)|~v15_lattices(X1)|~v11_lattices(X2)|~v11_lattices(X1)|~l3_lattices(X2)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_105]), c_0_106])).
% 0.20/0.38  cnf(c_0_109, negated_conjecture, (v2_struct_0(k7_filter_1(esk1_0,esk2_0))|~v11_lattices(esk2_0)|~v11_lattices(esk1_0)|~l3_lattices(k7_filter_1(esk1_0,esk2_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_108]), c_0_21]), c_0_27]), c_0_96]), c_0_86]), c_0_97]), c_0_87]), c_0_22]), c_0_28])]), c_0_29]), c_0_23])).
% 0.20/0.38  cnf(c_0_110, negated_conjecture, (v2_struct_0(k7_filter_1(esk1_0,esk2_0))|~v11_lattices(esk1_0)|~l3_lattices(k7_filter_1(esk1_0,esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_15]), c_0_103]), c_0_22])]), c_0_23])).
% 0.20/0.38  cnf(c_0_111, plain, (v2_struct_0(X1)|v2_struct_0(X2)|~v2_struct_0(k7_filter_1(X1,X2))|~v10_lattices(X1)|~v15_lattices(X1)|~v16_lattices(X1)|~l3_lattices(X1)|~v10_lattices(X2)|~v15_lattices(X2)|~v16_lattices(X2)|~l3_lattices(X2)|~epred2_2(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.38  cnf(c_0_112, negated_conjecture, (v2_struct_0(k7_filter_1(esk1_0,esk2_0))|~l3_lattices(k7_filter_1(esk1_0,esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_15]), c_0_94]), c_0_28])]), c_0_29])).
% 0.20/0.38  cnf(c_0_113, plain, (v2_struct_0(X1)|v2_struct_0(X2)|~v10_lattices(X2)|~v10_lattices(X1)|~v16_lattices(X2)|~v16_lattices(X1)|~v15_lattices(X2)|~v15_lattices(X1)|~v2_struct_0(k7_filter_1(X1,X2))|~l3_lattices(X2)|~l3_lattices(X1)), inference(csr,[status(thm)],[c_0_111, c_0_52])).
% 0.20/0.38  cnf(c_0_114, negated_conjecture, (v2_struct_0(k7_filter_1(esk1_0,esk2_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112, c_0_50]), c_0_22]), c_0_28])]), c_0_29]), c_0_23])).
% 0.20/0.38  cnf(c_0_115, plain, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_114]), c_0_21]), c_0_27]), c_0_96]), c_0_86]), c_0_97]), c_0_87]), c_0_22]), c_0_28])]), c_0_29]), c_0_23]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 116
% 0.20/0.38  # Proof object clause steps            : 95
% 0.20/0.38  # Proof object formula steps           : 21
% 0.20/0.38  # Proof object conjectures             : 52
% 0.20/0.38  # Proof object clause conjectures      : 49
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 34
% 0.20/0.38  # Proof object initial formulas used   : 6
% 0.20/0.38  # Proof object generating inferences   : 51
% 0.20/0.38  # Proof object simplifying inferences  : 187
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 6
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 76
% 0.20/0.38  # Removed in clause preprocessing      : 2
% 0.20/0.38  # Initial clauses in saturation        : 74
% 0.20/0.38  # Processed clauses                    : 235
% 0.20/0.38  # ...of these trivial                  : 16
% 0.20/0.38  # ...subsumed                          : 66
% 0.20/0.38  # ...remaining for further processing  : 153
% 0.20/0.38  # Other redundant clauses eliminated   : 0
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 33
% 0.20/0.38  # Backward-rewritten                   : 41
% 0.20/0.38  # Generated clauses                    : 497
% 0.20/0.38  # ...of the previous two non-trivial   : 287
% 0.20/0.38  # Contextual simplify-reflections      : 82
% 0.20/0.38  # Paramodulations                      : 497
% 0.20/0.38  # Factorizations                       : 0
% 0.20/0.38  # Equation resolutions                 : 0
% 0.20/0.38  # Propositional unsat checks           : 0
% 0.20/0.38  #    Propositional check models        : 0
% 0.20/0.38  #    Propositional check unsatisfiable : 0
% 0.20/0.38  #    Propositional clauses             : 0
% 0.20/0.38  #    Propositional clauses after purity: 0
% 0.20/0.38  #    Propositional unsat core size     : 0
% 0.20/0.38  #    Propositional preprocessing time  : 0.000
% 0.20/0.38  #    Propositional encoding time       : 0.000
% 0.20/0.38  #    Propositional solver time         : 0.000
% 0.20/0.38  #    Success case prop preproc time    : 0.000
% 0.20/0.38  #    Success case prop encoding time   : 0.000
% 0.20/0.38  #    Success case prop solver time     : 0.000
% 0.20/0.38  # Current number of processed clauses  : 79
% 0.20/0.38  #    Positive orientable unit clauses  : 15
% 0.20/0.38  #    Positive unorientable unit clauses: 0
% 0.20/0.38  #    Negative unit clauses             : 2
% 0.20/0.38  #    Non-unit-clauses                  : 62
% 0.20/0.38  # Current number of unprocessed clauses: 41
% 0.20/0.38  # ...number of literals in the above   : 678
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 74
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 2727
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 459
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 129
% 0.20/0.38  # Unit Clause-clause subsumption calls : 87
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 9
% 0.20/0.38  # BW rewrite match successes           : 9
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 19241
% 0.20/0.39  
% 0.20/0.39  # -------------------------------------------------
% 0.20/0.39  # User time                : 0.048 s
% 0.20/0.39  # System time              : 0.005 s
% 0.20/0.39  # Total time               : 0.052 s
% 0.20/0.39  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
