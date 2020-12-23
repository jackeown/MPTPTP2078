%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1452+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:16 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :  108 (1861 expanded)
%              Number of clauses        :   83 ( 579 expanded)
%              Number of leaves         :   10 ( 472 expanded)
%              Depth                    :   17
%              Number of atoms          :  908 (45008 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   40 (   7 average)
%              Maximal clause size      :  130 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_filter_1)).

fof(cc5_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( ( ~ v2_struct_0(X1)
          & v17_lattices(X1) )
       => ( ~ v2_struct_0(X1)
          & v11_lattices(X1)
          & v15_lattices(X1)
          & v16_lattices(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_lattices)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_filter_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_filter_1)).

fof(fc3_filter_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & l3_lattices(X1)
        & ~ v2_struct_0(X2)
        & v10_lattices(X2)
        & l3_lattices(X2) )
     => ( v3_lattices(k7_filter_1(X1,X2))
        & v10_lattices(k7_filter_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_filter_1)).

fof(dt_k7_filter_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1)
        & ~ v2_struct_0(X2)
        & l3_lattices(X2) )
     => ( v3_lattices(k7_filter_1(X1,X2))
        & l3_lattices(k7_filter_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_filter_1)).

fof(fc2_filter_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1)
        & ~ v2_struct_0(X2)
        & l3_lattices(X2) )
     => ( ~ v2_struct_0(k7_filter_1(X1,X2))
        & v3_lattices(k7_filter_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_filter_1)).

fof(cc6_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( ( ~ v2_struct_0(X1)
          & v11_lattices(X1)
          & v15_lattices(X1)
          & v16_lattices(X1) )
       => ( ~ v2_struct_0(X1)
          & v17_lattices(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc6_lattices)).

fof(c_0_8,plain,(
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

fof(c_0_9,negated_conjecture,(
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

fof(c_0_10,plain,(
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

fof(c_0_11,plain,(
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
    inference(split_equiv,[status(thm)],[c_0_8])).

fof(c_0_12,plain,(
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

fof(c_0_13,negated_conjecture,
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
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])])).

fof(c_0_14,plain,(
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
    inference(split_equiv,[status(thm)],[c_0_10])).

fof(c_0_15,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v10_lattices(X2)
            & l3_lattices(X2) )
         => epred1_2(X2,X1) ) ) ),
    inference(apply_def,[status(thm)],[t39_filter_1,c_0_10])).

fof(c_0_16,plain,(
    ! [X19,X20] :
      ( ( ~ v2_struct_0(k7_filter_1(X19,X20))
        | v2_struct_0(X19)
        | ~ v10_lattices(X19)
        | ~ v15_lattices(X19)
        | ~ v16_lattices(X19)
        | ~ l3_lattices(X19)
        | v2_struct_0(X20)
        | ~ v10_lattices(X20)
        | ~ v15_lattices(X20)
        | ~ v16_lattices(X20)
        | ~ l3_lattices(X20)
        | ~ epred2_2(X20,X19) )
      & ( v10_lattices(k7_filter_1(X19,X20))
        | v2_struct_0(X19)
        | ~ v10_lattices(X19)
        | ~ v15_lattices(X19)
        | ~ v16_lattices(X19)
        | ~ l3_lattices(X19)
        | v2_struct_0(X20)
        | ~ v10_lattices(X20)
        | ~ v15_lattices(X20)
        | ~ v16_lattices(X20)
        | ~ l3_lattices(X20)
        | ~ epred2_2(X20,X19) )
      & ( v15_lattices(k7_filter_1(X19,X20))
        | v2_struct_0(X19)
        | ~ v10_lattices(X19)
        | ~ v15_lattices(X19)
        | ~ v16_lattices(X19)
        | ~ l3_lattices(X19)
        | v2_struct_0(X20)
        | ~ v10_lattices(X20)
        | ~ v15_lattices(X20)
        | ~ v16_lattices(X20)
        | ~ l3_lattices(X20)
        | ~ epred2_2(X20,X19) )
      & ( v16_lattices(k7_filter_1(X19,X20))
        | v2_struct_0(X19)
        | ~ v10_lattices(X19)
        | ~ v15_lattices(X19)
        | ~ v16_lattices(X19)
        | ~ l3_lattices(X19)
        | v2_struct_0(X20)
        | ~ v10_lattices(X20)
        | ~ v15_lattices(X20)
        | ~ v16_lattices(X20)
        | ~ l3_lattices(X20)
        | ~ epred2_2(X20,X19) )
      & ( l3_lattices(k7_filter_1(X19,X20))
        | v2_struct_0(X19)
        | ~ v10_lattices(X19)
        | ~ v15_lattices(X19)
        | ~ v16_lattices(X19)
        | ~ l3_lattices(X19)
        | v2_struct_0(X20)
        | ~ v10_lattices(X20)
        | ~ v15_lattices(X20)
        | ~ v16_lattices(X20)
        | ~ l3_lattices(X20)
        | ~ epred2_2(X20,X19) )
      & ( ~ v2_struct_0(X19)
        | v2_struct_0(k7_filter_1(X19,X20))
        | ~ v10_lattices(k7_filter_1(X19,X20))
        | ~ v15_lattices(k7_filter_1(X19,X20))
        | ~ v16_lattices(k7_filter_1(X19,X20))
        | ~ l3_lattices(k7_filter_1(X19,X20))
        | ~ epred2_2(X20,X19) )
      & ( v10_lattices(X19)
        | v2_struct_0(k7_filter_1(X19,X20))
        | ~ v10_lattices(k7_filter_1(X19,X20))
        | ~ v15_lattices(k7_filter_1(X19,X20))
        | ~ v16_lattices(k7_filter_1(X19,X20))
        | ~ l3_lattices(k7_filter_1(X19,X20))
        | ~ epred2_2(X20,X19) )
      & ( v15_lattices(X19)
        | v2_struct_0(k7_filter_1(X19,X20))
        | ~ v10_lattices(k7_filter_1(X19,X20))
        | ~ v15_lattices(k7_filter_1(X19,X20))
        | ~ v16_lattices(k7_filter_1(X19,X20))
        | ~ l3_lattices(k7_filter_1(X19,X20))
        | ~ epred2_2(X20,X19) )
      & ( v16_lattices(X19)
        | v2_struct_0(k7_filter_1(X19,X20))
        | ~ v10_lattices(k7_filter_1(X19,X20))
        | ~ v15_lattices(k7_filter_1(X19,X20))
        | ~ v16_lattices(k7_filter_1(X19,X20))
        | ~ l3_lattices(k7_filter_1(X19,X20))
        | ~ epred2_2(X20,X19) )
      & ( l3_lattices(X19)
        | v2_struct_0(k7_filter_1(X19,X20))
        | ~ v10_lattices(k7_filter_1(X19,X20))
        | ~ v15_lattices(k7_filter_1(X19,X20))
        | ~ v16_lattices(k7_filter_1(X19,X20))
        | ~ l3_lattices(k7_filter_1(X19,X20))
        | ~ epred2_2(X20,X19) )
      & ( ~ v2_struct_0(X20)
        | v2_struct_0(k7_filter_1(X19,X20))
        | ~ v10_lattices(k7_filter_1(X19,X20))
        | ~ v15_lattices(k7_filter_1(X19,X20))
        | ~ v16_lattices(k7_filter_1(X19,X20))
        | ~ l3_lattices(k7_filter_1(X19,X20))
        | ~ epred2_2(X20,X19) )
      & ( v10_lattices(X20)
        | v2_struct_0(k7_filter_1(X19,X20))
        | ~ v10_lattices(k7_filter_1(X19,X20))
        | ~ v15_lattices(k7_filter_1(X19,X20))
        | ~ v16_lattices(k7_filter_1(X19,X20))
        | ~ l3_lattices(k7_filter_1(X19,X20))
        | ~ epred2_2(X20,X19) )
      & ( v15_lattices(X20)
        | v2_struct_0(k7_filter_1(X19,X20))
        | ~ v10_lattices(k7_filter_1(X19,X20))
        | ~ v15_lattices(k7_filter_1(X19,X20))
        | ~ v16_lattices(k7_filter_1(X19,X20))
        | ~ l3_lattices(k7_filter_1(X19,X20))
        | ~ epred2_2(X20,X19) )
      & ( v16_lattices(X20)
        | v2_struct_0(k7_filter_1(X19,X20))
        | ~ v10_lattices(k7_filter_1(X19,X20))
        | ~ v15_lattices(k7_filter_1(X19,X20))
        | ~ v16_lattices(k7_filter_1(X19,X20))
        | ~ l3_lattices(k7_filter_1(X19,X20))
        | ~ epred2_2(X20,X19) )
      & ( l3_lattices(X20)
        | v2_struct_0(k7_filter_1(X19,X20))
        | ~ v10_lattices(k7_filter_1(X19,X20))
        | ~ v15_lattices(k7_filter_1(X19,X20))
        | ~ v16_lattices(k7_filter_1(X19,X20))
        | ~ l3_lattices(k7_filter_1(X19,X20))
        | ~ epred2_2(X20,X19) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])).

cnf(c_0_17,plain,
    ( v16_lattices(X1)
    | v2_struct_0(X1)
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( v10_lattices(k7_filter_1(esk1_0,esk2_0))
    | v17_lattices(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( l3_lattices(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,negated_conjecture,
    ( l3_lattices(k7_filter_1(esk1_0,esk2_0))
    | v17_lattices(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_22,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v10_lattices(X2)
            & l3_lattices(X2) )
         => epred2_2(X2,X1) ) ) ),
    inference(apply_def,[status(thm)],[t46_filter_1,c_0_8])).

cnf(c_0_23,plain,
    ( v15_lattices(X1)
    | v2_struct_0(X1)
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_24,plain,(
    ! [X17,X18] :
      ( ( ~ v2_struct_0(k7_filter_1(X17,X18))
        | v2_struct_0(X17)
        | ~ v10_lattices(X17)
        | ~ v11_lattices(X17)
        | ~ l3_lattices(X17)
        | v2_struct_0(X18)
        | ~ v10_lattices(X18)
        | ~ v11_lattices(X18)
        | ~ l3_lattices(X18)
        | ~ epred1_2(X18,X17) )
      & ( v10_lattices(k7_filter_1(X17,X18))
        | v2_struct_0(X17)
        | ~ v10_lattices(X17)
        | ~ v11_lattices(X17)
        | ~ l3_lattices(X17)
        | v2_struct_0(X18)
        | ~ v10_lattices(X18)
        | ~ v11_lattices(X18)
        | ~ l3_lattices(X18)
        | ~ epred1_2(X18,X17) )
      & ( v11_lattices(k7_filter_1(X17,X18))
        | v2_struct_0(X17)
        | ~ v10_lattices(X17)
        | ~ v11_lattices(X17)
        | ~ l3_lattices(X17)
        | v2_struct_0(X18)
        | ~ v10_lattices(X18)
        | ~ v11_lattices(X18)
        | ~ l3_lattices(X18)
        | ~ epred1_2(X18,X17) )
      & ( l3_lattices(k7_filter_1(X17,X18))
        | v2_struct_0(X17)
        | ~ v10_lattices(X17)
        | ~ v11_lattices(X17)
        | ~ l3_lattices(X17)
        | v2_struct_0(X18)
        | ~ v10_lattices(X18)
        | ~ v11_lattices(X18)
        | ~ l3_lattices(X18)
        | ~ epred1_2(X18,X17) )
      & ( ~ v2_struct_0(X17)
        | v2_struct_0(k7_filter_1(X17,X18))
        | ~ v10_lattices(k7_filter_1(X17,X18))
        | ~ v11_lattices(k7_filter_1(X17,X18))
        | ~ l3_lattices(k7_filter_1(X17,X18))
        | ~ epred1_2(X18,X17) )
      & ( v10_lattices(X17)
        | v2_struct_0(k7_filter_1(X17,X18))
        | ~ v10_lattices(k7_filter_1(X17,X18))
        | ~ v11_lattices(k7_filter_1(X17,X18))
        | ~ l3_lattices(k7_filter_1(X17,X18))
        | ~ epred1_2(X18,X17) )
      & ( v11_lattices(X17)
        | v2_struct_0(k7_filter_1(X17,X18))
        | ~ v10_lattices(k7_filter_1(X17,X18))
        | ~ v11_lattices(k7_filter_1(X17,X18))
        | ~ l3_lattices(k7_filter_1(X17,X18))
        | ~ epred1_2(X18,X17) )
      & ( l3_lattices(X17)
        | v2_struct_0(k7_filter_1(X17,X18))
        | ~ v10_lattices(k7_filter_1(X17,X18))
        | ~ v11_lattices(k7_filter_1(X17,X18))
        | ~ l3_lattices(k7_filter_1(X17,X18))
        | ~ epred1_2(X18,X17) )
      & ( ~ v2_struct_0(X18)
        | v2_struct_0(k7_filter_1(X17,X18))
        | ~ v10_lattices(k7_filter_1(X17,X18))
        | ~ v11_lattices(k7_filter_1(X17,X18))
        | ~ l3_lattices(k7_filter_1(X17,X18))
        | ~ epred1_2(X18,X17) )
      & ( v10_lattices(X18)
        | v2_struct_0(k7_filter_1(X17,X18))
        | ~ v10_lattices(k7_filter_1(X17,X18))
        | ~ v11_lattices(k7_filter_1(X17,X18))
        | ~ l3_lattices(k7_filter_1(X17,X18))
        | ~ epred1_2(X18,X17) )
      & ( v11_lattices(X18)
        | v2_struct_0(k7_filter_1(X17,X18))
        | ~ v10_lattices(k7_filter_1(X17,X18))
        | ~ v11_lattices(k7_filter_1(X17,X18))
        | ~ l3_lattices(k7_filter_1(X17,X18))
        | ~ epred1_2(X18,X17) )
      & ( l3_lattices(X18)
        | v2_struct_0(k7_filter_1(X17,X18))
        | ~ v10_lattices(k7_filter_1(X17,X18))
        | ~ v11_lattices(k7_filter_1(X17,X18))
        | ~ l3_lattices(k7_filter_1(X17,X18))
        | ~ epred1_2(X18,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).

fof(c_0_25,plain,(
    ! [X9,X10] :
      ( ( v3_lattices(k7_filter_1(X9,X10))
        | v2_struct_0(X9)
        | ~ v10_lattices(X9)
        | ~ l3_lattices(X9)
        | v2_struct_0(X10)
        | ~ v10_lattices(X10)
        | ~ l3_lattices(X10) )
      & ( v10_lattices(k7_filter_1(X9,X10))
        | v2_struct_0(X9)
        | ~ v10_lattices(X9)
        | ~ l3_lattices(X9)
        | v2_struct_0(X10)
        | ~ v10_lattices(X10)
        | ~ l3_lattices(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc3_filter_1])])])])).

fof(c_0_26,plain,(
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

fof(c_0_27,plain,(
    ! [X11,X12] :
      ( v2_struct_0(X11)
      | ~ v10_lattices(X11)
      | ~ l3_lattices(X11)
      | v2_struct_0(X12)
      | ~ v10_lattices(X12)
      | ~ l3_lattices(X12)
      | epred1_2(X12,X11) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).

fof(c_0_28,plain,(
    ! [X7,X8] :
      ( ( ~ v2_struct_0(k7_filter_1(X7,X8))
        | v2_struct_0(X7)
        | ~ l3_lattices(X7)
        | v2_struct_0(X8)
        | ~ l3_lattices(X8) )
      & ( v3_lattices(k7_filter_1(X7,X8))
        | v2_struct_0(X7)
        | ~ l3_lattices(X7)
        | v2_struct_0(X8)
        | ~ l3_lattices(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_filter_1])])])])).

cnf(c_0_29,plain,
    ( v16_lattices(X1)
    | v2_struct_0(k7_filter_1(X2,X1))
    | ~ v10_lattices(k7_filter_1(X2,X1))
    | ~ v15_lattices(k7_filter_1(X2,X1))
    | ~ v16_lattices(k7_filter_1(X2,X1))
    | ~ l3_lattices(k7_filter_1(X2,X1))
    | ~ epred2_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_30,negated_conjecture,
    ( v10_lattices(k7_filter_1(esk1_0,esk2_0))
    | v16_lattices(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_31,negated_conjecture,
    ( v16_lattices(esk2_0)
    | l3_lattices(k7_filter_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_21]),c_0_19])]),c_0_20])).

fof(c_0_32,plain,(
    ! [X13,X14] :
      ( v2_struct_0(X13)
      | ~ v10_lattices(X13)
      | ~ l3_lattices(X13)
      | v2_struct_0(X14)
      | ~ v10_lattices(X14)
      | ~ l3_lattices(X14)
      | epred2_2(X14,X13) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_22])])])])).

cnf(c_0_33,plain,
    ( v15_lattices(X1)
    | v2_struct_0(k7_filter_1(X2,X1))
    | ~ v10_lattices(k7_filter_1(X2,X1))
    | ~ v15_lattices(k7_filter_1(X2,X1))
    | ~ v16_lattices(k7_filter_1(X2,X1))
    | ~ l3_lattices(k7_filter_1(X2,X1))
    | ~ epred2_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_34,negated_conjecture,
    ( v10_lattices(k7_filter_1(esk1_0,esk2_0))
    | v15_lattices(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_35,negated_conjecture,
    ( v15_lattices(esk2_0)
    | l3_lattices(k7_filter_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_21]),c_0_19])]),c_0_20])).

cnf(c_0_36,negated_conjecture,
    ( v10_lattices(k7_filter_1(esk1_0,esk2_0))
    | v17_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_37,negated_conjecture,
    ( l3_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_38,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_39,negated_conjecture,
    ( l3_lattices(k7_filter_1(esk1_0,esk2_0))
    | v17_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_40,plain,
    ( v11_lattices(X1)
    | v2_struct_0(k7_filter_1(X2,X1))
    | ~ v10_lattices(k7_filter_1(X2,X1))
    | ~ v11_lattices(k7_filter_1(X2,X1))
    | ~ l3_lattices(k7_filter_1(X2,X1))
    | ~ epred1_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_41,plain,
    ( v10_lattices(k7_filter_1(X1,X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_42,plain,
    ( l3_lattices(k7_filter_1(X1,X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l3_lattices(X1)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_43,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | epred1_2(X2,X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_44,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_struct_0(k7_filter_1(X1,X2))
    | ~ l3_lattices(X1)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_45,plain,
    ( v16_lattices(esk2_0)
    | v2_struct_0(k7_filter_1(esk1_0,esk2_0))
    | ~ epred2_2(esk2_0,esk1_0)
    | ~ v16_lattices(k7_filter_1(esk1_0,esk2_0))
    | ~ v15_lattices(k7_filter_1(esk1_0,esk2_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])).

cnf(c_0_46,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | epred2_2(X2,X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_47,negated_conjecture,
    ( v10_lattices(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_48,negated_conjecture,
    ( v10_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_49,negated_conjecture,
    ( v17_lattices(k7_filter_1(esk1_0,esk2_0))
    | v17_lattices(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_50,negated_conjecture,
    ( v17_lattices(esk2_0)
    | ~ v2_struct_0(k7_filter_1(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_51,plain,
    ( v15_lattices(esk2_0)
    | v2_struct_0(k7_filter_1(esk1_0,esk2_0))
    | ~ epred2_2(esk2_0,esk1_0)
    | ~ v16_lattices(k7_filter_1(esk1_0,esk2_0))
    | ~ v15_lattices(k7_filter_1(esk1_0,esk2_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])).

cnf(c_0_52,plain,
    ( v16_lattices(X1)
    | v2_struct_0(k7_filter_1(X1,X2))
    | ~ v10_lattices(k7_filter_1(X1,X2))
    | ~ v15_lattices(k7_filter_1(X1,X2))
    | ~ v16_lattices(k7_filter_1(X1,X2))
    | ~ l3_lattices(k7_filter_1(X1,X2))
    | ~ epred2_2(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_53,negated_conjecture,
    ( v10_lattices(k7_filter_1(esk1_0,esk2_0))
    | v16_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_36]),c_0_37])]),c_0_38])).

cnf(c_0_54,negated_conjecture,
    ( v16_lattices(esk1_0)
    | l3_lattices(k7_filter_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_39]),c_0_37])]),c_0_38])).

cnf(c_0_55,plain,
    ( v15_lattices(X1)
    | v2_struct_0(k7_filter_1(X1,X2))
    | ~ v10_lattices(k7_filter_1(X1,X2))
    | ~ v15_lattices(k7_filter_1(X1,X2))
    | ~ v16_lattices(k7_filter_1(X1,X2))
    | ~ l3_lattices(k7_filter_1(X1,X2))
    | ~ epred2_2(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_56,negated_conjecture,
    ( v10_lattices(k7_filter_1(esk1_0,esk2_0))
    | v15_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_36]),c_0_37])]),c_0_38])).

cnf(c_0_57,negated_conjecture,
    ( v15_lattices(esk1_0)
    | l3_lattices(k7_filter_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_39]),c_0_37])]),c_0_38])).

cnf(c_0_58,plain,
    ( v11_lattices(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v10_lattices(X1)
    | ~ v10_lattices(X2)
    | ~ v11_lattices(k7_filter_1(X2,X1))
    | ~ l3_lattices(X1)
    | ~ l3_lattices(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42]),c_0_43]),c_0_44])).

cnf(c_0_59,plain,
    ( v11_lattices(X1)
    | v2_struct_0(X1)
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_60,plain,
    ( v16_lattices(esk2_0)
    | v2_struct_0(k7_filter_1(esk1_0,esk2_0))
    | ~ v16_lattices(k7_filter_1(esk1_0,esk2_0))
    | ~ v15_lattices(k7_filter_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47]),c_0_48]),c_0_19]),c_0_37])]),c_0_38]),c_0_20])).

cnf(c_0_61,negated_conjecture,
    ( v15_lattices(k7_filter_1(esk1_0,esk2_0))
    | v17_lattices(esk2_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_49]),c_0_21]),c_0_50])).

cnf(c_0_62,negated_conjecture,
    ( v16_lattices(k7_filter_1(esk1_0,esk2_0))
    | v17_lattices(esk2_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_49]),c_0_21]),c_0_50])).

cnf(c_0_63,plain,
    ( v15_lattices(esk2_0)
    | v2_struct_0(k7_filter_1(esk1_0,esk2_0))
    | ~ v16_lattices(k7_filter_1(esk1_0,esk2_0))
    | ~ v15_lattices(k7_filter_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_46]),c_0_47]),c_0_48]),c_0_19]),c_0_37])]),c_0_38]),c_0_20])).

cnf(c_0_64,plain,
    ( v11_lattices(X1)
    | v2_struct_0(k7_filter_1(X1,X2))
    | ~ v10_lattices(k7_filter_1(X1,X2))
    | ~ v11_lattices(k7_filter_1(X1,X2))
    | ~ l3_lattices(k7_filter_1(X1,X2))
    | ~ epred1_2(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_65,plain,
    ( v16_lattices(esk1_0)
    | v2_struct_0(k7_filter_1(esk1_0,esk2_0))
    | ~ epred2_2(esk2_0,esk1_0)
    | ~ v16_lattices(k7_filter_1(esk1_0,esk2_0))
    | ~ v15_lattices(k7_filter_1(esk1_0,esk2_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54])).

cnf(c_0_66,negated_conjecture,
    ( v17_lattices(k7_filter_1(esk1_0,esk2_0))
    | v17_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_67,negated_conjecture,
    ( v17_lattices(esk1_0)
    | ~ v2_struct_0(k7_filter_1(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_68,plain,
    ( v15_lattices(esk1_0)
    | v2_struct_0(k7_filter_1(esk1_0,esk2_0))
    | ~ epred2_2(esk2_0,esk1_0)
    | ~ v16_lattices(k7_filter_1(esk1_0,esk2_0))
    | ~ v15_lattices(k7_filter_1(esk1_0,esk2_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57])).

fof(c_0_69,plain,(
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

cnf(c_0_70,plain,
    ( v11_lattices(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ v10_lattices(X2)
    | ~ v17_lattices(k7_filter_1(X2,X1))
    | ~ l3_lattices(X1)
    | ~ l3_lattices(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_42]),c_0_44])).

cnf(c_0_71,negated_conjecture,
    ( v16_lattices(esk2_0)
    | v17_lattices(esk2_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_62]),c_0_50])).

cnf(c_0_72,negated_conjecture,
    ( v15_lattices(esk2_0)
    | v17_lattices(esk2_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_62]),c_0_61]),c_0_50])).

cnf(c_0_73,plain,
    ( v11_lattices(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v10_lattices(X2)
    | ~ v10_lattices(X1)
    | ~ v11_lattices(k7_filter_1(X1,X2))
    | ~ l3_lattices(X2)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_41]),c_0_42]),c_0_43]),c_0_44])).

cnf(c_0_74,plain,
    ( v16_lattices(esk1_0)
    | v2_struct_0(k7_filter_1(esk1_0,esk2_0))
    | ~ v16_lattices(k7_filter_1(esk1_0,esk2_0))
    | ~ v15_lattices(k7_filter_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_46]),c_0_47]),c_0_48]),c_0_19]),c_0_37])]),c_0_38]),c_0_20])).

cnf(c_0_75,negated_conjecture,
    ( v15_lattices(k7_filter_1(esk1_0,esk2_0))
    | v17_lattices(esk1_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_66]),c_0_39]),c_0_67])).

cnf(c_0_76,negated_conjecture,
    ( v16_lattices(k7_filter_1(esk1_0,esk2_0))
    | v17_lattices(esk1_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_66]),c_0_39]),c_0_67])).

cnf(c_0_77,plain,
    ( v15_lattices(esk1_0)
    | v2_struct_0(k7_filter_1(esk1_0,esk2_0))
    | ~ v16_lattices(k7_filter_1(esk1_0,esk2_0))
    | ~ v15_lattices(k7_filter_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_46]),c_0_47]),c_0_48]),c_0_19]),c_0_37])]),c_0_38]),c_0_20])).

cnf(c_0_78,negated_conjecture,
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
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_79,plain,
    ( v17_lattices(X1)
    | v2_struct_0(X1)
    | ~ v11_lattices(X1)
    | ~ v15_lattices(X1)
    | ~ v16_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_80,negated_conjecture,
    ( v11_lattices(esk2_0)
    | v17_lattices(esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_49]),c_0_47]),c_0_48]),c_0_19]),c_0_37])]),c_0_38]),c_0_20])).

cnf(c_0_81,negated_conjecture,
    ( v16_lattices(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_71]),c_0_19])]),c_0_20])).

cnf(c_0_82,negated_conjecture,
    ( v15_lattices(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_72]),c_0_19])]),c_0_20])).

cnf(c_0_83,plain,
    ( v11_lattices(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v10_lattices(X2)
    | ~ v10_lattices(X1)
    | ~ v17_lattices(k7_filter_1(X1,X2))
    | ~ l3_lattices(X2)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_59]),c_0_42]),c_0_44])).

cnf(c_0_84,negated_conjecture,
    ( v16_lattices(esk1_0)
    | v17_lattices(esk1_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_76]),c_0_67])).

cnf(c_0_85,negated_conjecture,
    ( v15_lattices(esk1_0)
    | v17_lattices(esk1_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_76]),c_0_75]),c_0_67])).

cnf(c_0_86,negated_conjecture,
    ( v2_struct_0(k7_filter_1(esk1_0,esk2_0))
    | ~ v10_lattices(k7_filter_1(esk1_0,esk2_0))
    | ~ v17_lattices(k7_filter_1(esk1_0,esk2_0))
    | ~ v17_lattices(esk1_0)
    | ~ v17_lattices(esk2_0)
    | ~ l3_lattices(k7_filter_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_37]),c_0_19]),c_0_48]),c_0_47])]),c_0_38]),c_0_20])).

cnf(c_0_87,negated_conjecture,
    ( v17_lattices(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_81]),c_0_82]),c_0_19])]),c_0_20])).

cnf(c_0_88,negated_conjecture,
    ( v11_lattices(esk1_0)
    | v17_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_66]),c_0_47]),c_0_48]),c_0_19]),c_0_37])]),c_0_38]),c_0_20])).

cnf(c_0_89,negated_conjecture,
    ( v16_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_84]),c_0_37])]),c_0_38])).

cnf(c_0_90,negated_conjecture,
    ( v15_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_85]),c_0_37])]),c_0_38])).

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
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_92,negated_conjecture,
    ( v2_struct_0(k7_filter_1(esk1_0,esk2_0))
    | ~ v10_lattices(k7_filter_1(esk1_0,esk2_0))
    | ~ v17_lattices(k7_filter_1(esk1_0,esk2_0))
    | ~ v17_lattices(esk1_0)
    | ~ l3_lattices(k7_filter_1(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_86,c_0_87])])).

cnf(c_0_93,negated_conjecture,
    ( v17_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_88]),c_0_89]),c_0_90]),c_0_37])]),c_0_38])).

cnf(c_0_94,plain,
    ( v11_lattices(k7_filter_1(X1,X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v10_lattices(X2)
    | ~ v10_lattices(X1)
    | ~ v11_lattices(X2)
    | ~ v11_lattices(X1)
    | ~ l3_lattices(X2)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[c_0_91,c_0_43])).

cnf(c_0_95,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_96,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_97,negated_conjecture,
    ( v2_struct_0(k7_filter_1(esk1_0,esk2_0))
    | ~ v10_lattices(k7_filter_1(esk1_0,esk2_0))
    | ~ v17_lattices(k7_filter_1(esk1_0,esk2_0))
    | ~ l3_lattices(k7_filter_1(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_92,c_0_93])])).

cnf(c_0_98,plain,
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
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_94]),c_0_42]),c_0_44])).

cnf(c_0_99,plain,
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
    inference(csr,[status(thm)],[c_0_95,c_0_46])).

cnf(c_0_100,plain,
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
    inference(csr,[status(thm)],[c_0_96,c_0_46])).

cnf(c_0_101,negated_conjecture,
    ( v2_struct_0(k7_filter_1(esk1_0,esk2_0))
    | ~ v17_lattices(k7_filter_1(esk1_0,esk2_0))
    | ~ l3_lattices(k7_filter_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_41]),c_0_47]),c_0_48]),c_0_19]),c_0_37])]),c_0_38]),c_0_20])).

cnf(c_0_102,plain,
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
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_100])).

cnf(c_0_103,negated_conjecture,
    ( v2_struct_0(k7_filter_1(esk1_0,esk2_0))
    | ~ v11_lattices(esk2_0)
    | ~ v11_lattices(esk1_0)
    | ~ l3_lattices(k7_filter_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_102]),c_0_47]),c_0_48]),c_0_81]),c_0_89]),c_0_82]),c_0_90]),c_0_19]),c_0_37])]),c_0_38]),c_0_20])).

cnf(c_0_104,negated_conjecture,
    ( v2_struct_0(k7_filter_1(esk1_0,esk2_0))
    | ~ v11_lattices(esk1_0)
    | ~ l3_lattices(k7_filter_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_59]),c_0_87]),c_0_19])]),c_0_20])).

cnf(c_0_105,negated_conjecture,
    ( v2_struct_0(k7_filter_1(esk1_0,esk2_0))
    | ~ l3_lattices(k7_filter_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_59]),c_0_93]),c_0_37])]),c_0_38])).

cnf(c_0_106,negated_conjecture,
    ( v2_struct_0(k7_filter_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_42]),c_0_19]),c_0_37])]),c_0_38]),c_0_20])).

cnf(c_0_107,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_106]),c_0_19]),c_0_37])]),c_0_38]),c_0_20]),
    [proof]).

%------------------------------------------------------------------------------
