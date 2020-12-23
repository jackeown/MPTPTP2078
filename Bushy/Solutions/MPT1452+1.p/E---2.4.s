%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : filter_1__t47_filter_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:09 EDT 2019

% Result     : Theorem 0.88s
% Output     : CNFRefutation 0.88s
% Verified   : 
% Statistics : Number of formulae       :  106 (3029 expanded)
%              Number of clauses        :   81 ( 939 expanded)
%              Number of leaves         :   10 ( 782 expanded)
%              Depth                    :   21
%              Number of atoms          :  954 (71375 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   40 (   7 average)
%              Maximal clause size      :  130 (   5 average)
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
    file('/export/starexec/sandbox2/benchmark/filter_1__t47_filter_1.p',t47_filter_1)).

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
    file('/export/starexec/sandbox2/benchmark/filter_1__t47_filter_1.p',t39_filter_1)).

fof(cc6_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( ( ~ v2_struct_0(X1)
          & v11_lattices(X1)
          & v15_lattices(X1)
          & v16_lattices(X1) )
       => ( ~ v2_struct_0(X1)
          & v17_lattices(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t47_filter_1.p',cc6_lattices)).

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
    file('/export/starexec/sandbox2/benchmark/filter_1__t47_filter_1.p',fc3_filter_1)).

fof(dt_k7_filter_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1)
        & ~ v2_struct_0(X2)
        & l3_lattices(X2) )
     => ( v3_lattices(k7_filter_1(X1,X2))
        & l3_lattices(k7_filter_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t47_filter_1.p',dt_k7_filter_1)).

fof(fc2_filter_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1)
        & ~ v2_struct_0(X2)
        & l3_lattices(X2) )
     => ( ~ v2_struct_0(k7_filter_1(X1,X2))
        & v3_lattices(k7_filter_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t47_filter_1.p',fc2_filter_1)).

fof(cc5_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( ( ~ v2_struct_0(X1)
          & v17_lattices(X1) )
       => ( ~ v2_struct_0(X1)
          & v11_lattices(X1)
          & v15_lattices(X1)
          & v16_lattices(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t47_filter_1.p',cc5_lattices)).

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
    file('/export/starexec/sandbox2/benchmark/filter_1__t47_filter_1.p',t46_filter_1)).

fof(c_0_8,negated_conjecture,(
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

fof(c_0_9,plain,(
    ! [X2,X1] :
      ( epred1_2(X1,X2)
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

fof(c_0_10,negated_conjecture,
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
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])])).

fof(c_0_11,plain,(
    ! [X2,X1] :
      ( epred1_2(X1,X2)
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
    inference(split_equiv,[status(thm)],[c_0_9])).

fof(c_0_12,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v10_lattices(X2)
            & l3_lattices(X2) )
         => epred1_2(X1,X2) ) ) ),
    inference(apply_def,[status(thm)],[t39_filter_1,c_0_9])).

cnf(c_0_13,negated_conjecture,
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
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( v10_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( v10_lattices(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( l3_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,negated_conjecture,
    ( l3_lattices(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_19,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_20,plain,(
    ! [X78] :
      ( ( ~ v2_struct_0(X78)
        | v2_struct_0(X78)
        | ~ v11_lattices(X78)
        | ~ v15_lattices(X78)
        | ~ v16_lattices(X78)
        | ~ l3_lattices(X78) )
      & ( v17_lattices(X78)
        | v2_struct_0(X78)
        | ~ v11_lattices(X78)
        | ~ v15_lattices(X78)
        | ~ v16_lattices(X78)
        | ~ l3_lattices(X78) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc6_lattices])])])])).

fof(c_0_21,plain,(
    ! [X214,X215] :
      ( ( ~ v2_struct_0(k7_filter_1(X215,X214))
        | v2_struct_0(X215)
        | ~ v10_lattices(X215)
        | ~ v11_lattices(X215)
        | ~ l3_lattices(X215)
        | v2_struct_0(X214)
        | ~ v10_lattices(X214)
        | ~ v11_lattices(X214)
        | ~ l3_lattices(X214)
        | ~ epred1_2(X215,X214) )
      & ( v10_lattices(k7_filter_1(X215,X214))
        | v2_struct_0(X215)
        | ~ v10_lattices(X215)
        | ~ v11_lattices(X215)
        | ~ l3_lattices(X215)
        | v2_struct_0(X214)
        | ~ v10_lattices(X214)
        | ~ v11_lattices(X214)
        | ~ l3_lattices(X214)
        | ~ epred1_2(X215,X214) )
      & ( v11_lattices(k7_filter_1(X215,X214))
        | v2_struct_0(X215)
        | ~ v10_lattices(X215)
        | ~ v11_lattices(X215)
        | ~ l3_lattices(X215)
        | v2_struct_0(X214)
        | ~ v10_lattices(X214)
        | ~ v11_lattices(X214)
        | ~ l3_lattices(X214)
        | ~ epred1_2(X215,X214) )
      & ( l3_lattices(k7_filter_1(X215,X214))
        | v2_struct_0(X215)
        | ~ v10_lattices(X215)
        | ~ v11_lattices(X215)
        | ~ l3_lattices(X215)
        | v2_struct_0(X214)
        | ~ v10_lattices(X214)
        | ~ v11_lattices(X214)
        | ~ l3_lattices(X214)
        | ~ epred1_2(X215,X214) )
      & ( ~ v2_struct_0(X215)
        | v2_struct_0(k7_filter_1(X215,X214))
        | ~ v10_lattices(k7_filter_1(X215,X214))
        | ~ v11_lattices(k7_filter_1(X215,X214))
        | ~ l3_lattices(k7_filter_1(X215,X214))
        | ~ epred1_2(X215,X214) )
      & ( v10_lattices(X215)
        | v2_struct_0(k7_filter_1(X215,X214))
        | ~ v10_lattices(k7_filter_1(X215,X214))
        | ~ v11_lattices(k7_filter_1(X215,X214))
        | ~ l3_lattices(k7_filter_1(X215,X214))
        | ~ epred1_2(X215,X214) )
      & ( v11_lattices(X215)
        | v2_struct_0(k7_filter_1(X215,X214))
        | ~ v10_lattices(k7_filter_1(X215,X214))
        | ~ v11_lattices(k7_filter_1(X215,X214))
        | ~ l3_lattices(k7_filter_1(X215,X214))
        | ~ epred1_2(X215,X214) )
      & ( l3_lattices(X215)
        | v2_struct_0(k7_filter_1(X215,X214))
        | ~ v10_lattices(k7_filter_1(X215,X214))
        | ~ v11_lattices(k7_filter_1(X215,X214))
        | ~ l3_lattices(k7_filter_1(X215,X214))
        | ~ epred1_2(X215,X214) )
      & ( ~ v2_struct_0(X214)
        | v2_struct_0(k7_filter_1(X215,X214))
        | ~ v10_lattices(k7_filter_1(X215,X214))
        | ~ v11_lattices(k7_filter_1(X215,X214))
        | ~ l3_lattices(k7_filter_1(X215,X214))
        | ~ epred1_2(X215,X214) )
      & ( v10_lattices(X214)
        | v2_struct_0(k7_filter_1(X215,X214))
        | ~ v10_lattices(k7_filter_1(X215,X214))
        | ~ v11_lattices(k7_filter_1(X215,X214))
        | ~ l3_lattices(k7_filter_1(X215,X214))
        | ~ epred1_2(X215,X214) )
      & ( v11_lattices(X214)
        | v2_struct_0(k7_filter_1(X215,X214))
        | ~ v10_lattices(k7_filter_1(X215,X214))
        | ~ v11_lattices(k7_filter_1(X215,X214))
        | ~ l3_lattices(k7_filter_1(X215,X214))
        | ~ epred1_2(X215,X214) )
      & ( l3_lattices(X214)
        | v2_struct_0(k7_filter_1(X215,X214))
        | ~ v10_lattices(k7_filter_1(X215,X214))
        | ~ v11_lattices(k7_filter_1(X215,X214))
        | ~ l3_lattices(k7_filter_1(X215,X214))
        | ~ epred1_2(X215,X214) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])).

fof(c_0_22,plain,(
    ! [X197,X198] :
      ( v2_struct_0(X197)
      | ~ v10_lattices(X197)
      | ~ l3_lattices(X197)
      | v2_struct_0(X198)
      | ~ v10_lattices(X198)
      | ~ l3_lattices(X198)
      | epred1_2(X197,X198) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])).

fof(c_0_23,plain,(
    ! [X123,X124] :
      ( ( v3_lattices(k7_filter_1(X123,X124))
        | v2_struct_0(X123)
        | ~ v10_lattices(X123)
        | ~ l3_lattices(X123)
        | v2_struct_0(X124)
        | ~ v10_lattices(X124)
        | ~ l3_lattices(X124) )
      & ( v10_lattices(k7_filter_1(X123,X124))
        | v2_struct_0(X123)
        | ~ v10_lattices(X123)
        | ~ l3_lattices(X123)
        | v2_struct_0(X124)
        | ~ v10_lattices(X124)
        | ~ l3_lattices(X124) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc3_filter_1])])])])).

fof(c_0_24,plain,(
    ! [X101,X102] :
      ( ( v3_lattices(k7_filter_1(X101,X102))
        | v2_struct_0(X101)
        | ~ l3_lattices(X101)
        | v2_struct_0(X102)
        | ~ l3_lattices(X102) )
      & ( l3_lattices(k7_filter_1(X101,X102))
        | v2_struct_0(X101)
        | ~ l3_lattices(X101)
        | v2_struct_0(X102)
        | ~ l3_lattices(X102) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_filter_1])])])])).

fof(c_0_25,plain,(
    ! [X119,X120] :
      ( ( ~ v2_struct_0(k7_filter_1(X119,X120))
        | v2_struct_0(X119)
        | ~ l3_lattices(X119)
        | v2_struct_0(X120)
        | ~ l3_lattices(X120) )
      & ( v3_lattices(k7_filter_1(X119,X120))
        | v2_struct_0(X119)
        | ~ l3_lattices(X119)
        | v2_struct_0(X120)
        | ~ l3_lattices(X120) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_filter_1])])])])).

fof(c_0_26,plain,(
    ! [X71] :
      ( ( ~ v2_struct_0(X71)
        | v2_struct_0(X71)
        | ~ v17_lattices(X71)
        | ~ l3_lattices(X71) )
      & ( v11_lattices(X71)
        | v2_struct_0(X71)
        | ~ v17_lattices(X71)
        | ~ l3_lattices(X71) )
      & ( v15_lattices(X71)
        | v2_struct_0(X71)
        | ~ v17_lattices(X71)
        | ~ l3_lattices(X71) )
      & ( v16_lattices(X71)
        | v2_struct_0(X71)
        | ~ v17_lattices(X71)
        | ~ l3_lattices(X71) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_lattices])])])])).

fof(c_0_27,plain,(
    ! [X2,X1] :
      ( epred2_2(X1,X2)
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

cnf(c_0_28,negated_conjecture,
    ( v2_struct_0(k7_filter_1(esk1_0,esk2_0))
    | ~ v17_lattices(k7_filter_1(esk1_0,esk2_0))
    | ~ v17_lattices(esk1_0)
    | ~ v17_lattices(esk2_0)
    | ~ l3_lattices(k7_filter_1(esk1_0,esk2_0))
    | ~ v10_lattices(k7_filter_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13,c_0_14]),c_0_15]),c_0_16]),c_0_17])]),c_0_18]),c_0_19])).

cnf(c_0_29,plain,
    ( v17_lattices(X1)
    | v2_struct_0(X1)
    | ~ v11_lattices(X1)
    | ~ v15_lattices(X1)
    | ~ v16_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( v11_lattices(X1)
    | v2_struct_0(k7_filter_1(X2,X1))
    | ~ v10_lattices(k7_filter_1(X2,X1))
    | ~ v11_lattices(k7_filter_1(X2,X1))
    | ~ l3_lattices(k7_filter_1(X2,X1))
    | ~ epred1_2(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | epred1_2(X1,X2)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( v10_lattices(k7_filter_1(X1,X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,plain,
    ( l3_lattices(k7_filter_1(X1,X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l3_lattices(X1)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_struct_0(k7_filter_1(X1,X2))
    | ~ l3_lattices(X1)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,plain,
    ( v11_lattices(X1)
    | v2_struct_0(X1)
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,negated_conjecture,
    ( v17_lattices(k7_filter_1(esk1_0,esk2_0))
    | v17_lattices(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_37,negated_conjecture,
    ( l3_lattices(k7_filter_1(esk1_0,esk2_0))
    | v17_lattices(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_38,negated_conjecture,
    ( v17_lattices(esk2_0)
    | ~ v2_struct_0(k7_filter_1(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_39,plain,(
    ! [X2,X1] :
      ( epred2_2(X1,X2)
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
    inference(split_equiv,[status(thm)],[c_0_27])).

fof(c_0_40,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v10_lattices(X2)
            & l3_lattices(X2) )
         => epred2_2(X1,X2) ) ) ),
    inference(apply_def,[status(thm)],[t46_filter_1,c_0_27])).

cnf(c_0_41,negated_conjecture,
    ( v2_struct_0(k7_filter_1(esk1_0,esk2_0))
    | ~ v16_lattices(esk1_0)
    | ~ v15_lattices(esk1_0)
    | ~ v11_lattices(esk1_0)
    | ~ v17_lattices(k7_filter_1(esk1_0,esk2_0))
    | ~ v17_lattices(esk2_0)
    | ~ l3_lattices(k7_filter_1(esk1_0,esk2_0))
    | ~ v10_lattices(k7_filter_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_16])]),c_0_18])).

cnf(c_0_42,plain,
    ( v11_lattices(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v11_lattices(k7_filter_1(X2,X1))
    | ~ l3_lattices(X1)
    | ~ l3_lattices(X2)
    | ~ v10_lattices(X1)
    | ~ v10_lattices(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_33]),c_0_34])).

cnf(c_0_43,negated_conjecture,
    ( v11_lattices(k7_filter_1(esk1_0,esk2_0))
    | v17_lattices(esk2_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37]),c_0_38])).

cnf(c_0_44,plain,
    ( v11_lattices(X1)
    | v2_struct_0(k7_filter_1(X1,X2))
    | ~ v10_lattices(k7_filter_1(X1,X2))
    | ~ v11_lattices(k7_filter_1(X1,X2))
    | ~ l3_lattices(k7_filter_1(X1,X2))
    | ~ epred1_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_45,negated_conjecture,
    ( v17_lattices(k7_filter_1(esk1_0,esk2_0))
    | v17_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_46,negated_conjecture,
    ( l3_lattices(k7_filter_1(esk1_0,esk2_0))
    | v17_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_47,negated_conjecture,
    ( v17_lattices(esk1_0)
    | ~ v2_struct_0(k7_filter_1(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_48,plain,(
    ! [X216,X217] :
      ( ( ~ v2_struct_0(k7_filter_1(X217,X216))
        | v2_struct_0(X217)
        | ~ v10_lattices(X217)
        | ~ v15_lattices(X217)
        | ~ v16_lattices(X217)
        | ~ l3_lattices(X217)
        | v2_struct_0(X216)
        | ~ v10_lattices(X216)
        | ~ v15_lattices(X216)
        | ~ v16_lattices(X216)
        | ~ l3_lattices(X216)
        | ~ epred2_2(X217,X216) )
      & ( v10_lattices(k7_filter_1(X217,X216))
        | v2_struct_0(X217)
        | ~ v10_lattices(X217)
        | ~ v15_lattices(X217)
        | ~ v16_lattices(X217)
        | ~ l3_lattices(X217)
        | v2_struct_0(X216)
        | ~ v10_lattices(X216)
        | ~ v15_lattices(X216)
        | ~ v16_lattices(X216)
        | ~ l3_lattices(X216)
        | ~ epred2_2(X217,X216) )
      & ( v15_lattices(k7_filter_1(X217,X216))
        | v2_struct_0(X217)
        | ~ v10_lattices(X217)
        | ~ v15_lattices(X217)
        | ~ v16_lattices(X217)
        | ~ l3_lattices(X217)
        | v2_struct_0(X216)
        | ~ v10_lattices(X216)
        | ~ v15_lattices(X216)
        | ~ v16_lattices(X216)
        | ~ l3_lattices(X216)
        | ~ epred2_2(X217,X216) )
      & ( v16_lattices(k7_filter_1(X217,X216))
        | v2_struct_0(X217)
        | ~ v10_lattices(X217)
        | ~ v15_lattices(X217)
        | ~ v16_lattices(X217)
        | ~ l3_lattices(X217)
        | v2_struct_0(X216)
        | ~ v10_lattices(X216)
        | ~ v15_lattices(X216)
        | ~ v16_lattices(X216)
        | ~ l3_lattices(X216)
        | ~ epred2_2(X217,X216) )
      & ( l3_lattices(k7_filter_1(X217,X216))
        | v2_struct_0(X217)
        | ~ v10_lattices(X217)
        | ~ v15_lattices(X217)
        | ~ v16_lattices(X217)
        | ~ l3_lattices(X217)
        | v2_struct_0(X216)
        | ~ v10_lattices(X216)
        | ~ v15_lattices(X216)
        | ~ v16_lattices(X216)
        | ~ l3_lattices(X216)
        | ~ epred2_2(X217,X216) )
      & ( ~ v2_struct_0(X217)
        | v2_struct_0(k7_filter_1(X217,X216))
        | ~ v10_lattices(k7_filter_1(X217,X216))
        | ~ v15_lattices(k7_filter_1(X217,X216))
        | ~ v16_lattices(k7_filter_1(X217,X216))
        | ~ l3_lattices(k7_filter_1(X217,X216))
        | ~ epred2_2(X217,X216) )
      & ( v10_lattices(X217)
        | v2_struct_0(k7_filter_1(X217,X216))
        | ~ v10_lattices(k7_filter_1(X217,X216))
        | ~ v15_lattices(k7_filter_1(X217,X216))
        | ~ v16_lattices(k7_filter_1(X217,X216))
        | ~ l3_lattices(k7_filter_1(X217,X216))
        | ~ epred2_2(X217,X216) )
      & ( v15_lattices(X217)
        | v2_struct_0(k7_filter_1(X217,X216))
        | ~ v10_lattices(k7_filter_1(X217,X216))
        | ~ v15_lattices(k7_filter_1(X217,X216))
        | ~ v16_lattices(k7_filter_1(X217,X216))
        | ~ l3_lattices(k7_filter_1(X217,X216))
        | ~ epred2_2(X217,X216) )
      & ( v16_lattices(X217)
        | v2_struct_0(k7_filter_1(X217,X216))
        | ~ v10_lattices(k7_filter_1(X217,X216))
        | ~ v15_lattices(k7_filter_1(X217,X216))
        | ~ v16_lattices(k7_filter_1(X217,X216))
        | ~ l3_lattices(k7_filter_1(X217,X216))
        | ~ epred2_2(X217,X216) )
      & ( l3_lattices(X217)
        | v2_struct_0(k7_filter_1(X217,X216))
        | ~ v10_lattices(k7_filter_1(X217,X216))
        | ~ v15_lattices(k7_filter_1(X217,X216))
        | ~ v16_lattices(k7_filter_1(X217,X216))
        | ~ l3_lattices(k7_filter_1(X217,X216))
        | ~ epred2_2(X217,X216) )
      & ( ~ v2_struct_0(X216)
        | v2_struct_0(k7_filter_1(X217,X216))
        | ~ v10_lattices(k7_filter_1(X217,X216))
        | ~ v15_lattices(k7_filter_1(X217,X216))
        | ~ v16_lattices(k7_filter_1(X217,X216))
        | ~ l3_lattices(k7_filter_1(X217,X216))
        | ~ epred2_2(X217,X216) )
      & ( v10_lattices(X216)
        | v2_struct_0(k7_filter_1(X217,X216))
        | ~ v10_lattices(k7_filter_1(X217,X216))
        | ~ v15_lattices(k7_filter_1(X217,X216))
        | ~ v16_lattices(k7_filter_1(X217,X216))
        | ~ l3_lattices(k7_filter_1(X217,X216))
        | ~ epred2_2(X217,X216) )
      & ( v15_lattices(X216)
        | v2_struct_0(k7_filter_1(X217,X216))
        | ~ v10_lattices(k7_filter_1(X217,X216))
        | ~ v15_lattices(k7_filter_1(X217,X216))
        | ~ v16_lattices(k7_filter_1(X217,X216))
        | ~ l3_lattices(k7_filter_1(X217,X216))
        | ~ epred2_2(X217,X216) )
      & ( v16_lattices(X216)
        | v2_struct_0(k7_filter_1(X217,X216))
        | ~ v10_lattices(k7_filter_1(X217,X216))
        | ~ v15_lattices(k7_filter_1(X217,X216))
        | ~ v16_lattices(k7_filter_1(X217,X216))
        | ~ l3_lattices(k7_filter_1(X217,X216))
        | ~ epred2_2(X217,X216) )
      & ( l3_lattices(X216)
        | v2_struct_0(k7_filter_1(X217,X216))
        | ~ v10_lattices(k7_filter_1(X217,X216))
        | ~ v15_lattices(k7_filter_1(X217,X216))
        | ~ v16_lattices(k7_filter_1(X217,X216))
        | ~ l3_lattices(k7_filter_1(X217,X216))
        | ~ epred2_2(X217,X216) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_39])])])])).

fof(c_0_49,plain,(
    ! [X201,X202] :
      ( v2_struct_0(X201)
      | ~ v10_lattices(X201)
      | ~ l3_lattices(X201)
      | v2_struct_0(X202)
      | ~ v10_lattices(X202)
      | ~ l3_lattices(X202)
      | epred2_2(X201,X202) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_40])])])])).

cnf(c_0_50,negated_conjecture,
    ( v2_struct_0(k7_filter_1(esk1_0,esk2_0))
    | ~ v16_lattices(esk1_0)
    | ~ v16_lattices(esk2_0)
    | ~ v15_lattices(esk1_0)
    | ~ v15_lattices(esk2_0)
    | ~ v11_lattices(esk1_0)
    | ~ v11_lattices(esk2_0)
    | ~ v17_lattices(k7_filter_1(esk1_0,esk2_0))
    | ~ l3_lattices(k7_filter_1(esk1_0,esk2_0))
    | ~ v10_lattices(k7_filter_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_29]),c_0_17])]),c_0_19])).

cnf(c_0_51,negated_conjecture,
    ( v10_lattices(k7_filter_1(esk1_0,esk2_0))
    | v17_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_52,negated_conjecture,
    ( v11_lattices(esk2_0)
    | v17_lattices(esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_17]),c_0_16]),c_0_15]),c_0_14])]),c_0_18]),c_0_19])).

cnf(c_0_53,plain,
    ( v11_lattices(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v11_lattices(k7_filter_1(X1,X2))
    | ~ l3_lattices(X2)
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X2)
    | ~ v10_lattices(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_31]),c_0_32]),c_0_33]),c_0_34])).

cnf(c_0_54,negated_conjecture,
    ( v11_lattices(k7_filter_1(esk1_0,esk2_0))
    | v17_lattices(esk1_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_45]),c_0_46]),c_0_47])).

cnf(c_0_55,plain,
    ( v15_lattices(X1)
    | v2_struct_0(k7_filter_1(X2,X1))
    | ~ v10_lattices(k7_filter_1(X2,X1))
    | ~ v15_lattices(k7_filter_1(X2,X1))
    | ~ v16_lattices(k7_filter_1(X2,X1))
    | ~ l3_lattices(k7_filter_1(X2,X1))
    | ~ epred2_2(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_56,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | epred2_2(X1,X2)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_57,plain,
    ( v16_lattices(X1)
    | v2_struct_0(X1)
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_58,plain,
    ( v15_lattices(X1)
    | v2_struct_0(X1)
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_59,negated_conjecture,
    ( v17_lattices(esk1_0)
    | ~ v16_lattices(esk1_0)
    | ~ v16_lattices(esk2_0)
    | ~ v15_lattices(esk1_0)
    | ~ v15_lattices(esk2_0)
    | ~ v11_lattices(esk1_0)
    | ~ v11_lattices(esk2_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_45]),c_0_51]),c_0_46]),c_0_47])).

cnf(c_0_60,negated_conjecture,
    ( v11_lattices(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_52]),c_0_17])]),c_0_19])).

cnf(c_0_61,negated_conjecture,
    ( v11_lattices(esk1_0)
    | v17_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_17]),c_0_16]),c_0_15]),c_0_14])]),c_0_18]),c_0_19])).

cnf(c_0_62,plain,
    ( v15_lattices(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v16_lattices(k7_filter_1(X2,X1))
    | ~ v15_lattices(k7_filter_1(X2,X1))
    | ~ l3_lattices(X1)
    | ~ l3_lattices(X2)
    | ~ v10_lattices(X1)
    | ~ v10_lattices(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_32]),c_0_33]),c_0_34])).

cnf(c_0_63,negated_conjecture,
    ( v16_lattices(k7_filter_1(esk1_0,esk2_0))
    | v17_lattices(esk2_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_36]),c_0_37]),c_0_38])).

cnf(c_0_64,negated_conjecture,
    ( v15_lattices(k7_filter_1(esk1_0,esk2_0))
    | v17_lattices(esk2_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_36]),c_0_37]),c_0_38])).

cnf(c_0_65,plain,
    ( v15_lattices(X1)
    | v2_struct_0(k7_filter_1(X1,X2))
    | ~ v10_lattices(k7_filter_1(X1,X2))
    | ~ v15_lattices(k7_filter_1(X1,X2))
    | ~ v16_lattices(k7_filter_1(X1,X2))
    | ~ l3_lattices(k7_filter_1(X1,X2))
    | ~ epred2_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_66,negated_conjecture,
    ( v17_lattices(esk1_0)
    | ~ v16_lattices(esk1_0)
    | ~ v16_lattices(esk2_0)
    | ~ v15_lattices(esk1_0)
    | ~ v15_lattices(esk2_0)
    | ~ v11_lattices(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_60])])).

cnf(c_0_67,negated_conjecture,
    ( v11_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_61]),c_0_16])]),c_0_18])).

cnf(c_0_68,negated_conjecture,
    ( v15_lattices(esk2_0)
    | v17_lattices(esk2_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_17]),c_0_16]),c_0_15]),c_0_14])]),c_0_18]),c_0_19]),c_0_64])).

cnf(c_0_69,plain,
    ( v15_lattices(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v16_lattices(k7_filter_1(X1,X2))
    | ~ v15_lattices(k7_filter_1(X1,X2))
    | ~ l3_lattices(X2)
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X2)
    | ~ v10_lattices(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_56]),c_0_32]),c_0_33]),c_0_34])).

cnf(c_0_70,negated_conjecture,
    ( v16_lattices(k7_filter_1(esk1_0,esk2_0))
    | v17_lattices(esk1_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_45]),c_0_46]),c_0_47])).

cnf(c_0_71,negated_conjecture,
    ( v15_lattices(k7_filter_1(esk1_0,esk2_0))
    | v17_lattices(esk1_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_45]),c_0_46]),c_0_47])).

cnf(c_0_72,plain,
    ( v16_lattices(X1)
    | v2_struct_0(k7_filter_1(X2,X1))
    | ~ v10_lattices(k7_filter_1(X2,X1))
    | ~ v15_lattices(k7_filter_1(X2,X1))
    | ~ v16_lattices(k7_filter_1(X2,X1))
    | ~ l3_lattices(k7_filter_1(X2,X1))
    | ~ epred2_2(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_73,negated_conjecture,
    ( v2_struct_0(k7_filter_1(esk1_0,esk2_0))
    | ~ v16_lattices(k7_filter_1(esk1_0,esk2_0))
    | ~ v16_lattices(esk1_0)
    | ~ v16_lattices(esk2_0)
    | ~ v15_lattices(k7_filter_1(esk1_0,esk2_0))
    | ~ v15_lattices(esk1_0)
    | ~ v15_lattices(esk2_0)
    | ~ v11_lattices(k7_filter_1(esk1_0,esk2_0))
    | ~ v11_lattices(esk1_0)
    | ~ v11_lattices(esk2_0)
    | ~ l3_lattices(k7_filter_1(esk1_0,esk2_0))
    | ~ v10_lattices(k7_filter_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_29])).

cnf(c_0_74,negated_conjecture,
    ( v17_lattices(esk1_0)
    | ~ v16_lattices(esk1_0)
    | ~ v16_lattices(esk2_0)
    | ~ v15_lattices(esk1_0)
    | ~ v15_lattices(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_67])])).

cnf(c_0_75,negated_conjecture,
    ( v15_lattices(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_68]),c_0_17])]),c_0_19])).

cnf(c_0_76,negated_conjecture,
    ( v15_lattices(esk1_0)
    | v17_lattices(esk1_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_17]),c_0_16]),c_0_15]),c_0_14])]),c_0_18]),c_0_19]),c_0_71])).

cnf(c_0_77,plain,
    ( v16_lattices(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v16_lattices(k7_filter_1(X2,X1))
    | ~ v15_lattices(k7_filter_1(X2,X1))
    | ~ l3_lattices(X1)
    | ~ l3_lattices(X2)
    | ~ v10_lattices(X1)
    | ~ v10_lattices(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_56]),c_0_32]),c_0_33]),c_0_34])).

cnf(c_0_78,negated_conjecture,
    ( v2_struct_0(k7_filter_1(esk1_0,esk2_0))
    | ~ v16_lattices(k7_filter_1(esk1_0,esk2_0))
    | ~ v16_lattices(esk1_0)
    | ~ v16_lattices(esk2_0)
    | ~ v15_lattices(k7_filter_1(esk1_0,esk2_0))
    | ~ v15_lattices(esk1_0)
    | ~ v15_lattices(esk2_0)
    | ~ v11_lattices(k7_filter_1(esk1_0,esk2_0))
    | ~ v11_lattices(esk1_0)
    | ~ l3_lattices(k7_filter_1(esk1_0,esk2_0))
    | ~ v10_lattices(k7_filter_1(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_60])])).

cnf(c_0_79,negated_conjecture,
    ( v17_lattices(esk1_0)
    | ~ v16_lattices(esk1_0)
    | ~ v16_lattices(esk2_0)
    | ~ v15_lattices(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_75])])).

cnf(c_0_80,negated_conjecture,
    ( v15_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_76]),c_0_16])]),c_0_18])).

cnf(c_0_81,negated_conjecture,
    ( v16_lattices(esk2_0)
    | v17_lattices(esk2_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_63]),c_0_17]),c_0_16]),c_0_15]),c_0_14])]),c_0_18]),c_0_19]),c_0_64])).

cnf(c_0_82,negated_conjecture,
    ( v2_struct_0(k7_filter_1(esk1_0,esk2_0))
    | ~ v16_lattices(k7_filter_1(esk1_0,esk2_0))
    | ~ v16_lattices(esk1_0)
    | ~ v16_lattices(esk2_0)
    | ~ v15_lattices(k7_filter_1(esk1_0,esk2_0))
    | ~ v15_lattices(esk1_0)
    | ~ v15_lattices(esk2_0)
    | ~ v11_lattices(k7_filter_1(esk1_0,esk2_0))
    | ~ l3_lattices(k7_filter_1(esk1_0,esk2_0))
    | ~ v10_lattices(k7_filter_1(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_67])])).

cnf(c_0_83,plain,
    ( v16_lattices(X1)
    | v2_struct_0(k7_filter_1(X1,X2))
    | ~ v10_lattices(k7_filter_1(X1,X2))
    | ~ v15_lattices(k7_filter_1(X1,X2))
    | ~ v16_lattices(k7_filter_1(X1,X2))
    | ~ l3_lattices(k7_filter_1(X1,X2))
    | ~ epred2_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_84,negated_conjecture,
    ( v17_lattices(esk1_0)
    | ~ v16_lattices(esk1_0)
    | ~ v16_lattices(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_80])])).

cnf(c_0_85,negated_conjecture,
    ( v16_lattices(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_81]),c_0_17])]),c_0_19])).

cnf(c_0_86,negated_conjecture,
    ( v2_struct_0(k7_filter_1(esk1_0,esk2_0))
    | ~ v16_lattices(k7_filter_1(esk1_0,esk2_0))
    | ~ v16_lattices(esk1_0)
    | ~ v16_lattices(esk2_0)
    | ~ v15_lattices(k7_filter_1(esk1_0,esk2_0))
    | ~ v15_lattices(esk1_0)
    | ~ v11_lattices(k7_filter_1(esk1_0,esk2_0))
    | ~ l3_lattices(k7_filter_1(esk1_0,esk2_0))
    | ~ v10_lattices(k7_filter_1(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_82,c_0_75])])).

cnf(c_0_87,plain,
    ( v16_lattices(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v16_lattices(k7_filter_1(X1,X2))
    | ~ v15_lattices(k7_filter_1(X1,X2))
    | ~ l3_lattices(X2)
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X2)
    | ~ v10_lattices(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_56]),c_0_32]),c_0_33]),c_0_34])).

cnf(c_0_88,negated_conjecture,
    ( v17_lattices(esk1_0)
    | ~ v16_lattices(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_84,c_0_85])])).

cnf(c_0_89,negated_conjecture,
    ( v2_struct_0(k7_filter_1(esk1_0,esk2_0))
    | ~ v16_lattices(k7_filter_1(esk1_0,esk2_0))
    | ~ v16_lattices(esk1_0)
    | ~ v16_lattices(esk2_0)
    | ~ v15_lattices(k7_filter_1(esk1_0,esk2_0))
    | ~ v11_lattices(k7_filter_1(esk1_0,esk2_0))
    | ~ l3_lattices(k7_filter_1(esk1_0,esk2_0))
    | ~ v10_lattices(k7_filter_1(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_86,c_0_80])])).

cnf(c_0_90,negated_conjecture,
    ( v17_lattices(esk1_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_70]),c_0_17]),c_0_16]),c_0_15]),c_0_14])]),c_0_18]),c_0_19]),c_0_71]),c_0_88])).

cnf(c_0_91,negated_conjecture,
    ( v2_struct_0(k7_filter_1(esk1_0,esk2_0))
    | ~ v16_lattices(k7_filter_1(esk1_0,esk2_0))
    | ~ v16_lattices(esk1_0)
    | ~ v15_lattices(k7_filter_1(esk1_0,esk2_0))
    | ~ v11_lattices(k7_filter_1(esk1_0,esk2_0))
    | ~ l3_lattices(k7_filter_1(esk1_0,esk2_0))
    | ~ v10_lattices(k7_filter_1(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_89,c_0_85])])).

cnf(c_0_92,negated_conjecture,
    ( v16_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_90]),c_0_16])]),c_0_18])).

cnf(c_0_93,plain,
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
    | ~ epred2_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_94,negated_conjecture,
    ( v2_struct_0(k7_filter_1(esk1_0,esk2_0))
    | ~ v16_lattices(k7_filter_1(esk1_0,esk2_0))
    | ~ v15_lattices(k7_filter_1(esk1_0,esk2_0))
    | ~ v11_lattices(k7_filter_1(esk1_0,esk2_0))
    | ~ l3_lattices(k7_filter_1(esk1_0,esk2_0))
    | ~ v10_lattices(k7_filter_1(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_91,c_0_92])])).

cnf(c_0_95,plain,
    ( v16_lattices(k7_filter_1(X1,X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v16_lattices(X2)
    | ~ v16_lattices(X1)
    | ~ v15_lattices(X2)
    | ~ v15_lattices(X1)
    | ~ l3_lattices(X2)
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X2)
    | ~ v10_lattices(X1) ),
    inference(csr,[status(thm)],[c_0_93,c_0_56])).

cnf(c_0_96,plain,
    ( v11_lattices(k7_filter_1(X1,X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v10_lattices(X1)
    | ~ v11_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X2)
    | ~ v11_lattices(X2)
    | ~ l3_lattices(X2)
    | ~ epred1_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_97,plain,
    ( v2_struct_0(k7_filter_1(esk1_0,esk2_0))
    | ~ v15_lattices(k7_filter_1(esk1_0,esk2_0))
    | ~ v11_lattices(k7_filter_1(esk1_0,esk2_0))
    | ~ l3_lattices(k7_filter_1(esk1_0,esk2_0))
    | ~ v10_lattices(k7_filter_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_85]),c_0_92]),c_0_75]),c_0_80]),c_0_17]),c_0_16]),c_0_15]),c_0_14])]),c_0_19]),c_0_18])).

cnf(c_0_98,plain,
    ( v11_lattices(k7_filter_1(X1,X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v11_lattices(X2)
    | ~ v11_lattices(X1)
    | ~ l3_lattices(X2)
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X2)
    | ~ v10_lattices(X1) ),
    inference(csr,[status(thm)],[c_0_96,c_0_31])).

cnf(c_0_99,plain,
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
    | ~ epred2_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_100,plain,
    ( v2_struct_0(k7_filter_1(esk1_0,esk2_0))
    | ~ v15_lattices(k7_filter_1(esk1_0,esk2_0))
    | ~ l3_lattices(k7_filter_1(esk1_0,esk2_0))
    | ~ v10_lattices(k7_filter_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_98]),c_0_60]),c_0_67]),c_0_17]),c_0_16]),c_0_15]),c_0_14])]),c_0_19]),c_0_18])).

cnf(c_0_101,plain,
    ( v15_lattices(k7_filter_1(X1,X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v16_lattices(X2)
    | ~ v16_lattices(X1)
    | ~ v15_lattices(X2)
    | ~ v15_lattices(X1)
    | ~ l3_lattices(X2)
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X2)
    | ~ v10_lattices(X1) ),
    inference(csr,[status(thm)],[c_0_99,c_0_56])).

cnf(c_0_102,plain,
    ( v2_struct_0(k7_filter_1(esk1_0,esk2_0))
    | ~ l3_lattices(k7_filter_1(esk1_0,esk2_0))
    | ~ v10_lattices(k7_filter_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_101]),c_0_85]),c_0_92]),c_0_75]),c_0_80]),c_0_17]),c_0_16]),c_0_15]),c_0_14])]),c_0_19]),c_0_18])).

cnf(c_0_103,plain,
    ( v2_struct_0(k7_filter_1(esk1_0,esk2_0))
    | ~ l3_lattices(k7_filter_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_32]),c_0_17]),c_0_16]),c_0_15]),c_0_14])]),c_0_19]),c_0_18])).

cnf(c_0_104,plain,
    ( v2_struct_0(k7_filter_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_33]),c_0_17]),c_0_16])]),c_0_19]),c_0_18])).

cnf(c_0_105,plain,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_104]),c_0_17]),c_0_16])]),c_0_19]),c_0_18]),
    [proof]).
%------------------------------------------------------------------------------
