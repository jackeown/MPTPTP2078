%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:10:30 EST 2020

% Result     : Theorem 0.47s
% Output     : CNFRefutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  116 (1628 expanded)
%              Number of clauses        :   85 ( 527 expanded)
%              Number of leaves         :   15 ( 401 expanded)
%              Depth                    :   16
%              Number of atoms          :  530 (10903 expanded)
%              Number of equality atoms :   56 (  95 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   28 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t53_lattices,conjecture,(
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

fof(dt_k7_lattices,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => m1_subset_1(k7_lattices(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_lattices)).

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

fof(reflexivity_r3_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & v8_lattices(X1)
        & v9_lattices(X1)
        & l3_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => r3_lattices(X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r3_lattices)).

fof(t21_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v8_lattices(X1)
        & v9_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r1_lattices(X1,X2,X3)
              <=> k2_lattices(X1,X2,X3) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_lattices)).

fof(d8_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => ( v8_lattices(X1)
      <=> ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => k1_lattices(X1,k2_lattices(X1,X2,X3),X3) = X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattices)).

fof(redefinition_k3_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v4_lattices(X1)
        & l2_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k3_lattices(X1,X2,X3) = k1_lattices(X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_lattices)).

fof(t50_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v17_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => k7_lattices(X1,k4_lattices(X1,X2,X3)) = k3_lattices(X1,k7_lattices(X1,X2),k7_lattices(X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_lattices)).

fof(dt_k2_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & l1_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k2_lattices(X1,X2,X3),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_lattices)).

fof(dt_l3_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( l1_lattices(X1)
        & l2_lattices(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(d3_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l2_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r1_lattices(X1,X2,X3)
              <=> k1_lattices(X1,X2,X3) = X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_lattices)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_lattices)).

fof(redefinition_k4_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & l1_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k4_lattices(X1,X2,X3) = k2_lattices(X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_lattices)).

fof(t27_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v7_lattices(X1)
        & v8_lattices(X1)
        & v9_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( r1_lattices(X1,X2,X3)
                   => r1_lattices(X1,k2_lattices(X1,X2,X4),k2_lattices(X1,X3,X4)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_lattices)).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1] :
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
    inference(assume_negation,[status(cth)],[t53_lattices])).

fof(c_0_16,plain,(
    ! [X22,X23] :
      ( v2_struct_0(X22)
      | ~ l3_lattices(X22)
      | ~ m1_subset_1(X23,u1_struct_0(X22))
      | m1_subset_1(k7_lattices(X22,X23),u1_struct_0(X22)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_lattices])])])).

fof(c_0_17,negated_conjecture,
    ( ~ v2_struct_0(esk5_0)
    & v10_lattices(esk5_0)
    & v17_lattices(esk5_0)
    & l3_lattices(esk5_0)
    & m1_subset_1(esk6_0,u1_struct_0(esk5_0))
    & m1_subset_1(esk7_0,u1_struct_0(esk5_0))
    & r3_lattices(esk5_0,esk6_0,esk7_0)
    & ~ r3_lattices(esk5_0,k7_lattices(esk5_0,esk7_0),k7_lattices(esk5_0,esk6_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).

fof(c_0_18,plain,(
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

fof(c_0_19,plain,(
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

cnf(c_0_20,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k7_lattices(X1,X2),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( l3_lattices(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( v9_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( v10_lattices(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_28,plain,(
    ! [X34,X35,X36] :
      ( v2_struct_0(X34)
      | ~ v6_lattices(X34)
      | ~ v8_lattices(X34)
      | ~ v9_lattices(X34)
      | ~ l3_lattices(X34)
      | ~ m1_subset_1(X35,u1_struct_0(X34))
      | ~ m1_subset_1(X36,u1_struct_0(X34))
      | r3_lattices(X34,X35,X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[reflexivity_r3_lattices])])])).

fof(c_0_29,plain,(
    ! [X37,X38,X39] :
      ( ( ~ r1_lattices(X37,X38,X39)
        | k2_lattices(X37,X38,X39) = X38
        | ~ m1_subset_1(X39,u1_struct_0(X37))
        | ~ m1_subset_1(X38,u1_struct_0(X37))
        | v2_struct_0(X37)
        | ~ v8_lattices(X37)
        | ~ v9_lattices(X37)
        | ~ l3_lattices(X37) )
      & ( k2_lattices(X37,X38,X39) != X38
        | r1_lattices(X37,X38,X39)
        | ~ m1_subset_1(X39,u1_struct_0(X37))
        | ~ m1_subset_1(X38,u1_struct_0(X37))
        | v2_struct_0(X37)
        | ~ v8_lattices(X37)
        | ~ v9_lattices(X37)
        | ~ l3_lattices(X37) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t21_lattices])])])])])).

cnf(c_0_30,plain,
    ( r1_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(k7_lattices(esk5_0,esk7_0),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])]),c_0_23])).

cnf(c_0_32,negated_conjecture,
    ( v9_lattices(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_22])]),c_0_23])).

cnf(c_0_33,negated_conjecture,
    ( v8_lattices(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_25]),c_0_22])]),c_0_23])).

cnf(c_0_34,negated_conjecture,
    ( v6_lattices(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_25]),c_0_22])]),c_0_23])).

cnf(c_0_35,plain,
    ( v2_struct_0(X1)
    | r3_lattices(X1,X2,X2)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_36,plain,(
    ! [X9,X10,X11] :
      ( ( ~ v8_lattices(X9)
        | ~ m1_subset_1(X10,u1_struct_0(X9))
        | ~ m1_subset_1(X11,u1_struct_0(X9))
        | k1_lattices(X9,k2_lattices(X9,X10,X11),X11) = X11
        | v2_struct_0(X9)
        | ~ l3_lattices(X9) )
      & ( m1_subset_1(esk1_1(X9),u1_struct_0(X9))
        | v8_lattices(X9)
        | v2_struct_0(X9)
        | ~ l3_lattices(X9) )
      & ( m1_subset_1(esk2_1(X9),u1_struct_0(X9))
        | v8_lattices(X9)
        | v2_struct_0(X9)
        | ~ l3_lattices(X9) )
      & ( k1_lattices(X9,k2_lattices(X9,esk1_1(X9),esk2_1(X9)),esk2_1(X9)) != esk2_1(X9)
        | v8_lattices(X9)
        | v2_struct_0(X9)
        | ~ l3_lattices(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d8_lattices])])])])])])).

cnf(c_0_37,plain,
    ( k2_lattices(X1,X2,X3) = X2
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,negated_conjecture,
    ( r1_lattices(esk5_0,X1,k7_lattices(esk5_0,esk7_0))
    | ~ r3_lattices(esk5_0,X1,k7_lattices(esk5_0,esk7_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_33]),c_0_34]),c_0_22])]),c_0_23])).

cnf(c_0_39,negated_conjecture,
    ( r3_lattices(esk5_0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_21]),c_0_32]),c_0_33]),c_0_34]),c_0_22])]),c_0_23])).

fof(c_0_40,plain,(
    ! [X25,X26,X27] :
      ( v2_struct_0(X25)
      | ~ v4_lattices(X25)
      | ~ l2_lattices(X25)
      | ~ m1_subset_1(X26,u1_struct_0(X25))
      | ~ m1_subset_1(X27,u1_struct_0(X25))
      | k3_lattices(X25,X26,X27) = k1_lattices(X25,X26,X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_lattices])])])).

cnf(c_0_41,plain,
    ( v4_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_42,plain,(
    ! [X47,X48,X49] :
      ( v2_struct_0(X47)
      | ~ v10_lattices(X47)
      | ~ v17_lattices(X47)
      | ~ l3_lattices(X47)
      | ~ m1_subset_1(X48,u1_struct_0(X47))
      | ~ m1_subset_1(X49,u1_struct_0(X47))
      | k7_lattices(X47,k4_lattices(X47,X48,X49)) = k3_lattices(X47,k7_lattices(X47,X48),k7_lattices(X47,X49)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t50_lattices])])])])).

fof(c_0_43,plain,(
    ! [X19,X20,X21] :
      ( v2_struct_0(X19)
      | ~ l1_lattices(X19)
      | ~ m1_subset_1(X20,u1_struct_0(X19))
      | ~ m1_subset_1(X21,u1_struct_0(X19))
      | m1_subset_1(k2_lattices(X19,X20,X21),u1_struct_0(X19)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k2_lattices])])])).

cnf(c_0_44,plain,
    ( k1_lattices(X1,k2_lattices(X1,X2,X3),X3) = X3
    | v2_struct_0(X1)
    | ~ v8_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_45,negated_conjecture,
    ( k2_lattices(esk5_0,X1,k7_lattices(esk5_0,esk7_0)) = X1
    | ~ r1_lattices(esk5_0,X1,k7_lattices(esk5_0,esk7_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_31]),c_0_32]),c_0_33]),c_0_22])]),c_0_23])).

cnf(c_0_46,negated_conjecture,
    ( r1_lattices(esk5_0,k7_lattices(esk5_0,esk7_0),k7_lattices(esk5_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_31])])).

cnf(c_0_47,plain,
    ( v2_struct_0(X1)
    | k3_lattices(X1,X2,X3) = k1_lattices(X1,X2,X3)
    | ~ v4_lattices(X1)
    | ~ l2_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_48,negated_conjecture,
    ( v4_lattices(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_25]),c_0_22])]),c_0_23])).

cnf(c_0_49,plain,
    ( v2_struct_0(X1)
    | k7_lattices(X1,k4_lattices(X1,X2,X3)) = k3_lattices(X1,k7_lattices(X1,X2),k7_lattices(X1,X3))
    | ~ v10_lattices(X1)
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_50,negated_conjecture,
    ( v17_lattices(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_51,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k2_lattices(X1,X2,X3),u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_53,plain,(
    ! [X24] :
      ( ( l1_lattices(X24)
        | ~ l3_lattices(X24) )
      & ( l2_lattices(X24)
        | ~ l3_lattices(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).

fof(c_0_54,plain,(
    ! [X6,X7,X8] :
      ( ( ~ r1_lattices(X6,X7,X8)
        | k1_lattices(X6,X7,X8) = X8
        | ~ m1_subset_1(X8,u1_struct_0(X6))
        | ~ m1_subset_1(X7,u1_struct_0(X6))
        | v2_struct_0(X6)
        | ~ l2_lattices(X6) )
      & ( k1_lattices(X6,X7,X8) != X8
        | r1_lattices(X6,X7,X8)
        | ~ m1_subset_1(X8,u1_struct_0(X6))
        | ~ m1_subset_1(X7,u1_struct_0(X6))
        | v2_struct_0(X6)
        | ~ l2_lattices(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d3_lattices])])])])])).

cnf(c_0_55,negated_conjecture,
    ( k1_lattices(esk5_0,k2_lattices(esk5_0,X1,k7_lattices(esk5_0,esk7_0)),k7_lattices(esk5_0,esk7_0)) = k7_lattices(esk5_0,esk7_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_31]),c_0_33]),c_0_22])]),c_0_23])).

cnf(c_0_56,negated_conjecture,
    ( k2_lattices(esk5_0,k7_lattices(esk5_0,esk7_0),k7_lattices(esk5_0,esk7_0)) = k7_lattices(esk5_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_31])])).

cnf(c_0_57,negated_conjecture,
    ( k3_lattices(esk5_0,X1,k7_lattices(esk5_0,esk7_0)) = k1_lattices(esk5_0,X1,k7_lattices(esk5_0,esk7_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ l2_lattices(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_31]),c_0_48])]),c_0_23])).

cnf(c_0_58,negated_conjecture,
    ( k3_lattices(esk5_0,k7_lattices(esk5_0,X1),k7_lattices(esk5_0,esk7_0)) = k7_lattices(esk5_0,k4_lattices(esk5_0,X1,esk7_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_21]),c_0_50]),c_0_25]),c_0_22])]),c_0_23])).

fof(c_0_59,plain,(
    ! [X40,X41,X42] :
      ( v2_struct_0(X40)
      | ~ v4_lattices(X40)
      | ~ l2_lattices(X40)
      | ~ m1_subset_1(X41,u1_struct_0(X40))
      | ~ m1_subset_1(X42,u1_struct_0(X40))
      | ~ r1_lattices(X40,X41,X42)
      | ~ r1_lattices(X40,X42,X41)
      | X41 = X42 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t26_lattices])])])])).

cnf(c_0_60,negated_conjecture,
    ( m1_subset_1(k2_lattices(esk5_0,X1,esk6_0),u1_struct_0(esk5_0))
    | ~ l1_lattices(esk5_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_23])).

cnf(c_0_61,plain,
    ( l1_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_62,plain,
    ( r1_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | k1_lattices(X1,X2,X3) != X3
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_63,negated_conjecture,
    ( k1_lattices(esk5_0,k7_lattices(esk5_0,esk7_0),k7_lattices(esk5_0,esk7_0)) = k7_lattices(esk5_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_31])])).

cnf(c_0_64,negated_conjecture,
    ( k1_lattices(esk5_0,k7_lattices(esk5_0,X1),k7_lattices(esk5_0,esk7_0)) = k7_lattices(esk5_0,k4_lattices(esk5_0,X1,esk7_0))
    | ~ m1_subset_1(k7_lattices(esk5_0,X1),u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ l2_lattices(esk5_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

fof(c_0_65,plain,(
    ! [X28,X29,X30] :
      ( v2_struct_0(X28)
      | ~ v6_lattices(X28)
      | ~ l1_lattices(X28)
      | ~ m1_subset_1(X29,u1_struct_0(X28))
      | ~ m1_subset_1(X30,u1_struct_0(X28))
      | k4_lattices(X28,X29,X30) = k2_lattices(X28,X29,X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k4_lattices])])])).

cnf(c_0_66,negated_conjecture,
    ( r1_lattices(esk5_0,X1,esk7_0)
    | ~ r3_lattices(esk5_0,X1,esk7_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_21]),c_0_32]),c_0_33]),c_0_34]),c_0_22])]),c_0_23])).

cnf(c_0_67,plain,
    ( v2_struct_0(X1)
    | X2 = X3
    | ~ v4_lattices(X1)
    | ~ l2_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_lattices(X1,X2,X3)
    | ~ r1_lattices(X1,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_68,negated_conjecture,
    ( m1_subset_1(k2_lattices(esk5_0,X1,esk6_0),u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_22])])).

cnf(c_0_69,negated_conjecture,
    ( r1_lattices(esk5_0,X1,esk6_0)
    | k1_lattices(esk5_0,X1,esk6_0) != esk6_0
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ l2_lattices(esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_52]),c_0_23])).

cnf(c_0_70,plain,
    ( l2_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

fof(c_0_71,plain,(
    ! [X43,X44,X45,X46] :
      ( v2_struct_0(X43)
      | ~ v7_lattices(X43)
      | ~ v8_lattices(X43)
      | ~ v9_lattices(X43)
      | ~ l3_lattices(X43)
      | ~ m1_subset_1(X44,u1_struct_0(X43))
      | ~ m1_subset_1(X45,u1_struct_0(X43))
      | ~ m1_subset_1(X46,u1_struct_0(X43))
      | ~ r1_lattices(X43,X44,X45)
      | r1_lattices(X43,k2_lattices(X43,X44,X46),k2_lattices(X43,X45,X46)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t27_lattices])])])])).

cnf(c_0_72,plain,
    ( v7_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_73,negated_conjecture,
    ( r1_lattices(esk5_0,X1,esk6_0)
    | ~ r3_lattices(esk5_0,X1,esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_52]),c_0_32]),c_0_33]),c_0_34]),c_0_22])]),c_0_23])).

cnf(c_0_74,negated_conjecture,
    ( k3_lattices(esk5_0,k7_lattices(esk5_0,X1),k7_lattices(esk5_0,esk6_0)) = k7_lattices(esk5_0,k4_lattices(esk5_0,X1,esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_52]),c_0_50]),c_0_25]),c_0_22])]),c_0_23])).

cnf(c_0_75,negated_conjecture,
    ( k7_lattices(esk5_0,k4_lattices(esk5_0,esk7_0,esk7_0)) = k7_lattices(esk5_0,esk7_0)
    | ~ l2_lattices(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_31]),c_0_21])])).

cnf(c_0_76,plain,
    ( v2_struct_0(X1)
    | k4_lattices(X1,X2,X3) = k2_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ l1_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_77,negated_conjecture,
    ( k2_lattices(esk5_0,X1,esk7_0) = X1
    | ~ r1_lattices(esk5_0,X1,esk7_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_21]),c_0_32]),c_0_33]),c_0_22])]),c_0_23])).

cnf(c_0_78,negated_conjecture,
    ( r1_lattices(esk5_0,esk7_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_39]),c_0_21])])).

cnf(c_0_79,negated_conjecture,
    ( X1 = k2_lattices(esk5_0,X2,esk6_0)
    | ~ r1_lattices(esk5_0,k2_lattices(esk5_0,X2,esk6_0),X1)
    | ~ r1_lattices(esk5_0,X1,k2_lattices(esk5_0,X2,esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0))
    | ~ l2_lattices(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_48])]),c_0_23])).

cnf(c_0_80,negated_conjecture,
    ( r1_lattices(esk5_0,X1,esk6_0)
    | k1_lattices(esk5_0,X1,esk6_0) != esk6_0
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_22])])).

cnf(c_0_81,negated_conjecture,
    ( k1_lattices(esk5_0,k2_lattices(esk5_0,X1,esk6_0),esk6_0) = esk6_0
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_52]),c_0_33]),c_0_22])]),c_0_23])).

cnf(c_0_82,plain,
    ( v2_struct_0(X1)
    | r1_lattices(X1,k2_lattices(X1,X2,X4),k2_lattices(X1,X3,X4))
    | ~ v7_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r1_lattices(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_83,negated_conjecture,
    ( v7_lattices(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_25]),c_0_22])]),c_0_23])).

cnf(c_0_84,negated_conjecture,
    ( k2_lattices(esk5_0,X1,esk6_0) = X1
    | ~ r1_lattices(esk5_0,X1,esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_52]),c_0_32]),c_0_33]),c_0_22])]),c_0_23])).

cnf(c_0_85,negated_conjecture,
    ( r1_lattices(esk5_0,esk6_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_39]),c_0_52])])).

cnf(c_0_86,negated_conjecture,
    ( m1_subset_1(k7_lattices(esk5_0,esk6_0),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_52]),c_0_22])]),c_0_23])).

cnf(c_0_87,negated_conjecture,
    ( k7_lattices(esk5_0,k4_lattices(esk5_0,k4_lattices(esk5_0,esk7_0,esk7_0),esk6_0)) = k3_lattices(esk5_0,k7_lattices(esk5_0,esk7_0),k7_lattices(esk5_0,esk6_0))
    | ~ m1_subset_1(k4_lattices(esk5_0,esk7_0,esk7_0),u1_struct_0(esk5_0))
    | ~ l2_lattices(esk5_0) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_88,negated_conjecture,
    ( k4_lattices(esk5_0,X1,esk7_0) = k2_lattices(esk5_0,X1,esk7_0)
    | ~ l1_lattices(esk5_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_21]),c_0_34])]),c_0_23])).

cnf(c_0_89,negated_conjecture,
    ( k2_lattices(esk5_0,esk7_0,esk7_0) = esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_21])])).

cnf(c_0_90,plain,
    ( r3_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_91,negated_conjecture,
    ( X1 = k2_lattices(esk5_0,X2,esk6_0)
    | ~ r1_lattices(esk5_0,k2_lattices(esk5_0,X2,esk6_0),X1)
    | ~ r1_lattices(esk5_0,X1,k2_lattices(esk5_0,X2,esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_70]),c_0_22])])).

cnf(c_0_92,negated_conjecture,
    ( r1_lattices(esk5_0,k2_lattices(esk5_0,X1,esk6_0),esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_68])).

cnf(c_0_93,negated_conjecture,
    ( r1_lattices(esk5_0,k2_lattices(esk5_0,X1,esk6_0),k2_lattices(esk5_0,X2,esk6_0))
    | ~ r1_lattices(esk5_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_52]),c_0_32]),c_0_33]),c_0_83]),c_0_22])]),c_0_23])).

cnf(c_0_94,negated_conjecture,
    ( k2_lattices(esk5_0,esk6_0,esk6_0) = esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_52])])).

cnf(c_0_95,negated_conjecture,
    ( r3_lattices(esk5_0,esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_96,negated_conjecture,
    ( k3_lattices(esk5_0,X1,k7_lattices(esk5_0,esk6_0)) = k1_lattices(esk5_0,X1,k7_lattices(esk5_0,esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ l2_lattices(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_86]),c_0_48])]),c_0_23])).

cnf(c_0_97,negated_conjecture,
    ( k3_lattices(esk5_0,k7_lattices(esk5_0,esk7_0),k7_lattices(esk5_0,esk6_0)) = k7_lattices(esk5_0,k4_lattices(esk5_0,esk7_0,esk6_0))
    | ~ l1_lattices(esk5_0)
    | ~ l2_lattices(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_89]),c_0_89]),c_0_21]),c_0_21])])).

cnf(c_0_98,negated_conjecture,
    ( ~ r3_lattices(esk5_0,k7_lattices(esk5_0,esk7_0),k7_lattices(esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_99,negated_conjecture,
    ( r3_lattices(esk5_0,X1,k7_lattices(esk5_0,esk6_0))
    | ~ r1_lattices(esk5_0,X1,k7_lattices(esk5_0,esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_86]),c_0_32]),c_0_33]),c_0_34]),c_0_22])]),c_0_23])).

cnf(c_0_100,negated_conjecture,
    ( k2_lattices(esk5_0,X1,esk6_0) = esk6_0
    | ~ r1_lattices(esk5_0,esk6_0,k2_lattices(esk5_0,X1,esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_52])])).

cnf(c_0_101,negated_conjecture,
    ( r1_lattices(esk5_0,esk6_0,k2_lattices(esk5_0,X1,esk6_0))
    | ~ r1_lattices(esk5_0,esk6_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_52])])).

cnf(c_0_102,plain,
    ( r1_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,X3) != X2
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_103,negated_conjecture,
    ( r1_lattices(esk5_0,esk6_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_95]),c_0_52])])).

cnf(c_0_104,negated_conjecture,
    ( r1_lattices(esk5_0,X1,k7_lattices(esk5_0,esk6_0))
    | k1_lattices(esk5_0,X1,k7_lattices(esk5_0,esk6_0)) != k7_lattices(esk5_0,esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ l2_lattices(esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_86]),c_0_23])).

cnf(c_0_105,negated_conjecture,
    ( k1_lattices(esk5_0,k7_lattices(esk5_0,esk7_0),k7_lattices(esk5_0,esk6_0)) = k7_lattices(esk5_0,k4_lattices(esk5_0,esk7_0,esk6_0))
    | ~ l1_lattices(esk5_0)
    | ~ l2_lattices(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_31])])).

cnf(c_0_106,negated_conjecture,
    ( ~ r1_lattices(esk5_0,k7_lattices(esk5_0,esk7_0),k7_lattices(esk5_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_31])])).

cnf(c_0_107,negated_conjecture,
    ( k2_lattices(esk5_0,X1,esk6_0) = esk6_0
    | ~ r1_lattices(esk5_0,esk6_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_100,c_0_101])).

cnf(c_0_108,negated_conjecture,
    ( r1_lattices(esk5_0,X1,esk7_0)
    | k2_lattices(esk5_0,X1,esk7_0) != X1
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_21]),c_0_32]),c_0_33]),c_0_22])]),c_0_23])).

cnf(c_0_109,negated_conjecture,
    ( k2_lattices(esk5_0,esk6_0,esk7_0) = esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_103]),c_0_52])])).

cnf(c_0_110,negated_conjecture,
    ( k7_lattices(esk5_0,k4_lattices(esk5_0,esk7_0,esk6_0)) != k7_lattices(esk5_0,esk6_0)
    | ~ l1_lattices(esk5_0)
    | ~ l2_lattices(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_105]),c_0_31])]),c_0_106])).

cnf(c_0_111,negated_conjecture,
    ( k4_lattices(esk5_0,X1,esk6_0) = k2_lattices(esk5_0,X1,esk6_0)
    | ~ l1_lattices(esk5_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_52]),c_0_34])]),c_0_23])).

cnf(c_0_112,negated_conjecture,
    ( k2_lattices(esk5_0,esk7_0,esk6_0) = esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_108]),c_0_21]),c_0_109]),c_0_52])])).

cnf(c_0_113,negated_conjecture,
    ( ~ l1_lattices(esk5_0)
    | ~ l2_lattices(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_111]),c_0_112]),c_0_21])])).

cnf(c_0_114,negated_conjecture,
    ( ~ l2_lattices(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_61]),c_0_22])])).

cnf(c_0_115,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_70]),c_0_22])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:57:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.47/0.70  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.47/0.70  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.47/0.70  #
% 0.47/0.70  # Preprocessing time       : 0.047 s
% 0.47/0.70  # Presaturation interreduction done
% 0.47/0.70  
% 0.47/0.70  # Proof found!
% 0.47/0.70  # SZS status Theorem
% 0.47/0.70  # SZS output start CNFRefutation
% 0.47/0.70  fof(t53_lattices, conjecture, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v17_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r3_lattices(X1,X2,X3)=>r3_lattices(X1,k7_lattices(X1,X3),k7_lattices(X1,X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_lattices)).
% 0.47/0.70  fof(dt_k7_lattices, axiom, ![X1, X2]:(((~(v2_struct_0(X1))&l3_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>m1_subset_1(k7_lattices(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_lattices)).
% 0.47/0.70  fof(cc1_lattices, axiom, ![X1]:(l3_lattices(X1)=>((~(v2_struct_0(X1))&v10_lattices(X1))=>((((((~(v2_struct_0(X1))&v4_lattices(X1))&v5_lattices(X1))&v6_lattices(X1))&v7_lattices(X1))&v8_lattices(X1))&v9_lattices(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattices)).
% 0.47/0.70  fof(redefinition_r3_lattices, axiom, ![X1, X2, X3]:(((((((~(v2_struct_0(X1))&v6_lattices(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>(r3_lattices(X1,X2,X3)<=>r1_lattices(X1,X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 0.47/0.70  fof(reflexivity_r3_lattices, axiom, ![X1, X2, X3]:(((((((~(v2_struct_0(X1))&v6_lattices(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>r3_lattices(X1,X2,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r3_lattices)).
% 0.47/0.70  fof(t21_lattices, axiom, ![X1]:((((~(v2_struct_0(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_lattices(X1,X2,X3)<=>k2_lattices(X1,X2,X3)=X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_lattices)).
% 0.47/0.70  fof(d8_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>(v8_lattices(X1)<=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>k1_lattices(X1,k2_lattices(X1,X2,X3),X3)=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_lattices)).
% 0.47/0.70  fof(redefinition_k3_lattices, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v4_lattices(X1))&l2_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k3_lattices(X1,X2,X3)=k1_lattices(X1,X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_lattices)).
% 0.47/0.70  fof(t50_lattices, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v17_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>k7_lattices(X1,k4_lattices(X1,X2,X3))=k3_lattices(X1,k7_lattices(X1,X2),k7_lattices(X1,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_lattices)).
% 0.47/0.70  fof(dt_k2_lattices, axiom, ![X1, X2, X3]:((((~(v2_struct_0(X1))&l1_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>m1_subset_1(k2_lattices(X1,X2,X3),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_lattices)).
% 0.47/0.70  fof(dt_l3_lattices, axiom, ![X1]:(l3_lattices(X1)=>(l1_lattices(X1)&l2_lattices(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l3_lattices)).
% 0.47/0.70  fof(d3_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l2_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_lattices(X1,X2,X3)<=>k1_lattices(X1,X2,X3)=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_lattices)).
% 0.47/0.70  fof(t26_lattices, axiom, ![X1]:(((~(v2_struct_0(X1))&v4_lattices(X1))&l2_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>((r1_lattices(X1,X2,X3)&r1_lattices(X1,X3,X2))=>X2=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_lattices)).
% 0.47/0.70  fof(redefinition_k4_lattices, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v6_lattices(X1))&l1_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k4_lattices(X1,X2,X3)=k2_lattices(X1,X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_lattices)).
% 0.47/0.70  fof(t27_lattices, axiom, ![X1]:(((((~(v2_struct_0(X1))&v7_lattices(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r1_lattices(X1,X2,X3)=>r1_lattices(X1,k2_lattices(X1,X2,X4),k2_lattices(X1,X3,X4))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_lattices)).
% 0.47/0.70  fof(c_0_15, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v17_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r3_lattices(X1,X2,X3)=>r3_lattices(X1,k7_lattices(X1,X3),k7_lattices(X1,X2))))))), inference(assume_negation,[status(cth)],[t53_lattices])).
% 0.47/0.70  fof(c_0_16, plain, ![X22, X23]:(v2_struct_0(X22)|~l3_lattices(X22)|~m1_subset_1(X23,u1_struct_0(X22))|m1_subset_1(k7_lattices(X22,X23),u1_struct_0(X22))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_lattices])])])).
% 0.47/0.70  fof(c_0_17, negated_conjecture, ((((~v2_struct_0(esk5_0)&v10_lattices(esk5_0))&v17_lattices(esk5_0))&l3_lattices(esk5_0))&(m1_subset_1(esk6_0,u1_struct_0(esk5_0))&(m1_subset_1(esk7_0,u1_struct_0(esk5_0))&(r3_lattices(esk5_0,esk6_0,esk7_0)&~r3_lattices(esk5_0,k7_lattices(esk5_0,esk7_0),k7_lattices(esk5_0,esk6_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).
% 0.47/0.70  fof(c_0_18, plain, ![X5]:(((((((~v2_struct_0(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5))&(v4_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v5_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v6_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v7_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v8_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v9_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).
% 0.47/0.70  fof(c_0_19, plain, ![X31, X32, X33]:((~r3_lattices(X31,X32,X33)|r1_lattices(X31,X32,X33)|(v2_struct_0(X31)|~v6_lattices(X31)|~v8_lattices(X31)|~v9_lattices(X31)|~l3_lattices(X31)|~m1_subset_1(X32,u1_struct_0(X31))|~m1_subset_1(X33,u1_struct_0(X31))))&(~r1_lattices(X31,X32,X33)|r3_lattices(X31,X32,X33)|(v2_struct_0(X31)|~v6_lattices(X31)|~v8_lattices(X31)|~v9_lattices(X31)|~l3_lattices(X31)|~m1_subset_1(X32,u1_struct_0(X31))|~m1_subset_1(X33,u1_struct_0(X31))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).
% 0.47/0.70  cnf(c_0_20, plain, (v2_struct_0(X1)|m1_subset_1(k7_lattices(X1,X2),u1_struct_0(X1))|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.47/0.70  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk7_0,u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.47/0.70  cnf(c_0_22, negated_conjecture, (l3_lattices(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.47/0.70  cnf(c_0_23, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.47/0.70  cnf(c_0_24, plain, (v9_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.47/0.70  cnf(c_0_25, negated_conjecture, (v10_lattices(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.47/0.70  cnf(c_0_26, plain, (v8_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.47/0.70  cnf(c_0_27, plain, (v6_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.47/0.70  fof(c_0_28, plain, ![X34, X35, X36]:(v2_struct_0(X34)|~v6_lattices(X34)|~v8_lattices(X34)|~v9_lattices(X34)|~l3_lattices(X34)|~m1_subset_1(X35,u1_struct_0(X34))|~m1_subset_1(X36,u1_struct_0(X34))|r3_lattices(X34,X35,X35)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[reflexivity_r3_lattices])])])).
% 0.47/0.70  fof(c_0_29, plain, ![X37, X38, X39]:((~r1_lattices(X37,X38,X39)|k2_lattices(X37,X38,X39)=X38|~m1_subset_1(X39,u1_struct_0(X37))|~m1_subset_1(X38,u1_struct_0(X37))|(v2_struct_0(X37)|~v8_lattices(X37)|~v9_lattices(X37)|~l3_lattices(X37)))&(k2_lattices(X37,X38,X39)!=X38|r1_lattices(X37,X38,X39)|~m1_subset_1(X39,u1_struct_0(X37))|~m1_subset_1(X38,u1_struct_0(X37))|(v2_struct_0(X37)|~v8_lattices(X37)|~v9_lattices(X37)|~l3_lattices(X37)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t21_lattices])])])])])).
% 0.47/0.70  cnf(c_0_30, plain, (r1_lattices(X1,X2,X3)|v2_struct_0(X1)|~r3_lattices(X1,X2,X3)|~v6_lattices(X1)|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.47/0.70  cnf(c_0_31, negated_conjecture, (m1_subset_1(k7_lattices(esk5_0,esk7_0),u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22])]), c_0_23])).
% 0.47/0.70  cnf(c_0_32, negated_conjecture, (v9_lattices(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_22])]), c_0_23])).
% 0.47/0.70  cnf(c_0_33, negated_conjecture, (v8_lattices(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_25]), c_0_22])]), c_0_23])).
% 0.47/0.70  cnf(c_0_34, negated_conjecture, (v6_lattices(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_25]), c_0_22])]), c_0_23])).
% 0.47/0.70  cnf(c_0_35, plain, (v2_struct_0(X1)|r3_lattices(X1,X2,X2)|~v6_lattices(X1)|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.47/0.70  fof(c_0_36, plain, ![X9, X10, X11]:((~v8_lattices(X9)|(~m1_subset_1(X10,u1_struct_0(X9))|(~m1_subset_1(X11,u1_struct_0(X9))|k1_lattices(X9,k2_lattices(X9,X10,X11),X11)=X11))|(v2_struct_0(X9)|~l3_lattices(X9)))&((m1_subset_1(esk1_1(X9),u1_struct_0(X9))|v8_lattices(X9)|(v2_struct_0(X9)|~l3_lattices(X9)))&((m1_subset_1(esk2_1(X9),u1_struct_0(X9))|v8_lattices(X9)|(v2_struct_0(X9)|~l3_lattices(X9)))&(k1_lattices(X9,k2_lattices(X9,esk1_1(X9),esk2_1(X9)),esk2_1(X9))!=esk2_1(X9)|v8_lattices(X9)|(v2_struct_0(X9)|~l3_lattices(X9)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d8_lattices])])])])])])).
% 0.47/0.70  cnf(c_0_37, plain, (k2_lattices(X1,X2,X3)=X2|v2_struct_0(X1)|~r1_lattices(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.47/0.70  cnf(c_0_38, negated_conjecture, (r1_lattices(esk5_0,X1,k7_lattices(esk5_0,esk7_0))|~r3_lattices(esk5_0,X1,k7_lattices(esk5_0,esk7_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32]), c_0_33]), c_0_34]), c_0_22])]), c_0_23])).
% 0.47/0.70  cnf(c_0_39, negated_conjecture, (r3_lattices(esk5_0,X1,X1)|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_21]), c_0_32]), c_0_33]), c_0_34]), c_0_22])]), c_0_23])).
% 0.47/0.70  fof(c_0_40, plain, ![X25, X26, X27]:(v2_struct_0(X25)|~v4_lattices(X25)|~l2_lattices(X25)|~m1_subset_1(X26,u1_struct_0(X25))|~m1_subset_1(X27,u1_struct_0(X25))|k3_lattices(X25,X26,X27)=k1_lattices(X25,X26,X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_lattices])])])).
% 0.47/0.70  cnf(c_0_41, plain, (v4_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.47/0.70  fof(c_0_42, plain, ![X47, X48, X49]:(v2_struct_0(X47)|~v10_lattices(X47)|~v17_lattices(X47)|~l3_lattices(X47)|(~m1_subset_1(X48,u1_struct_0(X47))|(~m1_subset_1(X49,u1_struct_0(X47))|k7_lattices(X47,k4_lattices(X47,X48,X49))=k3_lattices(X47,k7_lattices(X47,X48),k7_lattices(X47,X49))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t50_lattices])])])])).
% 0.47/0.70  fof(c_0_43, plain, ![X19, X20, X21]:(v2_struct_0(X19)|~l1_lattices(X19)|~m1_subset_1(X20,u1_struct_0(X19))|~m1_subset_1(X21,u1_struct_0(X19))|m1_subset_1(k2_lattices(X19,X20,X21),u1_struct_0(X19))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k2_lattices])])])).
% 0.47/0.70  cnf(c_0_44, plain, (k1_lattices(X1,k2_lattices(X1,X2,X3),X3)=X3|v2_struct_0(X1)|~v8_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.47/0.70  cnf(c_0_45, negated_conjecture, (k2_lattices(esk5_0,X1,k7_lattices(esk5_0,esk7_0))=X1|~r1_lattices(esk5_0,X1,k7_lattices(esk5_0,esk7_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_31]), c_0_32]), c_0_33]), c_0_22])]), c_0_23])).
% 0.47/0.70  cnf(c_0_46, negated_conjecture, (r1_lattices(esk5_0,k7_lattices(esk5_0,esk7_0),k7_lattices(esk5_0,esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_31])])).
% 0.47/0.70  cnf(c_0_47, plain, (v2_struct_0(X1)|k3_lattices(X1,X2,X3)=k1_lattices(X1,X2,X3)|~v4_lattices(X1)|~l2_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.47/0.70  cnf(c_0_48, negated_conjecture, (v4_lattices(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_25]), c_0_22])]), c_0_23])).
% 0.47/0.70  cnf(c_0_49, plain, (v2_struct_0(X1)|k7_lattices(X1,k4_lattices(X1,X2,X3))=k3_lattices(X1,k7_lattices(X1,X2),k7_lattices(X1,X3))|~v10_lattices(X1)|~v17_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.47/0.70  cnf(c_0_50, negated_conjecture, (v17_lattices(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.47/0.70  cnf(c_0_51, plain, (v2_struct_0(X1)|m1_subset_1(k2_lattices(X1,X2,X3),u1_struct_0(X1))|~l1_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.47/0.70  cnf(c_0_52, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.47/0.70  fof(c_0_53, plain, ![X24]:((l1_lattices(X24)|~l3_lattices(X24))&(l2_lattices(X24)|~l3_lattices(X24))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).
% 0.47/0.70  fof(c_0_54, plain, ![X6, X7, X8]:((~r1_lattices(X6,X7,X8)|k1_lattices(X6,X7,X8)=X8|~m1_subset_1(X8,u1_struct_0(X6))|~m1_subset_1(X7,u1_struct_0(X6))|(v2_struct_0(X6)|~l2_lattices(X6)))&(k1_lattices(X6,X7,X8)!=X8|r1_lattices(X6,X7,X8)|~m1_subset_1(X8,u1_struct_0(X6))|~m1_subset_1(X7,u1_struct_0(X6))|(v2_struct_0(X6)|~l2_lattices(X6)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d3_lattices])])])])])).
% 0.47/0.70  cnf(c_0_55, negated_conjecture, (k1_lattices(esk5_0,k2_lattices(esk5_0,X1,k7_lattices(esk5_0,esk7_0)),k7_lattices(esk5_0,esk7_0))=k7_lattices(esk5_0,esk7_0)|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_31]), c_0_33]), c_0_22])]), c_0_23])).
% 0.47/0.70  cnf(c_0_56, negated_conjecture, (k2_lattices(esk5_0,k7_lattices(esk5_0,esk7_0),k7_lattices(esk5_0,esk7_0))=k7_lattices(esk5_0,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_31])])).
% 0.47/0.70  cnf(c_0_57, negated_conjecture, (k3_lattices(esk5_0,X1,k7_lattices(esk5_0,esk7_0))=k1_lattices(esk5_0,X1,k7_lattices(esk5_0,esk7_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))|~l2_lattices(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_31]), c_0_48])]), c_0_23])).
% 0.47/0.70  cnf(c_0_58, negated_conjecture, (k3_lattices(esk5_0,k7_lattices(esk5_0,X1),k7_lattices(esk5_0,esk7_0))=k7_lattices(esk5_0,k4_lattices(esk5_0,X1,esk7_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_21]), c_0_50]), c_0_25]), c_0_22])]), c_0_23])).
% 0.47/0.70  fof(c_0_59, plain, ![X40, X41, X42]:(v2_struct_0(X40)|~v4_lattices(X40)|~l2_lattices(X40)|(~m1_subset_1(X41,u1_struct_0(X40))|(~m1_subset_1(X42,u1_struct_0(X40))|(~r1_lattices(X40,X41,X42)|~r1_lattices(X40,X42,X41)|X41=X42)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t26_lattices])])])])).
% 0.47/0.70  cnf(c_0_60, negated_conjecture, (m1_subset_1(k2_lattices(esk5_0,X1,esk6_0),u1_struct_0(esk5_0))|~l1_lattices(esk5_0)|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_23])).
% 0.47/0.70  cnf(c_0_61, plain, (l1_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.47/0.70  cnf(c_0_62, plain, (r1_lattices(X1,X2,X3)|v2_struct_0(X1)|k1_lattices(X1,X2,X3)!=X3|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l2_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.47/0.70  cnf(c_0_63, negated_conjecture, (k1_lattices(esk5_0,k7_lattices(esk5_0,esk7_0),k7_lattices(esk5_0,esk7_0))=k7_lattices(esk5_0,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_31])])).
% 0.47/0.70  cnf(c_0_64, negated_conjecture, (k1_lattices(esk5_0,k7_lattices(esk5_0,X1),k7_lattices(esk5_0,esk7_0))=k7_lattices(esk5_0,k4_lattices(esk5_0,X1,esk7_0))|~m1_subset_1(k7_lattices(esk5_0,X1),u1_struct_0(esk5_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))|~l2_lattices(esk5_0)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.47/0.70  fof(c_0_65, plain, ![X28, X29, X30]:(v2_struct_0(X28)|~v6_lattices(X28)|~l1_lattices(X28)|~m1_subset_1(X29,u1_struct_0(X28))|~m1_subset_1(X30,u1_struct_0(X28))|k4_lattices(X28,X29,X30)=k2_lattices(X28,X29,X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k4_lattices])])])).
% 0.47/0.70  cnf(c_0_66, negated_conjecture, (r1_lattices(esk5_0,X1,esk7_0)|~r3_lattices(esk5_0,X1,esk7_0)|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_21]), c_0_32]), c_0_33]), c_0_34]), c_0_22])]), c_0_23])).
% 0.47/0.70  cnf(c_0_67, plain, (v2_struct_0(X1)|X2=X3|~v4_lattices(X1)|~l2_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~r1_lattices(X1,X2,X3)|~r1_lattices(X1,X3,X2)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.47/0.70  cnf(c_0_68, negated_conjecture, (m1_subset_1(k2_lattices(esk5_0,X1,esk6_0),u1_struct_0(esk5_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_22])])).
% 0.47/0.70  cnf(c_0_69, negated_conjecture, (r1_lattices(esk5_0,X1,esk6_0)|k1_lattices(esk5_0,X1,esk6_0)!=esk6_0|~m1_subset_1(X1,u1_struct_0(esk5_0))|~l2_lattices(esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_52]), c_0_23])).
% 0.47/0.70  cnf(c_0_70, plain, (l2_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.47/0.70  fof(c_0_71, plain, ![X43, X44, X45, X46]:(v2_struct_0(X43)|~v7_lattices(X43)|~v8_lattices(X43)|~v9_lattices(X43)|~l3_lattices(X43)|(~m1_subset_1(X44,u1_struct_0(X43))|(~m1_subset_1(X45,u1_struct_0(X43))|(~m1_subset_1(X46,u1_struct_0(X43))|(~r1_lattices(X43,X44,X45)|r1_lattices(X43,k2_lattices(X43,X44,X46),k2_lattices(X43,X45,X46))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t27_lattices])])])])).
% 0.47/0.70  cnf(c_0_72, plain, (v7_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.47/0.70  cnf(c_0_73, negated_conjecture, (r1_lattices(esk5_0,X1,esk6_0)|~r3_lattices(esk5_0,X1,esk6_0)|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_52]), c_0_32]), c_0_33]), c_0_34]), c_0_22])]), c_0_23])).
% 0.47/0.70  cnf(c_0_74, negated_conjecture, (k3_lattices(esk5_0,k7_lattices(esk5_0,X1),k7_lattices(esk5_0,esk6_0))=k7_lattices(esk5_0,k4_lattices(esk5_0,X1,esk6_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_52]), c_0_50]), c_0_25]), c_0_22])]), c_0_23])).
% 0.47/0.70  cnf(c_0_75, negated_conjecture, (k7_lattices(esk5_0,k4_lattices(esk5_0,esk7_0,esk7_0))=k7_lattices(esk5_0,esk7_0)|~l2_lattices(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_31]), c_0_21])])).
% 0.47/0.70  cnf(c_0_76, plain, (v2_struct_0(X1)|k4_lattices(X1,X2,X3)=k2_lattices(X1,X2,X3)|~v6_lattices(X1)|~l1_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.47/0.70  cnf(c_0_77, negated_conjecture, (k2_lattices(esk5_0,X1,esk7_0)=X1|~r1_lattices(esk5_0,X1,esk7_0)|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_21]), c_0_32]), c_0_33]), c_0_22])]), c_0_23])).
% 0.47/0.70  cnf(c_0_78, negated_conjecture, (r1_lattices(esk5_0,esk7_0,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_39]), c_0_21])])).
% 0.47/0.70  cnf(c_0_79, negated_conjecture, (X1=k2_lattices(esk5_0,X2,esk6_0)|~r1_lattices(esk5_0,k2_lattices(esk5_0,X2,esk6_0),X1)|~r1_lattices(esk5_0,X1,k2_lattices(esk5_0,X2,esk6_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))|~m1_subset_1(X2,u1_struct_0(esk5_0))|~l2_lattices(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_48])]), c_0_23])).
% 0.47/0.70  cnf(c_0_80, negated_conjecture, (r1_lattices(esk5_0,X1,esk6_0)|k1_lattices(esk5_0,X1,esk6_0)!=esk6_0|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_22])])).
% 0.47/0.70  cnf(c_0_81, negated_conjecture, (k1_lattices(esk5_0,k2_lattices(esk5_0,X1,esk6_0),esk6_0)=esk6_0|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_52]), c_0_33]), c_0_22])]), c_0_23])).
% 0.47/0.70  cnf(c_0_82, plain, (v2_struct_0(X1)|r1_lattices(X1,k2_lattices(X1,X2,X4),k2_lattices(X1,X3,X4))|~v7_lattices(X1)|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~r1_lattices(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.47/0.70  cnf(c_0_83, negated_conjecture, (v7_lattices(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_25]), c_0_22])]), c_0_23])).
% 0.47/0.70  cnf(c_0_84, negated_conjecture, (k2_lattices(esk5_0,X1,esk6_0)=X1|~r1_lattices(esk5_0,X1,esk6_0)|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_52]), c_0_32]), c_0_33]), c_0_22])]), c_0_23])).
% 0.47/0.70  cnf(c_0_85, negated_conjecture, (r1_lattices(esk5_0,esk6_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_39]), c_0_52])])).
% 0.47/0.70  cnf(c_0_86, negated_conjecture, (m1_subset_1(k7_lattices(esk5_0,esk6_0),u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_52]), c_0_22])]), c_0_23])).
% 0.47/0.70  cnf(c_0_87, negated_conjecture, (k7_lattices(esk5_0,k4_lattices(esk5_0,k4_lattices(esk5_0,esk7_0,esk7_0),esk6_0))=k3_lattices(esk5_0,k7_lattices(esk5_0,esk7_0),k7_lattices(esk5_0,esk6_0))|~m1_subset_1(k4_lattices(esk5_0,esk7_0,esk7_0),u1_struct_0(esk5_0))|~l2_lattices(esk5_0)), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 0.47/0.70  cnf(c_0_88, negated_conjecture, (k4_lattices(esk5_0,X1,esk7_0)=k2_lattices(esk5_0,X1,esk7_0)|~l1_lattices(esk5_0)|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_21]), c_0_34])]), c_0_23])).
% 0.47/0.70  cnf(c_0_89, negated_conjecture, (k2_lattices(esk5_0,esk7_0,esk7_0)=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_21])])).
% 0.47/0.70  cnf(c_0_90, plain, (r3_lattices(X1,X2,X3)|v2_struct_0(X1)|~r1_lattices(X1,X2,X3)|~v6_lattices(X1)|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.47/0.70  cnf(c_0_91, negated_conjecture, (X1=k2_lattices(esk5_0,X2,esk6_0)|~r1_lattices(esk5_0,k2_lattices(esk5_0,X2,esk6_0),X1)|~r1_lattices(esk5_0,X1,k2_lattices(esk5_0,X2,esk6_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))|~m1_subset_1(X2,u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_70]), c_0_22])])).
% 0.47/0.70  cnf(c_0_92, negated_conjecture, (r1_lattices(esk5_0,k2_lattices(esk5_0,X1,esk6_0),esk6_0)|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_68])).
% 0.47/0.70  cnf(c_0_93, negated_conjecture, (r1_lattices(esk5_0,k2_lattices(esk5_0,X1,esk6_0),k2_lattices(esk5_0,X2,esk6_0))|~r1_lattices(esk5_0,X1,X2)|~m1_subset_1(X2,u1_struct_0(esk5_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_52]), c_0_32]), c_0_33]), c_0_83]), c_0_22])]), c_0_23])).
% 0.47/0.70  cnf(c_0_94, negated_conjecture, (k2_lattices(esk5_0,esk6_0,esk6_0)=esk6_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_52])])).
% 0.47/0.70  cnf(c_0_95, negated_conjecture, (r3_lattices(esk5_0,esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.47/0.70  cnf(c_0_96, negated_conjecture, (k3_lattices(esk5_0,X1,k7_lattices(esk5_0,esk6_0))=k1_lattices(esk5_0,X1,k7_lattices(esk5_0,esk6_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))|~l2_lattices(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_86]), c_0_48])]), c_0_23])).
% 0.47/0.70  cnf(c_0_97, negated_conjecture, (k3_lattices(esk5_0,k7_lattices(esk5_0,esk7_0),k7_lattices(esk5_0,esk6_0))=k7_lattices(esk5_0,k4_lattices(esk5_0,esk7_0,esk6_0))|~l1_lattices(esk5_0)|~l2_lattices(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_89]), c_0_89]), c_0_21]), c_0_21])])).
% 0.47/0.70  cnf(c_0_98, negated_conjecture, (~r3_lattices(esk5_0,k7_lattices(esk5_0,esk7_0),k7_lattices(esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.47/0.70  cnf(c_0_99, negated_conjecture, (r3_lattices(esk5_0,X1,k7_lattices(esk5_0,esk6_0))|~r1_lattices(esk5_0,X1,k7_lattices(esk5_0,esk6_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_86]), c_0_32]), c_0_33]), c_0_34]), c_0_22])]), c_0_23])).
% 0.47/0.70  cnf(c_0_100, negated_conjecture, (k2_lattices(esk5_0,X1,esk6_0)=esk6_0|~r1_lattices(esk5_0,esk6_0,k2_lattices(esk5_0,X1,esk6_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_52])])).
% 0.47/0.70  cnf(c_0_101, negated_conjecture, (r1_lattices(esk5_0,esk6_0,k2_lattices(esk5_0,X1,esk6_0))|~r1_lattices(esk5_0,esk6_0,X1)|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_94]), c_0_52])])).
% 0.47/0.70  cnf(c_0_102, plain, (r1_lattices(X1,X2,X3)|v2_struct_0(X1)|k2_lattices(X1,X2,X3)!=X2|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.47/0.70  cnf(c_0_103, negated_conjecture, (r1_lattices(esk5_0,esk6_0,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_95]), c_0_52])])).
% 0.47/0.70  cnf(c_0_104, negated_conjecture, (r1_lattices(esk5_0,X1,k7_lattices(esk5_0,esk6_0))|k1_lattices(esk5_0,X1,k7_lattices(esk5_0,esk6_0))!=k7_lattices(esk5_0,esk6_0)|~m1_subset_1(X1,u1_struct_0(esk5_0))|~l2_lattices(esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_86]), c_0_23])).
% 0.47/0.70  cnf(c_0_105, negated_conjecture, (k1_lattices(esk5_0,k7_lattices(esk5_0,esk7_0),k7_lattices(esk5_0,esk6_0))=k7_lattices(esk5_0,k4_lattices(esk5_0,esk7_0,esk6_0))|~l1_lattices(esk5_0)|~l2_lattices(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_97]), c_0_31])])).
% 0.47/0.70  cnf(c_0_106, negated_conjecture, (~r1_lattices(esk5_0,k7_lattices(esk5_0,esk7_0),k7_lattices(esk5_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_99]), c_0_31])])).
% 0.47/0.70  cnf(c_0_107, negated_conjecture, (k2_lattices(esk5_0,X1,esk6_0)=esk6_0|~r1_lattices(esk5_0,esk6_0,X1)|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_100, c_0_101])).
% 0.47/0.70  cnf(c_0_108, negated_conjecture, (r1_lattices(esk5_0,X1,esk7_0)|k2_lattices(esk5_0,X1,esk7_0)!=X1|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_21]), c_0_32]), c_0_33]), c_0_22])]), c_0_23])).
% 0.47/0.70  cnf(c_0_109, negated_conjecture, (k2_lattices(esk5_0,esk6_0,esk7_0)=esk6_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_103]), c_0_52])])).
% 0.47/0.70  cnf(c_0_110, negated_conjecture, (k7_lattices(esk5_0,k4_lattices(esk5_0,esk7_0,esk6_0))!=k7_lattices(esk5_0,esk6_0)|~l1_lattices(esk5_0)|~l2_lattices(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_105]), c_0_31])]), c_0_106])).
% 0.47/0.70  cnf(c_0_111, negated_conjecture, (k4_lattices(esk5_0,X1,esk6_0)=k2_lattices(esk5_0,X1,esk6_0)|~l1_lattices(esk5_0)|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_52]), c_0_34])]), c_0_23])).
% 0.47/0.70  cnf(c_0_112, negated_conjecture, (k2_lattices(esk5_0,esk7_0,esk6_0)=esk6_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_108]), c_0_21]), c_0_109]), c_0_52])])).
% 0.47/0.70  cnf(c_0_113, negated_conjecture, (~l1_lattices(esk5_0)|~l2_lattices(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_111]), c_0_112]), c_0_21])])).
% 0.47/0.70  cnf(c_0_114, negated_conjecture, (~l2_lattices(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_61]), c_0_22])])).
% 0.47/0.70  cnf(c_0_115, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_70]), c_0_22])]), ['proof']).
% 0.47/0.70  # SZS output end CNFRefutation
% 0.47/0.70  # Proof object total steps             : 116
% 0.47/0.70  # Proof object clause steps            : 85
% 0.47/0.70  # Proof object formula steps           : 31
% 0.47/0.70  # Proof object conjectures             : 67
% 0.47/0.70  # Proof object clause conjectures      : 64
% 0.47/0.70  # Proof object formula conjectures     : 3
% 0.47/0.70  # Proof object initial clauses used    : 29
% 0.47/0.70  # Proof object initial formulas used   : 15
% 0.47/0.70  # Proof object generating inferences   : 56
% 0.47/0.70  # Proof object simplifying inferences  : 168
% 0.47/0.70  # Training examples: 0 positive, 0 negative
% 0.47/0.70  # Parsed axioms                        : 16
% 0.47/0.70  # Removed by relevancy pruning/SinE    : 0
% 0.47/0.70  # Initial clauses                      : 39
% 0.47/0.70  # Removed in clause preprocessing      : 1
% 0.47/0.70  # Initial clauses in saturation        : 38
% 0.47/0.70  # Processed clauses                    : 2494
% 0.47/0.70  # ...of these trivial                  : 2
% 0.47/0.70  # ...subsumed                          : 1553
% 0.47/0.70  # ...remaining for further processing  : 939
% 0.47/0.70  # Other redundant clauses eliminated   : 0
% 0.47/0.70  # Clauses deleted for lack of memory   : 0
% 0.47/0.70  # Backward-subsumed                    : 58
% 0.47/0.70  # Backward-rewritten                   : 17
% 0.47/0.70  # Generated clauses                    : 6256
% 0.47/0.70  # ...of the previous two non-trivial   : 4552
% 0.47/0.70  # Contextual simplify-reflections      : 48
% 0.47/0.70  # Paramodulations                      : 6256
% 0.47/0.70  # Factorizations                       : 0
% 0.47/0.70  # Equation resolutions                 : 0
% 0.47/0.70  # Propositional unsat checks           : 0
% 0.47/0.70  #    Propositional check models        : 0
% 0.47/0.70  #    Propositional check unsatisfiable : 0
% 0.47/0.70  #    Propositional clauses             : 0
% 0.47/0.70  #    Propositional clauses after purity: 0
% 0.47/0.70  #    Propositional unsat core size     : 0
% 0.47/0.70  #    Propositional preprocessing time  : 0.000
% 0.47/0.70  #    Propositional encoding time       : 0.000
% 0.47/0.70  #    Propositional solver time         : 0.000
% 0.47/0.70  #    Success case prop preproc time    : 0.000
% 0.47/0.70  #    Success case prop encoding time   : 0.000
% 0.47/0.70  #    Success case prop solver time     : 0.000
% 0.47/0.70  # Current number of processed clauses  : 826
% 0.47/0.70  #    Positive orientable unit clauses  : 90
% 0.47/0.70  #    Positive unorientable unit clauses: 0
% 0.47/0.70  #    Negative unit clauses             : 5
% 0.47/0.70  #    Non-unit-clauses                  : 731
% 0.47/0.70  # Current number of unprocessed clauses: 2101
% 0.47/0.70  # ...number of literals in the above   : 9719
% 0.47/0.70  # Current number of archived formulas  : 0
% 0.47/0.70  # Current number of archived clauses   : 113
% 0.47/0.70  # Clause-clause subsumption calls (NU) : 68049
% 0.47/0.70  # Rec. Clause-clause subsumption calls : 35844
% 0.47/0.70  # Non-unit clause-clause subsumptions  : 1654
% 0.47/0.70  # Unit Clause-clause subsumption calls : 915
% 0.47/0.70  # Rewrite failures with RHS unbound    : 0
% 0.47/0.70  # BW rewrite match attempts            : 1125
% 0.47/0.70  # BW rewrite match successes           : 1
% 0.47/0.70  # Condensation attempts                : 0
% 0.47/0.70  # Condensation successes               : 0
% 0.47/0.70  # Termbank termtop insertions          : 233573
% 0.47/0.70  
% 0.47/0.70  # -------------------------------------------------
% 0.47/0.70  # User time                : 0.354 s
% 0.47/0.70  # System time              : 0.005 s
% 0.47/0.70  # Total time               : 0.359 s
% 0.47/0.70  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
