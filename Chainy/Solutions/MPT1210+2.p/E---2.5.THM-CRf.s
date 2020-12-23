%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1210+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:03 EST 2020

% Result     : Theorem 5.05s
% Output     : CNFRefutation 5.05s
% Verified   : 
% Statistics : Number of formulae       :   38 ( 148 expanded)
%              Number of clauses        :   23 (  50 expanded)
%              Number of leaves         :    7 (  37 expanded)
%              Depth                    :    7
%              Number of atoms          :  207 ( 764 expanded)
%              Number of equality atoms :   19 (  19 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   28 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t45_lattices,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v14_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => r3_lattices(X1,X2,k6_lattices(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_lattices)).

fof(d17_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l2_lattices(X1) )
     => ( v14_lattices(X1)
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ( X2 = k6_lattices(X1)
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => ( k1_lattices(X1,X2,X3) = X2
                    & k1_lattices(X1,X3,X2) = X2 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_lattices)).

fof(dt_k6_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l2_lattices(X1) )
     => m1_subset_1(k6_lattices(X1),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_lattices)).

fof(dt_l3_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( l1_lattices(X1)
        & l2_lattices(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_lattices)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_lattices)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v10_lattices(X1)
          & v14_lattices(X1)
          & l3_lattices(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => r3_lattices(X1,X2,k6_lattices(X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t45_lattices])).

fof(c_0_8,plain,(
    ! [X31,X32,X33] :
      ( ( k1_lattices(X31,X32,X33) = X32
        | ~ m1_subset_1(X33,u1_struct_0(X31))
        | X32 != k6_lattices(X31)
        | ~ m1_subset_1(X32,u1_struct_0(X31))
        | ~ v14_lattices(X31)
        | v2_struct_0(X31)
        | ~ l2_lattices(X31) )
      & ( k1_lattices(X31,X33,X32) = X32
        | ~ m1_subset_1(X33,u1_struct_0(X31))
        | X32 != k6_lattices(X31)
        | ~ m1_subset_1(X32,u1_struct_0(X31))
        | ~ v14_lattices(X31)
        | v2_struct_0(X31)
        | ~ l2_lattices(X31) )
      & ( m1_subset_1(esk3_2(X31,X32),u1_struct_0(X31))
        | X32 = k6_lattices(X31)
        | ~ m1_subset_1(X32,u1_struct_0(X31))
        | ~ v14_lattices(X31)
        | v2_struct_0(X31)
        | ~ l2_lattices(X31) )
      & ( k1_lattices(X31,X32,esk3_2(X31,X32)) != X32
        | k1_lattices(X31,esk3_2(X31,X32),X32) != X32
        | X32 = k6_lattices(X31)
        | ~ m1_subset_1(X32,u1_struct_0(X31))
        | ~ v14_lattices(X31)
        | v2_struct_0(X31)
        | ~ l2_lattices(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_lattices])])])])])])).

fof(c_0_9,plain,(
    ! [X35] :
      ( v2_struct_0(X35)
      | ~ l2_lattices(X35)
      | m1_subset_1(k6_lattices(X35),u1_struct_0(X35)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_lattices])])])).

fof(c_0_10,plain,(
    ! [X197] :
      ( ( l1_lattices(X197)
        | ~ l3_lattices(X197) )
      & ( l2_lattices(X197)
        | ~ l3_lattices(X197) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).

fof(c_0_11,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v10_lattices(esk1_0)
    & v14_lattices(esk1_0)
    & l3_lattices(esk1_0)
    & m1_subset_1(esk2_0,u1_struct_0(esk1_0))
    & ~ r3_lattices(esk1_0,esk2_0,k6_lattices(esk1_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])).

cnf(c_0_12,plain,
    ( k1_lattices(X1,X2,X3) = X3
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | X3 != k6_lattices(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v14_lattices(X1)
    | ~ l2_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k6_lattices(X1),u1_struct_0(X1))
    | ~ l2_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( l2_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( l3_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_16,plain,(
    ! [X253,X254,X255] :
      ( ( ~ r1_lattices(X253,X254,X255)
        | k1_lattices(X253,X254,X255) = X255
        | ~ m1_subset_1(X255,u1_struct_0(X253))
        | ~ m1_subset_1(X254,u1_struct_0(X253))
        | v2_struct_0(X253)
        | ~ l2_lattices(X253) )
      & ( k1_lattices(X253,X254,X255) != X255
        | r1_lattices(X253,X254,X255)
        | ~ m1_subset_1(X255,u1_struct_0(X253))
        | ~ m1_subset_1(X254,u1_struct_0(X253))
        | v2_struct_0(X253)
        | ~ l2_lattices(X253) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d3_lattices])])])])])).

cnf(c_0_17,plain,
    ( k1_lattices(X1,X2,k6_lattices(X1)) = k6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v14_lattices(X1)
    | ~ l2_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_12]),c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,negated_conjecture,
    ( v14_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,negated_conjecture,
    ( l2_lattices(esk1_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_22,plain,(
    ! [X241] :
      ( ( ~ v2_struct_0(X241)
        | v2_struct_0(X241)
        | ~ v10_lattices(X241)
        | ~ l3_lattices(X241) )
      & ( v4_lattices(X241)
        | v2_struct_0(X241)
        | ~ v10_lattices(X241)
        | ~ l3_lattices(X241) )
      & ( v5_lattices(X241)
        | v2_struct_0(X241)
        | ~ v10_lattices(X241)
        | ~ l3_lattices(X241) )
      & ( v6_lattices(X241)
        | v2_struct_0(X241)
        | ~ v10_lattices(X241)
        | ~ l3_lattices(X241) )
      & ( v7_lattices(X241)
        | v2_struct_0(X241)
        | ~ v10_lattices(X241)
        | ~ l3_lattices(X241) )
      & ( v8_lattices(X241)
        | v2_struct_0(X241)
        | ~ v10_lattices(X241)
        | ~ l3_lattices(X241) )
      & ( v9_lattices(X241)
        | v2_struct_0(X241)
        | ~ v10_lattices(X241)
        | ~ l3_lattices(X241) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).

fof(c_0_23,plain,(
    ! [X23,X24,X25] :
      ( ( ~ r3_lattices(X23,X24,X25)
        | r1_lattices(X23,X24,X25)
        | v2_struct_0(X23)
        | ~ v6_lattices(X23)
        | ~ v8_lattices(X23)
        | ~ v9_lattices(X23)
        | ~ l3_lattices(X23)
        | ~ m1_subset_1(X24,u1_struct_0(X23))
        | ~ m1_subset_1(X25,u1_struct_0(X23)) )
      & ( ~ r1_lattices(X23,X24,X25)
        | r3_lattices(X23,X24,X25)
        | v2_struct_0(X23)
        | ~ v6_lattices(X23)
        | ~ v8_lattices(X23)
        | ~ v9_lattices(X23)
        | ~ l3_lattices(X23)
        | ~ m1_subset_1(X24,u1_struct_0(X23))
        | ~ m1_subset_1(X25,u1_struct_0(X23)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).

cnf(c_0_24,plain,
    ( r1_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | k1_lattices(X1,X2,X3) != X3
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,negated_conjecture,
    ( k1_lattices(esk1_0,esk2_0,k6_lattices(esk1_0)) = k6_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_20])]),c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(k6_lattices(esk1_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_20]),c_0_21])).

cnf(c_0_27,plain,
    ( v9_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( v10_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_29,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( r3_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,negated_conjecture,
    ( r1_lattices(esk1_0,esk2_0,k6_lattices(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_20]),c_0_26]),c_0_18])]),c_0_21])).

cnf(c_0_33,negated_conjecture,
    ( v9_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_15]),c_0_28])]),c_0_21])).

cnf(c_0_34,negated_conjecture,
    ( v8_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_15]),c_0_28])]),c_0_21])).

cnf(c_0_35,negated_conjecture,
    ( v6_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_15]),c_0_28])]),c_0_21])).

cnf(c_0_36,negated_conjecture,
    ( ~ r3_lattices(esk1_0,esk2_0,k6_lattices(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_37,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_34]),c_0_35]),c_0_15]),c_0_26]),c_0_18])]),c_0_36]),c_0_21]),
    [proof]).
%------------------------------------------------------------------------------
