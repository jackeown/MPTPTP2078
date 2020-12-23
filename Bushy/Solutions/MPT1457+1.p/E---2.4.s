%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : filter_1__t52_filter_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:10 EDT 2019

% Result     : Theorem 152.88s
% Output     : CNFRefutation 152.88s
% Verified   : 
% Statistics : Number of formulae       :  127 (2765 expanded)
%              Number of clauses        :   92 ( 873 expanded)
%              Number of leaves         :   17 ( 683 expanded)
%              Depth                    :   19
%              Number of atoms          :  502 (19507 expanded)
%              Number of equality atoms :  108 (6735 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   28 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t52_filter_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v17_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( k7_lattices(X1,k4_filter_0(X1,X2,X3)) = k4_lattices(X1,X2,k7_lattices(X1,X3))
                & k7_lattices(X1,k7_filter_0(X1,X2,X3)) = k3_lattices(X1,k4_lattices(X1,X2,k7_lattices(X1,X3)),k4_lattices(X1,k7_lattices(X1,X2),X3))
                & k7_lattices(X1,k7_filter_0(X1,X2,X3)) = k7_filter_0(X1,X2,k7_lattices(X1,X3))
                & k7_lattices(X1,k7_filter_0(X1,X2,X3)) = k7_filter_0(X1,k7_lattices(X1,X2),X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t52_filter_1.p',t52_filter_1)).

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
    file('/export/starexec/sandbox/benchmark/filter_1__t52_filter_1.p',t50_lattices)).

fof(commutativity_k4_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & l1_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k4_lattices(X1,X2,X3) = k4_lattices(X1,X3,X2) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t52_filter_1.p',commutativity_k4_lattices)).

fof(dt_k7_lattices,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => m1_subset_1(k7_lattices(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t52_filter_1.p',dt_k7_lattices)).

fof(dt_l3_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( l1_lattices(X1)
        & l2_lattices(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t52_filter_1.p',dt_l3_lattices)).

fof(t49_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v17_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => k7_lattices(X1,k7_lattices(X1,X2)) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t52_filter_1.p',t49_lattices)).

fof(t55_filter_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v17_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => k4_filter_0(X1,X2,X3) = k3_lattices(X1,k7_lattices(X1,X2),X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t52_filter_1.p',t55_filter_0)).

fof(commutativity_k3_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v4_lattices(X1)
        & l2_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k3_lattices(X1,X2,X3) = k3_lattices(X1,X3,X2) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t52_filter_1.p',commutativity_k3_lattices)).

fof(d11_filter_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => k7_filter_0(X1,X2,X3) = k4_lattices(X1,k4_filter_0(X1,X2,X3),k4_filter_0(X1,X3,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t52_filter_1.p',d11_filter_0)).

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
    file('/export/starexec/sandbox/benchmark/filter_1__t52_filter_1.p',cc1_lattices)).

fof(redefinition_k3_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v4_lattices(X1)
        & l2_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k3_lattices(X1,X2,X3) = k1_lattices(X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t52_filter_1.p',redefinition_k3_lattices)).

fof(t51_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v17_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => k7_lattices(X1,k3_lattices(X1,X2,X3)) = k4_lattices(X1,k7_lattices(X1,X2),k7_lattices(X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t52_filter_1.p',t51_lattices)).

fof(dt_k4_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & l1_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k4_lattices(X1,X2,X3),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t52_filter_1.p',dt_k4_lattices)).

fof(dt_k4_filter_0,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & l3_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k4_filter_0(X1,X2,X3),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t52_filter_1.p',dt_k4_filter_0)).

fof(dt_k1_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & l2_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k1_lattices(X1,X2,X3),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t52_filter_1.p',dt_k1_lattices)).

fof(t51_filter_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v17_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => k7_filter_0(X1,X2,X3) = k3_lattices(X1,k4_lattices(X1,X2,X3),k4_lattices(X1,k7_lattices(X1,X2),k7_lattices(X1,X3))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t52_filter_1.p',t51_filter_1)).

fof(dt_k7_filter_0,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & l3_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k7_filter_0(X1,X2,X3),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t52_filter_1.p',dt_k7_filter_0)).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v10_lattices(X1)
          & v17_lattices(X1)
          & l3_lattices(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ( k7_lattices(X1,k4_filter_0(X1,X2,X3)) = k4_lattices(X1,X2,k7_lattices(X1,X3))
                  & k7_lattices(X1,k7_filter_0(X1,X2,X3)) = k3_lattices(X1,k4_lattices(X1,X2,k7_lattices(X1,X3)),k4_lattices(X1,k7_lattices(X1,X2),X3))
                  & k7_lattices(X1,k7_filter_0(X1,X2,X3)) = k7_filter_0(X1,X2,k7_lattices(X1,X3))
                  & k7_lattices(X1,k7_filter_0(X1,X2,X3)) = k7_filter_0(X1,k7_lattices(X1,X2),X3) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t52_filter_1])).

fof(c_0_18,plain,(
    ! [X76,X77,X78] :
      ( v2_struct_0(X76)
      | ~ v10_lattices(X76)
      | ~ v17_lattices(X76)
      | ~ l3_lattices(X76)
      | ~ m1_subset_1(X77,u1_struct_0(X76))
      | ~ m1_subset_1(X78,u1_struct_0(X76))
      | k7_lattices(X76,k4_lattices(X76,X77,X78)) = k3_lattices(X76,k7_lattices(X76,X77),k7_lattices(X76,X78)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t50_lattices])])])])).

fof(c_0_19,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v10_lattices(esk1_0)
    & v17_lattices(esk1_0)
    & l3_lattices(esk1_0)
    & m1_subset_1(esk2_0,u1_struct_0(esk1_0))
    & m1_subset_1(esk3_0,u1_struct_0(esk1_0))
    & ( k7_lattices(esk1_0,k4_filter_0(esk1_0,esk2_0,esk3_0)) != k4_lattices(esk1_0,esk2_0,k7_lattices(esk1_0,esk3_0))
      | k7_lattices(esk1_0,k7_filter_0(esk1_0,esk2_0,esk3_0)) != k3_lattices(esk1_0,k4_lattices(esk1_0,esk2_0,k7_lattices(esk1_0,esk3_0)),k4_lattices(esk1_0,k7_lattices(esk1_0,esk2_0),esk3_0))
      | k7_lattices(esk1_0,k7_filter_0(esk1_0,esk2_0,esk3_0)) != k7_filter_0(esk1_0,esk2_0,k7_lattices(esk1_0,esk3_0))
      | k7_lattices(esk1_0,k7_filter_0(esk1_0,esk2_0,esk3_0)) != k7_filter_0(esk1_0,k7_lattices(esk1_0,esk2_0),esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_17])])])])).

fof(c_0_20,plain,(
    ! [X14,X15,X16] :
      ( v2_struct_0(X14)
      | ~ v6_lattices(X14)
      | ~ l1_lattices(X14)
      | ~ m1_subset_1(X15,u1_struct_0(X14))
      | ~ m1_subset_1(X16,u1_struct_0(X14))
      | k4_lattices(X14,X15,X16) = k4_lattices(X14,X16,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[commutativity_k4_lattices])])])).

fof(c_0_21,plain,(
    ! [X42,X43] :
      ( v2_struct_0(X42)
      | ~ l3_lattices(X42)
      | ~ m1_subset_1(X43,u1_struct_0(X42))
      | m1_subset_1(k7_lattices(X42,X43),u1_struct_0(X42)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_lattices])])])).

fof(c_0_22,plain,(
    ! [X46] :
      ( ( l1_lattices(X46)
        | ~ l3_lattices(X46) )
      & ( l2_lattices(X46)
        | ~ l3_lattices(X46) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).

fof(c_0_23,plain,(
    ! [X71,X72] :
      ( v2_struct_0(X71)
      | ~ v10_lattices(X71)
      | ~ v17_lattices(X71)
      | ~ l3_lattices(X71)
      | ~ m1_subset_1(X72,u1_struct_0(X71))
      | k7_lattices(X71,k7_lattices(X71,X72)) = X72 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t49_lattices])])])])).

cnf(c_0_24,plain,
    ( v2_struct_0(X1)
    | k7_lattices(X1,k4_lattices(X1,X2,X3)) = k3_lattices(X1,k7_lattices(X1,X2),k7_lattices(X1,X3))
    | ~ v10_lattices(X1)
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( l3_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( v17_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,negated_conjecture,
    ( v10_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_30,plain,(
    ! [X85,X86,X87] :
      ( v2_struct_0(X85)
      | ~ v10_lattices(X85)
      | ~ v17_lattices(X85)
      | ~ l3_lattices(X85)
      | ~ m1_subset_1(X86,u1_struct_0(X85))
      | ~ m1_subset_1(X87,u1_struct_0(X85))
      | k4_filter_0(X85,X86,X87) = k3_lattices(X85,k7_lattices(X85,X86),X87) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t55_filter_0])])])])).

cnf(c_0_31,plain,
    ( v2_struct_0(X1)
    | k4_lattices(X1,X2,X3) = k4_lattices(X1,X3,X2)
    | ~ v6_lattices(X1)
    | ~ l1_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_32,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k7_lattices(X1,X2),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_33,plain,
    ( l1_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_34,plain,
    ( v2_struct_0(X1)
    | k7_lattices(X1,k7_lattices(X1,X2)) = X2
    | ~ v10_lattices(X1)
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_36,plain,(
    ! [X11,X12,X13] :
      ( v2_struct_0(X11)
      | ~ v4_lattices(X11)
      | ~ l2_lattices(X11)
      | ~ m1_subset_1(X12,u1_struct_0(X11))
      | ~ m1_subset_1(X13,u1_struct_0(X11))
      | k3_lattices(X11,X12,X13) = k3_lattices(X11,X13,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[commutativity_k3_lattices])])])).

cnf(c_0_37,negated_conjecture,
    ( k3_lattices(esk1_0,k7_lattices(esk1_0,X1),k7_lattices(esk1_0,esk2_0)) = k7_lattices(esk1_0,k4_lattices(esk1_0,X1,esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26]),c_0_27]),c_0_28])]),c_0_29])).

cnf(c_0_38,plain,
    ( v2_struct_0(X1)
    | k4_filter_0(X1,X2,X3) = k3_lattices(X1,k7_lattices(X1,X2),X3)
    | ~ v10_lattices(X1)
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,plain,
    ( k4_lattices(X1,X2,k7_lattices(X1,X3)) = k4_lattices(X1,k7_lattices(X1,X3),X2)
    | v2_struct_0(X1)
    | ~ v6_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])).

cnf(c_0_40,negated_conjecture,
    ( k7_lattices(esk1_0,k7_lattices(esk1_0,esk3_0)) = esk3_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_26]),c_0_27]),c_0_28])]),c_0_29])).

cnf(c_0_41,negated_conjecture,
    ( k3_lattices(esk1_0,k7_lattices(esk1_0,X1),k7_lattices(esk1_0,esk3_0)) = k7_lattices(esk1_0,k4_lattices(esk1_0,X1,esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_35]),c_0_26]),c_0_27]),c_0_28])]),c_0_29])).

cnf(c_0_42,plain,
    ( v2_struct_0(X1)
    | k3_lattices(X1,X2,X3) = k3_lattices(X1,X3,X2)
    | ~ v4_lattices(X1)
    | ~ l2_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_43,plain,
    ( l2_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_44,negated_conjecture,
    ( k3_lattices(esk1_0,k7_lattices(esk1_0,esk3_0),k7_lattices(esk1_0,esk2_0)) = k7_lattices(esk1_0,k4_lattices(esk1_0,esk3_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_35])).

cnf(c_0_45,negated_conjecture,
    ( k3_lattices(esk1_0,k7_lattices(esk1_0,X1),esk3_0) = k4_filter_0(esk1_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_35]),c_0_26]),c_0_27]),c_0_28])]),c_0_29])).

cnf(c_0_46,negated_conjecture,
    ( k4_lattices(esk1_0,X1,esk3_0) = k4_lattices(esk1_0,esk3_0,X1)
    | ~ v6_lattices(esk1_0)
    | ~ m1_subset_1(k7_lattices(esk1_0,esk3_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_26])]),c_0_29])).

cnf(c_0_47,negated_conjecture,
    ( k3_lattices(esk1_0,k7_lattices(esk1_0,esk2_0),k7_lattices(esk1_0,esk3_0)) = k7_lattices(esk1_0,k4_lattices(esk1_0,esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_25])).

cnf(c_0_48,negated_conjecture,
    ( k3_lattices(esk1_0,k7_lattices(esk1_0,X1),esk2_0) = k4_filter_0(esk1_0,X1,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_25]),c_0_26]),c_0_27]),c_0_28])]),c_0_29])).

cnf(c_0_49,plain,
    ( k3_lattices(X1,X2,k7_lattices(X1,X3)) = k3_lattices(X1,k7_lattices(X1,X3),X2)
    | v2_struct_0(X1)
    | ~ v4_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_32]),c_0_43])).

fof(c_0_50,plain,(
    ! [X17,X18,X19] :
      ( v2_struct_0(X17)
      | ~ v10_lattices(X17)
      | ~ l3_lattices(X17)
      | ~ m1_subset_1(X18,u1_struct_0(X17))
      | ~ m1_subset_1(X19,u1_struct_0(X17))
      | k7_filter_0(X17,X18,X19) = k4_lattices(X17,k4_filter_0(X17,X18,X19),k4_filter_0(X17,X19,X18)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d11_filter_0])])])])).

cnf(c_0_51,negated_conjecture,
    ( k4_filter_0(esk1_0,esk3_0,k7_lattices(esk1_0,esk2_0)) = k7_lattices(esk1_0,k4_lattices(esk1_0,esk3_0,esk2_0))
    | ~ m1_subset_1(k7_lattices(esk1_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_44]),c_0_35]),c_0_26]),c_0_27]),c_0_28])]),c_0_29])).

cnf(c_0_52,negated_conjecture,
    ( k3_lattices(esk1_0,k7_lattices(esk1_0,k7_lattices(esk1_0,X1)),esk3_0) = k4_filter_0(esk1_0,k7_lattices(esk1_0,X1),esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_32]),c_0_26])]),c_0_29])).

cnf(c_0_53,negated_conjecture,
    ( k7_lattices(esk1_0,k7_lattices(esk1_0,esk2_0)) = esk2_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_25]),c_0_26]),c_0_27]),c_0_28])]),c_0_29])).

cnf(c_0_54,negated_conjecture,
    ( k4_lattices(esk1_0,X1,esk3_0) = k4_lattices(esk1_0,esk3_0,X1)
    | ~ v6_lattices(esk1_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_32]),c_0_35]),c_0_26])]),c_0_29])).

fof(c_0_55,plain,(
    ! [X10] :
      ( ( ~ v2_struct_0(X10)
        | v2_struct_0(X10)
        | ~ v10_lattices(X10)
        | ~ l3_lattices(X10) )
      & ( v4_lattices(X10)
        | v2_struct_0(X10)
        | ~ v10_lattices(X10)
        | ~ l3_lattices(X10) )
      & ( v5_lattices(X10)
        | v2_struct_0(X10)
        | ~ v10_lattices(X10)
        | ~ l3_lattices(X10) )
      & ( v6_lattices(X10)
        | v2_struct_0(X10)
        | ~ v10_lattices(X10)
        | ~ l3_lattices(X10) )
      & ( v7_lattices(X10)
        | v2_struct_0(X10)
        | ~ v10_lattices(X10)
        | ~ l3_lattices(X10) )
      & ( v8_lattices(X10)
        | v2_struct_0(X10)
        | ~ v10_lattices(X10)
        | ~ l3_lattices(X10) )
      & ( v9_lattices(X10)
        | v2_struct_0(X10)
        | ~ v10_lattices(X10)
        | ~ l3_lattices(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).

cnf(c_0_56,negated_conjecture,
    ( k4_filter_0(esk1_0,esk2_0,k7_lattices(esk1_0,esk3_0)) = k7_lattices(esk1_0,k4_lattices(esk1_0,esk2_0,esk3_0))
    | ~ m1_subset_1(k7_lattices(esk1_0,esk3_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_47]),c_0_25]),c_0_26]),c_0_27]),c_0_28])]),c_0_29])).

cnf(c_0_57,negated_conjecture,
    ( k3_lattices(esk1_0,k7_lattices(esk1_0,k7_lattices(esk1_0,X1)),esk2_0) = k4_filter_0(esk1_0,k7_lattices(esk1_0,X1),esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_32]),c_0_26])]),c_0_29])).

cnf(c_0_58,negated_conjecture,
    ( k3_lattices(esk1_0,X1,esk3_0) = k3_lattices(esk1_0,esk3_0,X1)
    | ~ v4_lattices(esk1_0)
    | ~ m1_subset_1(k7_lattices(esk1_0,esk3_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_40]),c_0_26])]),c_0_29])).

cnf(c_0_59,plain,
    ( v2_struct_0(X1)
    | k7_filter_0(X1,X2,X3) = k4_lattices(X1,k4_filter_0(X1,X2,X3),k4_filter_0(X1,X3,X2))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_60,negated_conjecture,
    ( k4_filter_0(esk1_0,esk3_0,k7_lattices(esk1_0,esk2_0)) = k7_lattices(esk1_0,k4_lattices(esk1_0,esk3_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_32]),c_0_25]),c_0_26])]),c_0_29])).

cnf(c_0_61,negated_conjecture,
    ( k4_filter_0(esk1_0,k7_lattices(esk1_0,esk2_0),esk3_0) = k3_lattices(esk1_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_25]),c_0_53])).

cnf(c_0_62,negated_conjecture,
    ( k4_lattices(esk1_0,esk3_0,esk2_0) = k4_lattices(esk1_0,esk2_0,esk3_0)
    | ~ v6_lattices(esk1_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_25])).

cnf(c_0_63,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

fof(c_0_64,plain,(
    ! [X55,X56,X57] :
      ( v2_struct_0(X55)
      | ~ v4_lattices(X55)
      | ~ l2_lattices(X55)
      | ~ m1_subset_1(X56,u1_struct_0(X55))
      | ~ m1_subset_1(X57,u1_struct_0(X55))
      | k3_lattices(X55,X56,X57) = k1_lattices(X55,X56,X57) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_lattices])])])).

fof(c_0_65,plain,(
    ! [X82,X83,X84] :
      ( v2_struct_0(X82)
      | ~ v10_lattices(X82)
      | ~ v17_lattices(X82)
      | ~ l3_lattices(X82)
      | ~ m1_subset_1(X83,u1_struct_0(X82))
      | ~ m1_subset_1(X84,u1_struct_0(X82))
      | k7_lattices(X82,k3_lattices(X82,X83,X84)) = k4_lattices(X82,k7_lattices(X82,X83),k7_lattices(X82,X84)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t51_lattices])])])])).

cnf(c_0_66,negated_conjecture,
    ( k4_filter_0(esk1_0,esk2_0,k7_lattices(esk1_0,esk3_0)) = k7_lattices(esk1_0,k4_lattices(esk1_0,esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_32]),c_0_35]),c_0_26])]),c_0_29])).

cnf(c_0_67,negated_conjecture,
    ( k4_filter_0(esk1_0,k7_lattices(esk1_0,esk3_0),esk2_0) = k3_lattices(esk1_0,esk3_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_35]),c_0_40])).

cnf(c_0_68,negated_conjecture,
    ( k3_lattices(esk1_0,X1,esk3_0) = k3_lattices(esk1_0,esk3_0,X1)
    | ~ v4_lattices(esk1_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_32]),c_0_35]),c_0_26])]),c_0_29])).

cnf(c_0_69,negated_conjecture,
    ( k4_lattices(esk1_0,k7_lattices(esk1_0,k4_lattices(esk1_0,esk3_0,esk2_0)),k3_lattices(esk1_0,esk2_0,esk3_0)) = k7_filter_0(esk1_0,esk3_0,k7_lattices(esk1_0,esk2_0))
    | ~ m1_subset_1(k7_lattices(esk1_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61]),c_0_35]),c_0_26]),c_0_28])]),c_0_29])).

cnf(c_0_70,negated_conjecture,
    ( k4_lattices(esk1_0,esk3_0,esk2_0) = k4_lattices(esk1_0,esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_26]),c_0_28])]),c_0_29])).

cnf(c_0_71,plain,
    ( v2_struct_0(X1)
    | k3_lattices(X1,X2,X3) = k1_lattices(X1,X2,X3)
    | ~ v4_lattices(X1)
    | ~ l2_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

fof(c_0_72,plain,(
    ! [X36,X37,X38] :
      ( v2_struct_0(X36)
      | ~ v6_lattices(X36)
      | ~ l1_lattices(X36)
      | ~ m1_subset_1(X37,u1_struct_0(X36))
      | ~ m1_subset_1(X38,u1_struct_0(X36))
      | m1_subset_1(k4_lattices(X36,X37,X38),u1_struct_0(X36)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_lattices])])])).

cnf(c_0_73,plain,
    ( v2_struct_0(X1)
    | k7_lattices(X1,k3_lattices(X1,X2,X3)) = k4_lattices(X1,k7_lattices(X1,X2),k7_lattices(X1,X3))
    | ~ v10_lattices(X1)
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

fof(c_0_74,plain,(
    ! [X33,X34,X35] :
      ( v2_struct_0(X33)
      | ~ v10_lattices(X33)
      | ~ l3_lattices(X33)
      | ~ m1_subset_1(X34,u1_struct_0(X33))
      | ~ m1_subset_1(X35,u1_struct_0(X33))
      | m1_subset_1(k4_filter_0(X33,X34,X35),u1_struct_0(X33)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_filter_0])])])).

cnf(c_0_75,negated_conjecture,
    ( k4_lattices(esk1_0,k3_lattices(esk1_0,esk2_0,esk3_0),k7_lattices(esk1_0,k4_lattices(esk1_0,esk3_0,esk2_0))) = k7_filter_0(esk1_0,k7_lattices(esk1_0,esk2_0),esk3_0)
    | ~ m1_subset_1(k7_lattices(esk1_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61]),c_0_35]),c_0_26]),c_0_28])]),c_0_29])).

cnf(c_0_76,negated_conjecture,
    ( k4_lattices(esk1_0,k7_lattices(esk1_0,k4_lattices(esk1_0,esk2_0,esk3_0)),k3_lattices(esk1_0,esk3_0,esk2_0)) = k7_filter_0(esk1_0,esk2_0,k7_lattices(esk1_0,esk3_0))
    | ~ m1_subset_1(k7_lattices(esk1_0,esk3_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_66]),c_0_67]),c_0_25]),c_0_26]),c_0_28])]),c_0_29])).

cnf(c_0_77,negated_conjecture,
    ( k3_lattices(esk1_0,esk3_0,esk2_0) = k3_lattices(esk1_0,esk2_0,esk3_0)
    | ~ v4_lattices(esk1_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_25])).

cnf(c_0_78,plain,
    ( v4_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_79,negated_conjecture,
    ( k4_lattices(esk1_0,k7_lattices(esk1_0,k4_lattices(esk1_0,esk2_0,esk3_0)),k3_lattices(esk1_0,esk2_0,esk3_0)) = k7_filter_0(esk1_0,esk3_0,k7_lattices(esk1_0,esk2_0))
    | ~ m1_subset_1(k7_lattices(esk1_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_69,c_0_70])).

fof(c_0_80,plain,(
    ! [X20,X21,X22] :
      ( v2_struct_0(X20)
      | ~ l2_lattices(X20)
      | ~ m1_subset_1(X21,u1_struct_0(X20))
      | ~ m1_subset_1(X22,u1_struct_0(X20))
      | m1_subset_1(k1_lattices(X20,X21,X22),u1_struct_0(X20)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_lattices])])])).

cnf(c_0_81,negated_conjecture,
    ( k1_lattices(esk1_0,X1,esk3_0) = k3_lattices(esk1_0,X1,esk3_0)
    | ~ l2_lattices(esk1_0)
    | ~ v4_lattices(esk1_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_35]),c_0_29])).

cnf(c_0_82,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k4_lattices(X1,X2,X3),u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ l1_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_83,negated_conjecture,
    ( k4_lattices(esk1_0,k7_lattices(esk1_0,X1),k7_lattices(esk1_0,esk3_0)) = k7_lattices(esk1_0,k3_lattices(esk1_0,X1,esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_35]),c_0_26]),c_0_27]),c_0_28])]),c_0_29])).

cnf(c_0_84,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k4_filter_0(X1,X2,X3),u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_85,negated_conjecture,
    ( k4_lattices(esk1_0,k3_lattices(esk1_0,esk2_0,esk3_0),k7_lattices(esk1_0,k4_lattices(esk1_0,esk2_0,esk3_0))) = k7_filter_0(esk1_0,k7_lattices(esk1_0,esk2_0),esk3_0)
    | ~ m1_subset_1(k7_lattices(esk1_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_75,c_0_70])).

cnf(c_0_86,negated_conjecture,
    ( k4_lattices(esk1_0,k7_lattices(esk1_0,k4_lattices(esk1_0,esk2_0,esk3_0)),k3_lattices(esk1_0,esk3_0,esk2_0)) = k7_filter_0(esk1_0,esk2_0,k7_lattices(esk1_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_32]),c_0_35]),c_0_26])]),c_0_29])).

cnf(c_0_87,negated_conjecture,
    ( k3_lattices(esk1_0,esk3_0,esk2_0) = k3_lattices(esk1_0,esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_26]),c_0_28])]),c_0_29])).

cnf(c_0_88,negated_conjecture,
    ( k4_lattices(esk1_0,k7_lattices(esk1_0,k4_lattices(esk1_0,esk2_0,esk3_0)),k3_lattices(esk1_0,esk2_0,esk3_0)) = k7_filter_0(esk1_0,esk3_0,k7_lattices(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_32]),c_0_25]),c_0_26])]),c_0_29])).

cnf(c_0_89,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k1_lattices(X1,X2,X3),u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_90,negated_conjecture,
    ( k1_lattices(esk1_0,esk2_0,esk3_0) = k3_lattices(esk1_0,esk2_0,esk3_0)
    | ~ l2_lattices(esk1_0)
    | ~ v4_lattices(esk1_0) ),
    inference(spm,[status(thm)],[c_0_81,c_0_25])).

cnf(c_0_91,plain,
    ( k7_lattices(X1,k7_lattices(X1,k4_lattices(X1,X2,X3))) = k4_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | ~ v17_lattices(X1)
    | ~ v10_lattices(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_82]),c_0_63]),c_0_33])).

fof(c_0_92,plain,(
    ! [X79,X80,X81] :
      ( v2_struct_0(X79)
      | ~ v10_lattices(X79)
      | ~ v17_lattices(X79)
      | ~ l3_lattices(X79)
      | ~ m1_subset_1(X80,u1_struct_0(X79))
      | ~ m1_subset_1(X81,u1_struct_0(X79))
      | k7_filter_0(X79,X80,X81) = k3_lattices(X79,k4_lattices(X79,X80,X81),k4_lattices(X79,k7_lattices(X79,X80),k7_lattices(X79,X81))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t51_filter_1])])])])).

cnf(c_0_93,negated_conjecture,
    ( k4_lattices(esk1_0,k7_lattices(esk1_0,k7_lattices(esk1_0,X1)),k7_lattices(esk1_0,esk3_0)) = k7_lattices(esk1_0,k3_lattices(esk1_0,k7_lattices(esk1_0,X1),esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_32]),c_0_26])]),c_0_29])).

cnf(c_0_94,negated_conjecture,
    ( k3_lattices(esk1_0,k7_lattices(esk1_0,esk2_0),esk3_0) = k4_filter_0(esk1_0,esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_25])).

cnf(c_0_95,plain,
    ( k4_lattices(X1,k4_filter_0(X1,X2,X3),k4_filter_0(X1,X3,X2)) = k7_filter_0(X1,X3,X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_59]),c_0_84]),c_0_84]),c_0_63]),c_0_33])).

cnf(c_0_96,negated_conjecture,
    ( k4_filter_0(esk1_0,esk3_0,k7_lattices(esk1_0,esk2_0)) = k7_lattices(esk1_0,k4_lattices(esk1_0,esk2_0,esk3_0)) ),
    inference(rw,[status(thm)],[c_0_60,c_0_70])).

cnf(c_0_97,negated_conjecture,
    ( k4_lattices(esk1_0,k3_lattices(esk1_0,esk2_0,esk3_0),k7_lattices(esk1_0,k4_lattices(esk1_0,esk2_0,esk3_0))) = k7_filter_0(esk1_0,k7_lattices(esk1_0,esk2_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_32]),c_0_25]),c_0_26])]),c_0_29])).

cnf(c_0_98,negated_conjecture,
    ( k7_filter_0(esk1_0,esk3_0,k7_lattices(esk1_0,esk2_0)) = k7_filter_0(esk1_0,esk2_0,k7_lattices(esk1_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_86,c_0_87]),c_0_88])).

fof(c_0_99,plain,(
    ! [X39,X40,X41] :
      ( v2_struct_0(X39)
      | ~ v10_lattices(X39)
      | ~ l3_lattices(X39)
      | ~ m1_subset_1(X40,u1_struct_0(X39))
      | ~ m1_subset_1(X41,u1_struct_0(X39))
      | m1_subset_1(k7_filter_0(X39,X40,X41),u1_struct_0(X39)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_filter_0])])])).

cnf(c_0_100,negated_conjecture,
    ( m1_subset_1(k3_lattices(esk1_0,esk2_0,esk3_0),u1_struct_0(esk1_0))
    | ~ l2_lattices(esk1_0)
    | ~ v4_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_35]),c_0_25])]),c_0_29])).

cnf(c_0_101,negated_conjecture,
    ( k7_lattices(esk1_0,k7_lattices(esk1_0,k4_lattices(esk1_0,X1,esk3_0))) = k4_lattices(esk1_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_35]),c_0_26]),c_0_27]),c_0_28])]),c_0_29])).

cnf(c_0_102,plain,
    ( v2_struct_0(X1)
    | k7_filter_0(X1,X2,X3) = k3_lattices(X1,k4_lattices(X1,X2,X3),k4_lattices(X1,k7_lattices(X1,X2),k7_lattices(X1,X3)))
    | ~ v10_lattices(X1)
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_92])).

cnf(c_0_103,negated_conjecture,
    ( k4_lattices(esk1_0,k7_lattices(esk1_0,esk2_0),k7_lattices(esk1_0,esk3_0)) = k7_lattices(esk1_0,k3_lattices(esk1_0,esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_83,c_0_25])).

cnf(c_0_104,negated_conjecture,
    ( k7_lattices(esk1_0,k4_filter_0(esk1_0,esk2_0,esk3_0)) != k4_lattices(esk1_0,esk2_0,k7_lattices(esk1_0,esk3_0))
    | k7_lattices(esk1_0,k7_filter_0(esk1_0,esk2_0,esk3_0)) != k3_lattices(esk1_0,k4_lattices(esk1_0,esk2_0,k7_lattices(esk1_0,esk3_0)),k4_lattices(esk1_0,k7_lattices(esk1_0,esk2_0),esk3_0))
    | k7_lattices(esk1_0,k7_filter_0(esk1_0,esk2_0,esk3_0)) != k7_filter_0(esk1_0,esk2_0,k7_lattices(esk1_0,esk3_0))
    | k7_lattices(esk1_0,k7_filter_0(esk1_0,esk2_0,esk3_0)) != k7_filter_0(esk1_0,k7_lattices(esk1_0,esk2_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_105,negated_conjecture,
    ( k7_lattices(esk1_0,k4_filter_0(esk1_0,esk2_0,esk3_0)) = k4_lattices(esk1_0,esk2_0,k7_lattices(esk1_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_25]),c_0_53]),c_0_94])).

cnf(c_0_106,negated_conjecture,
    ( k7_filter_0(esk1_0,k7_lattices(esk1_0,esk2_0),esk3_0) = k7_filter_0(esk1_0,esk2_0,k7_lattices(esk1_0,esk3_0))
    | ~ m1_subset_1(k7_lattices(esk1_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_96]),c_0_61]),c_0_97]),c_0_98]),c_0_35]),c_0_26]),c_0_28])]),c_0_29])).

cnf(c_0_107,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k7_filter_0(X1,X2,X3),u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_99])).

cnf(c_0_108,negated_conjecture,
    ( k3_lattices(esk1_0,k7_lattices(esk1_0,X1),k7_lattices(esk1_0,k3_lattices(esk1_0,esk2_0,esk3_0))) = k7_lattices(esk1_0,k4_lattices(esk1_0,X1,k3_lattices(esk1_0,esk2_0,esk3_0)))
    | ~ l2_lattices(esk1_0)
    | ~ v4_lattices(esk1_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_100]),c_0_26]),c_0_27]),c_0_28])]),c_0_29])).

cnf(c_0_109,negated_conjecture,
    ( k7_lattices(esk1_0,k7_lattices(esk1_0,k4_lattices(esk1_0,esk2_0,esk3_0))) = k4_lattices(esk1_0,esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_101,c_0_25])).

cnf(c_0_110,negated_conjecture,
    ( k3_lattices(esk1_0,k4_lattices(esk1_0,esk2_0,esk3_0),k7_lattices(esk1_0,k3_lattices(esk1_0,esk2_0,esk3_0))) = k7_filter_0(esk1_0,esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_103]),c_0_35]),c_0_25]),c_0_26]),c_0_27]),c_0_28])]),c_0_29])).

cnf(c_0_111,negated_conjecture,
    ( k3_lattices(esk1_0,k4_lattices(esk1_0,esk2_0,k7_lattices(esk1_0,esk3_0)),k4_lattices(esk1_0,k7_lattices(esk1_0,esk2_0),esk3_0)) != k7_lattices(esk1_0,k7_filter_0(esk1_0,esk2_0,esk3_0))
    | k7_filter_0(esk1_0,esk2_0,k7_lattices(esk1_0,esk3_0)) != k7_lattices(esk1_0,k7_filter_0(esk1_0,esk2_0,esk3_0))
    | k7_filter_0(esk1_0,k7_lattices(esk1_0,esk2_0),esk3_0) != k7_lattices(esk1_0,k7_filter_0(esk1_0,esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_104,c_0_105])])).

cnf(c_0_112,negated_conjecture,
    ( k7_filter_0(esk1_0,k7_lattices(esk1_0,esk2_0),esk3_0) = k7_filter_0(esk1_0,esk2_0,k7_lattices(esk1_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_32]),c_0_25]),c_0_26])]),c_0_29])).

cnf(c_0_113,plain,
    ( k7_lattices(X1,k7_lattices(X1,k7_filter_0(X1,X2,X3))) = k7_filter_0(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | ~ v17_lattices(X1)
    | ~ v10_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_107])).

cnf(c_0_114,negated_conjecture,
    ( k7_lattices(esk1_0,k7_filter_0(esk1_0,esk2_0,k7_lattices(esk1_0,esk3_0))) = k7_filter_0(esk1_0,esk2_0,esk3_0)
    | ~ l2_lattices(esk1_0)
    | ~ v4_lattices(esk1_0)
    | ~ m1_subset_1(k7_lattices(esk1_0,k4_lattices(esk1_0,esk2_0,esk3_0)),u1_struct_0(esk1_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_109]),c_0_110]),c_0_88]),c_0_98])).

cnf(c_0_115,negated_conjecture,
    ( m1_subset_1(k7_lattices(esk1_0,k4_lattices(esk1_0,esk2_0,esk3_0)),u1_struct_0(esk1_0))
    | ~ m1_subset_1(k7_lattices(esk1_0,esk3_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_66]),c_0_25]),c_0_26]),c_0_28])]),c_0_29])).

cnf(c_0_116,negated_conjecture,
    ( k3_lattices(esk1_0,k4_lattices(esk1_0,esk2_0,k7_lattices(esk1_0,esk3_0)),k4_lattices(esk1_0,k7_lattices(esk1_0,esk2_0),esk3_0)) != k7_lattices(esk1_0,k7_filter_0(esk1_0,esk2_0,esk3_0))
    | k7_filter_0(esk1_0,esk2_0,k7_lattices(esk1_0,esk3_0)) != k7_lattices(esk1_0,k7_filter_0(esk1_0,esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_111,c_0_112])])).

cnf(c_0_117,negated_conjecture,
    ( k3_lattices(esk1_0,k4_lattices(esk1_0,X1,k7_lattices(esk1_0,esk3_0)),k4_lattices(esk1_0,k7_lattices(esk1_0,X1),esk3_0)) = k7_filter_0(esk1_0,X1,k7_lattices(esk1_0,esk3_0))
    | ~ m1_subset_1(k7_lattices(esk1_0,esk3_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_40]),c_0_26]),c_0_27]),c_0_28])]),c_0_29])).

cnf(c_0_118,negated_conjecture,
    ( k7_lattices(esk1_0,k7_lattices(esk1_0,k7_filter_0(esk1_0,esk2_0,k7_lattices(esk1_0,esk3_0)))) = k7_filter_0(esk1_0,esk2_0,k7_lattices(esk1_0,esk3_0))
    | ~ m1_subset_1(k7_lattices(esk1_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_98]),c_0_35]),c_0_26]),c_0_27]),c_0_28])]),c_0_29])).

cnf(c_0_119,negated_conjecture,
    ( k7_lattices(esk1_0,k7_filter_0(esk1_0,esk2_0,k7_lattices(esk1_0,esk3_0))) = k7_filter_0(esk1_0,esk2_0,esk3_0)
    | ~ l2_lattices(esk1_0)
    | ~ v4_lattices(esk1_0)
    | ~ m1_subset_1(k7_lattices(esk1_0,esk3_0),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_114,c_0_115])).

cnf(c_0_120,negated_conjecture,
    ( k7_filter_0(esk1_0,esk2_0,k7_lattices(esk1_0,esk3_0)) != k7_lattices(esk1_0,k7_filter_0(esk1_0,esk2_0,esk3_0))
    | ~ m1_subset_1(k7_lattices(esk1_0,esk3_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_117]),c_0_25])])).

cnf(c_0_121,negated_conjecture,
    ( k7_lattices(esk1_0,k7_lattices(esk1_0,k7_filter_0(esk1_0,esk2_0,k7_lattices(esk1_0,esk3_0)))) = k7_filter_0(esk1_0,esk2_0,k7_lattices(esk1_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118,c_0_32]),c_0_25]),c_0_26])]),c_0_29])).

cnf(c_0_122,negated_conjecture,
    ( k7_lattices(esk1_0,k7_filter_0(esk1_0,esk2_0,k7_lattices(esk1_0,esk3_0))) = k7_filter_0(esk1_0,esk2_0,esk3_0)
    | ~ l2_lattices(esk1_0)
    | ~ v4_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_32]),c_0_35]),c_0_26])]),c_0_29])).

cnf(c_0_123,negated_conjecture,
    ( k7_filter_0(esk1_0,esk2_0,k7_lattices(esk1_0,esk3_0)) != k7_lattices(esk1_0,k7_filter_0(esk1_0,esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_32]),c_0_35]),c_0_26])]),c_0_29])).

cnf(c_0_124,negated_conjecture,
    ( ~ l2_lattices(esk1_0)
    | ~ v4_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_122]),c_0_123])).

cnf(c_0_125,negated_conjecture,
    ( ~ l2_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_78]),c_0_26]),c_0_28])]),c_0_29])).

cnf(c_0_126,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125,c_0_43]),c_0_26])]),
    [proof]).
%------------------------------------------------------------------------------
