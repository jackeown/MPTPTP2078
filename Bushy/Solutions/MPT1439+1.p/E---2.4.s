%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : filter_1__t34_filter_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:09 EDT 2019

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   39 ( 173 expanded)
%              Number of clauses        :   28 (  54 expanded)
%              Number of leaves         :    5 (  43 expanded)
%              Depth                    :   10
%              Number of atoms          :  161 (1438 expanded)
%              Number of equality atoms :    3 (   9 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t34_filter_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v10_lattices(X2)
            & l3_lattices(X2) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & v10_lattices(X3)
                & l3_lattices(X3) )
             => ( ( r1_filter_1(X1,X2)
                  & r1_filter_1(X2,X3) )
               => r1_filter_1(X1,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t34_filter_1.p',t34_filter_1)).

fof(d9_filter_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v10_lattices(X2)
            & l3_lattices(X2) )
         => ( r1_filter_1(X1,X2)
          <=> r4_wellord1(k8_filter_1(X1),k8_filter_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t34_filter_1.p',d9_filter_1)).

fof(t52_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => ( ( r4_wellord1(X1,X2)
                  & r4_wellord1(X2,X3) )
               => r4_wellord1(X1,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t34_filter_1.p',t52_wellord1)).

fof(dt_k8_filter_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & l3_lattices(X1) )
     => v1_relat_1(k8_filter_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t34_filter_1.p',dt_k8_filter_1)).

fof(d8_filter_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & l3_lattices(X1) )
     => k8_filter_1(X1) = a_1_0_filter_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t34_filter_1.p',d8_filter_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v10_lattices(X1)
          & l3_lattices(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & v10_lattices(X2)
              & l3_lattices(X2) )
           => ! [X3] :
                ( ( ~ v2_struct_0(X3)
                  & v10_lattices(X3)
                  & l3_lattices(X3) )
               => ( ( r1_filter_1(X1,X2)
                    & r1_filter_1(X2,X3) )
                 => r1_filter_1(X1,X3) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t34_filter_1])).

fof(c_0_6,plain,(
    ! [X32,X33] :
      ( ( ~ r1_filter_1(X32,X33)
        | r4_wellord1(k8_filter_1(X32),k8_filter_1(X33))
        | v2_struct_0(X33)
        | ~ v10_lattices(X33)
        | ~ l3_lattices(X33)
        | v2_struct_0(X32)
        | ~ v10_lattices(X32)
        | ~ l3_lattices(X32) )
      & ( ~ r4_wellord1(k8_filter_1(X32),k8_filter_1(X33))
        | r1_filter_1(X32,X33)
        | v2_struct_0(X33)
        | ~ v10_lattices(X33)
        | ~ l3_lattices(X33)
        | v2_struct_0(X32)
        | ~ v10_lattices(X32)
        | ~ l3_lattices(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d9_filter_1])])])])])).

fof(c_0_7,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v10_lattices(esk1_0)
    & l3_lattices(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & v10_lattices(esk2_0)
    & l3_lattices(esk2_0)
    & ~ v2_struct_0(esk3_0)
    & v10_lattices(esk3_0)
    & l3_lattices(esk3_0)
    & r1_filter_1(esk1_0,esk2_0)
    & r1_filter_1(esk2_0,esk3_0)
    & ~ r1_filter_1(esk1_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])).

fof(c_0_8,plain,(
    ! [X89,X90,X91] :
      ( ~ v1_relat_1(X89)
      | ~ v1_relat_1(X90)
      | ~ v1_relat_1(X91)
      | ~ r4_wellord1(X89,X90)
      | ~ r4_wellord1(X90,X91)
      | r4_wellord1(X89,X91) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_wellord1])])])).

cnf(c_0_9,plain,
    ( r4_wellord1(k8_filter_1(X1),k8_filter_1(X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_filter_1(X1,X2)
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( r1_filter_1(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( l3_lattices(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( l3_lattices(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,negated_conjecture,
    ( v10_lattices(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,negated_conjecture,
    ( v10_lattices(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_16,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_17,plain,
    ( r4_wellord1(X1,X3)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ r4_wellord1(X1,X2)
    | ~ r4_wellord1(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_18,negated_conjecture,
    ( r4_wellord1(k8_filter_1(esk2_0),k8_filter_1(esk3_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11]),c_0_12]),c_0_13]),c_0_14])]),c_0_15]),c_0_16])).

fof(c_0_19,plain,(
    ! [X38] :
      ( v2_struct_0(X38)
      | ~ v10_lattices(X38)
      | ~ l3_lattices(X38)
      | v1_relat_1(k8_filter_1(X38)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k8_filter_1])])])).

cnf(c_0_20,negated_conjecture,
    ( r4_wellord1(X1,k8_filter_1(esk3_0))
    | ~ r4_wellord1(X1,k8_filter_1(esk2_0))
    | ~ v1_relat_1(k8_filter_1(esk3_0))
    | ~ v1_relat_1(k8_filter_1(esk2_0))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_21,plain,
    ( v2_struct_0(X1)
    | v1_relat_1(k8_filter_1(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_22,negated_conjecture,
    ( r1_filter_1(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_23,negated_conjecture,
    ( l3_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_24,negated_conjecture,
    ( v10_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_25,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_26,plain,(
    ! [X31] :
      ( v2_struct_0(X31)
      | ~ v10_lattices(X31)
      | ~ l3_lattices(X31)
      | k8_filter_1(X31) = a_1_0_filter_1(X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d8_filter_1])])])).

cnf(c_0_27,negated_conjecture,
    ( r4_wellord1(X1,k8_filter_1(esk3_0))
    | ~ r4_wellord1(X1,k8_filter_1(esk2_0))
    | ~ v1_relat_1(k8_filter_1(esk2_0))
    | ~ v1_relat_1(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_11]),c_0_13])]),c_0_16])).

cnf(c_0_28,negated_conjecture,
    ( r4_wellord1(k8_filter_1(esk1_0),k8_filter_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_22]),c_0_12]),c_0_23]),c_0_14]),c_0_24])]),c_0_25]),c_0_15])).

cnf(c_0_29,plain,
    ( v2_struct_0(X1)
    | k8_filter_1(X1) = a_1_0_filter_1(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_30,negated_conjecture,
    ( r4_wellord1(X1,k8_filter_1(esk3_0))
    | ~ r4_wellord1(X1,k8_filter_1(esk2_0))
    | ~ v1_relat_1(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_21]),c_0_12]),c_0_14])]),c_0_15])).

cnf(c_0_31,negated_conjecture,
    ( r4_wellord1(a_1_0_filter_1(esk1_0),k8_filter_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_23]),c_0_24])]),c_0_25])).

cnf(c_0_32,plain,
    ( r1_filter_1(X1,X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r4_wellord1(k8_filter_1(X1),k8_filter_1(X2))
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_33,negated_conjecture,
    ( r4_wellord1(a_1_0_filter_1(esk1_0),k8_filter_1(esk3_0))
    | ~ v1_relat_1(a_1_0_filter_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_34,plain,
    ( v1_relat_1(a_1_0_filter_1(X1))
    | v2_struct_0(X1)
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_29])).

cnf(c_0_35,plain,
    ( r1_filter_1(X1,X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r4_wellord1(a_1_0_filter_1(X1),k8_filter_1(X2))
    | ~ l3_lattices(X2)
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X2)
    | ~ v10_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_29])).

cnf(c_0_36,negated_conjecture,
    ( r4_wellord1(a_1_0_filter_1(esk1_0),k8_filter_1(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_23]),c_0_24])]),c_0_25])).

cnf(c_0_37,negated_conjecture,
    ( ~ r1_filter_1(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_38,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_11]),c_0_23]),c_0_13]),c_0_24])]),c_0_37]),c_0_16]),c_0_25]),
    [proof]).
%------------------------------------------------------------------------------
