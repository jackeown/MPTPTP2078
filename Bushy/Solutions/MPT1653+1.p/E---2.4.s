%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : waybel_0__t33_waybel_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:48 EDT 2019

% Result     : Theorem 0.54s
% Output     : CNFRefutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :   27 ( 188 expanded)
%              Number of clauses        :   20 (  59 expanded)
%              Number of leaves         :    3 (  46 expanded)
%              Depth                    :    8
%              Number of atoms          :  129 (1119 expanded)
%              Number of equality atoms :   15 ( 153 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   17 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t33_waybel_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( r1_yellow_0(X1,X2)
           => k1_yellow_0(X1,X2) = k1_yellow_0(X1,k3_waybel_0(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t33_waybel_0.p',t33_waybel_0)).

fof(t47_yellow_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ! [X2,X3] :
          ( ( r1_yellow_0(X1,X2)
            & ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_lattice3(X1,X2,X4)
                <=> r2_lattice3(X1,X3,X4) ) ) )
         => k1_yellow_0(X1,X2) = k1_yellow_0(X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t33_waybel_0.p',t47_yellow_0)).

fof(t31_waybel_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r2_lattice3(X1,X2,X3)
              <=> r2_lattice3(X1,k3_waybel_0(X1,X2),X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t33_waybel_0.p',t31_waybel_0)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( r1_yellow_0(X1,X2)
             => k1_yellow_0(X1,X2) = k1_yellow_0(X1,k3_waybel_0(X1,X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t33_waybel_0])).

fof(c_0_4,plain,(
    ! [X98,X99,X100] :
      ( ( m1_subset_1(esk23_3(X98,X99,X100),u1_struct_0(X98))
        | ~ r1_yellow_0(X98,X99)
        | k1_yellow_0(X98,X99) = k1_yellow_0(X98,X100)
        | v2_struct_0(X98)
        | ~ l1_orders_2(X98) )
      & ( ~ r2_lattice3(X98,X99,esk23_3(X98,X99,X100))
        | ~ r2_lattice3(X98,X100,esk23_3(X98,X99,X100))
        | ~ r1_yellow_0(X98,X99)
        | k1_yellow_0(X98,X99) = k1_yellow_0(X98,X100)
        | v2_struct_0(X98)
        | ~ l1_orders_2(X98) )
      & ( r2_lattice3(X98,X99,esk23_3(X98,X99,X100))
        | r2_lattice3(X98,X100,esk23_3(X98,X99,X100))
        | ~ r1_yellow_0(X98,X99)
        | k1_yellow_0(X98,X99) = k1_yellow_0(X98,X100)
        | v2_struct_0(X98)
        | ~ l1_orders_2(X98) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t47_yellow_0])])])])])])).

fof(c_0_5,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v3_orders_2(esk1_0)
    & v4_orders_2(esk1_0)
    & l1_orders_2(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & r1_yellow_0(esk1_0,esk2_0)
    & k1_yellow_0(esk1_0,esk2_0) != k1_yellow_0(esk1_0,k3_waybel_0(esk1_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_3])])])])).

fof(c_0_6,plain,(
    ! [X93,X94,X95] :
      ( ( ~ r2_lattice3(X93,X94,X95)
        | r2_lattice3(X93,k3_waybel_0(X93,X94),X95)
        | ~ m1_subset_1(X95,u1_struct_0(X93))
        | ~ m1_subset_1(X94,k1_zfmisc_1(u1_struct_0(X93)))
        | v2_struct_0(X93)
        | ~ v3_orders_2(X93)
        | ~ v4_orders_2(X93)
        | ~ l1_orders_2(X93) )
      & ( ~ r2_lattice3(X93,k3_waybel_0(X93,X94),X95)
        | r2_lattice3(X93,X94,X95)
        | ~ m1_subset_1(X95,u1_struct_0(X93))
        | ~ m1_subset_1(X94,k1_zfmisc_1(u1_struct_0(X93)))
        | v2_struct_0(X93)
        | ~ v3_orders_2(X93)
        | ~ v4_orders_2(X93)
        | ~ l1_orders_2(X93) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t31_waybel_0])])])])])).

cnf(c_0_7,plain,
    ( r2_lattice3(X1,X2,esk23_3(X1,X2,X3))
    | r2_lattice3(X1,X3,esk23_3(X1,X2,X3))
    | k1_yellow_0(X1,X2) = k1_yellow_0(X1,X3)
    | v2_struct_0(X1)
    | ~ r1_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,negated_conjecture,
    ( r1_yellow_0(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_11,plain,
    ( m1_subset_1(esk23_3(X1,X2,X3),u1_struct_0(X1))
    | k1_yellow_0(X1,X2) = k1_yellow_0(X1,X3)
    | v2_struct_0(X1)
    | ~ r1_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_12,plain,
    ( r2_lattice3(X1,k3_waybel_0(X1,X2),X3)
    | v2_struct_0(X1)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_14,negated_conjecture,
    ( v4_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_15,negated_conjecture,
    ( v3_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_16,plain,
    ( r2_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r2_lattice3(X1,k3_waybel_0(X1,X2),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_17,negated_conjecture,
    ( k1_yellow_0(esk1_0,esk2_0) = k1_yellow_0(esk1_0,X1)
    | r2_lattice3(esk1_0,esk2_0,esk23_3(esk1_0,esk2_0,X1))
    | r2_lattice3(esk1_0,X1,esk23_3(esk1_0,esk2_0,X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_8]),c_0_9])]),c_0_10])).

cnf(c_0_18,negated_conjecture,
    ( k1_yellow_0(esk1_0,esk2_0) = k1_yellow_0(esk1_0,X1)
    | m1_subset_1(esk23_3(esk1_0,esk2_0,X1),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_8]),c_0_9])]),c_0_10])).

cnf(c_0_19,plain,
    ( k1_yellow_0(X1,X2) = k1_yellow_0(X1,X3)
    | v2_struct_0(X1)
    | ~ r2_lattice3(X1,X2,esk23_3(X1,X2,X3))
    | ~ r2_lattice3(X1,X3,esk23_3(X1,X2,X3))
    | ~ r1_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_20,negated_conjecture,
    ( r2_lattice3(esk1_0,k3_waybel_0(esk1_0,esk2_0),X1)
    | ~ r2_lattice3(esk1_0,esk2_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_9]),c_0_14]),c_0_15])]),c_0_10])).

cnf(c_0_21,negated_conjecture,
    ( k1_yellow_0(esk1_0,k3_waybel_0(esk1_0,X1)) = k1_yellow_0(esk1_0,esk2_0)
    | r2_lattice3(esk1_0,esk2_0,esk23_3(esk1_0,esk2_0,k3_waybel_0(esk1_0,X1)))
    | r2_lattice3(esk1_0,X1,esk23_3(esk1_0,esk2_0,k3_waybel_0(esk1_0,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_9]),c_0_14]),c_0_15])]),c_0_10]),c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( k1_yellow_0(esk1_0,esk2_0) != k1_yellow_0(esk1_0,k3_waybel_0(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_23,negated_conjecture,
    ( k1_yellow_0(esk1_0,X1) = k1_yellow_0(esk1_0,k3_waybel_0(esk1_0,esk2_0))
    | ~ r2_lattice3(esk1_0,esk2_0,esk23_3(esk1_0,X1,k3_waybel_0(esk1_0,esk2_0)))
    | ~ r2_lattice3(esk1_0,X1,esk23_3(esk1_0,X1,k3_waybel_0(esk1_0,esk2_0)))
    | ~ r1_yellow_0(esk1_0,X1)
    | ~ m1_subset_1(esk23_3(esk1_0,X1,k3_waybel_0(esk1_0,esk2_0)),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_9])]),c_0_10])).

cnf(c_0_24,negated_conjecture,
    ( r2_lattice3(esk1_0,esk2_0,esk23_3(esk1_0,esk2_0,k3_waybel_0(esk1_0,esk2_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_13]),c_0_22])).

cnf(c_0_25,negated_conjecture,
    ( ~ m1_subset_1(esk23_3(esk1_0,esk2_0,k3_waybel_0(esk1_0,esk2_0)),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_24]),c_0_8])]),c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_18]),c_0_22]),
    [proof]).
%------------------------------------------------------------------------------
