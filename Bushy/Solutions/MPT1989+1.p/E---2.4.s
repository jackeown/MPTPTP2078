%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : waybel_7__t38_waybel_7.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:06 EDT 2019

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 169 expanded)
%              Number of clauses        :   28 (  52 expanded)
%              Number of leaves         :    9 (  42 expanded)
%              Depth                    :    8
%              Number of atoms          :  284 (1188 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :   24 (   6 average)
%              Maximal clause size      :   68 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t38_waybel_7,conjecture,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & v1_lattice3(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( v5_waybel_6(X2,X1)
           => v4_waybel_7(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t38_waybel_7.p',t38_waybel_7)).

fof(d6_waybel_7,axiom,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & v1_lattice3(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( v4_waybel_7(X2,X1)
          <=> ? [X3] :
                ( ~ v1_xboole_0(X3)
                & v1_waybel_0(X3,X1)
                & v12_waybel_0(X3,X1)
                & v1_waybel_7(X3,X1)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                & X2 = k1_yellow_0(X1,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t38_waybel_7.p',d6_waybel_7)).

fof(dt_k1_yellow_0,axiom,(
    ! [X1,X2] :
      ( l1_orders_2(X1)
     => m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t38_waybel_7.p',dt_k1_yellow_0)).

fof(dt_k5_waybel_0,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => m1_subset_1(k5_waybel_0(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t38_waybel_7.p',dt_k5_waybel_0)).

fof(t37_waybel_7,axiom,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & v1_lattice3(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( v5_waybel_6(X2,X1)
           => v1_waybel_7(k5_waybel_0(X1,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t38_waybel_7.p',t37_waybel_7)).

fof(fc8_waybel_0,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ~ v1_xboole_0(k5_waybel_0(X1,X2))
        & v1_waybel_0(k5_waybel_0(X1,X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t38_waybel_7.p',fc8_waybel_0)).

fof(fc12_waybel_0,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v4_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => v12_waybel_0(k5_waybel_0(X1,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t38_waybel_7.p',fc12_waybel_0)).

fof(t34_waybel_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( r1_yellow_0(X1,k5_waybel_0(X1,X2))
            & k1_yellow_0(X1,k5_waybel_0(X1,X2)) = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t38_waybel_7.p',t34_waybel_0)).

fof(cc2_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v2_lattice3(X1)
       => ~ v2_struct_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t38_waybel_7.p',cc2_lattice3)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( ( v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & v1_lattice3(X1)
          & v2_lattice3(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ( v5_waybel_6(X2,X1)
             => v4_waybel_7(X2,X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t38_waybel_7])).

fof(c_0_10,plain,(
    ! [X8,X9,X11] :
      ( ( ~ v1_xboole_0(esk3_2(X8,X9))
        | ~ v4_waybel_7(X9,X8)
        | ~ m1_subset_1(X9,u1_struct_0(X8))
        | ~ v3_orders_2(X8)
        | ~ v4_orders_2(X8)
        | ~ v5_orders_2(X8)
        | ~ v1_lattice3(X8)
        | ~ v2_lattice3(X8)
        | ~ l1_orders_2(X8) )
      & ( v1_waybel_0(esk3_2(X8,X9),X8)
        | ~ v4_waybel_7(X9,X8)
        | ~ m1_subset_1(X9,u1_struct_0(X8))
        | ~ v3_orders_2(X8)
        | ~ v4_orders_2(X8)
        | ~ v5_orders_2(X8)
        | ~ v1_lattice3(X8)
        | ~ v2_lattice3(X8)
        | ~ l1_orders_2(X8) )
      & ( v12_waybel_0(esk3_2(X8,X9),X8)
        | ~ v4_waybel_7(X9,X8)
        | ~ m1_subset_1(X9,u1_struct_0(X8))
        | ~ v3_orders_2(X8)
        | ~ v4_orders_2(X8)
        | ~ v5_orders_2(X8)
        | ~ v1_lattice3(X8)
        | ~ v2_lattice3(X8)
        | ~ l1_orders_2(X8) )
      & ( v1_waybel_7(esk3_2(X8,X9),X8)
        | ~ v4_waybel_7(X9,X8)
        | ~ m1_subset_1(X9,u1_struct_0(X8))
        | ~ v3_orders_2(X8)
        | ~ v4_orders_2(X8)
        | ~ v5_orders_2(X8)
        | ~ v1_lattice3(X8)
        | ~ v2_lattice3(X8)
        | ~ l1_orders_2(X8) )
      & ( m1_subset_1(esk3_2(X8,X9),k1_zfmisc_1(u1_struct_0(X8)))
        | ~ v4_waybel_7(X9,X8)
        | ~ m1_subset_1(X9,u1_struct_0(X8))
        | ~ v3_orders_2(X8)
        | ~ v4_orders_2(X8)
        | ~ v5_orders_2(X8)
        | ~ v1_lattice3(X8)
        | ~ v2_lattice3(X8)
        | ~ l1_orders_2(X8) )
      & ( X9 = k1_yellow_0(X8,esk3_2(X8,X9))
        | ~ v4_waybel_7(X9,X8)
        | ~ m1_subset_1(X9,u1_struct_0(X8))
        | ~ v3_orders_2(X8)
        | ~ v4_orders_2(X8)
        | ~ v5_orders_2(X8)
        | ~ v1_lattice3(X8)
        | ~ v2_lattice3(X8)
        | ~ l1_orders_2(X8) )
      & ( v1_xboole_0(X11)
        | ~ v1_waybel_0(X11,X8)
        | ~ v12_waybel_0(X11,X8)
        | ~ v1_waybel_7(X11,X8)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X8)))
        | X9 != k1_yellow_0(X8,X11)
        | v4_waybel_7(X9,X8)
        | ~ m1_subset_1(X9,u1_struct_0(X8))
        | ~ v3_orders_2(X8)
        | ~ v4_orders_2(X8)
        | ~ v5_orders_2(X8)
        | ~ v1_lattice3(X8)
        | ~ v2_lattice3(X8)
        | ~ l1_orders_2(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d6_waybel_7])])])])])])).

fof(c_0_11,plain,(
    ! [X12,X13] :
      ( ~ l1_orders_2(X12)
      | m1_subset_1(k1_yellow_0(X12,X13),u1_struct_0(X12)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_yellow_0])])).

fof(c_0_12,plain,(
    ! [X16,X17] :
      ( v2_struct_0(X16)
      | ~ l1_orders_2(X16)
      | ~ m1_subset_1(X17,u1_struct_0(X16))
      | m1_subset_1(k5_waybel_0(X16,X17),k1_zfmisc_1(u1_struct_0(X16))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_waybel_0])])])).

fof(c_0_13,negated_conjecture,
    ( v3_orders_2(esk1_0)
    & v4_orders_2(esk1_0)
    & v5_orders_2(esk1_0)
    & v1_lattice3(esk1_0)
    & v2_lattice3(esk1_0)
    & l1_orders_2(esk1_0)
    & m1_subset_1(esk2_0,u1_struct_0(esk1_0))
    & v5_waybel_6(esk2_0,esk1_0)
    & ~ v4_waybel_7(esk2_0,esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

fof(c_0_14,plain,(
    ! [X33,X34] :
      ( ~ v3_orders_2(X33)
      | ~ v4_orders_2(X33)
      | ~ v5_orders_2(X33)
      | ~ v1_lattice3(X33)
      | ~ v2_lattice3(X33)
      | ~ l1_orders_2(X33)
      | ~ m1_subset_1(X34,u1_struct_0(X33))
      | ~ v5_waybel_6(X34,X33)
      | v1_waybel_7(k5_waybel_0(X33,X34),X33) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_waybel_7])])])).

fof(c_0_15,plain,(
    ! [X51,X52] :
      ( ( ~ v1_xboole_0(k5_waybel_0(X51,X52))
        | v2_struct_0(X51)
        | ~ v3_orders_2(X51)
        | ~ l1_orders_2(X51)
        | ~ m1_subset_1(X52,u1_struct_0(X51)) )
      & ( v1_waybel_0(k5_waybel_0(X51,X52),X51)
        | v2_struct_0(X51)
        | ~ v3_orders_2(X51)
        | ~ l1_orders_2(X51)
        | ~ m1_subset_1(X52,u1_struct_0(X51)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc8_waybel_0])])])])).

fof(c_0_16,plain,(
    ! [X49,X50] :
      ( v2_struct_0(X49)
      | ~ v4_orders_2(X49)
      | ~ l1_orders_2(X49)
      | ~ m1_subset_1(X50,u1_struct_0(X49))
      | v12_waybel_0(k5_waybel_0(X49,X50),X49) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc12_waybel_0])])])).

cnf(c_0_17,plain,
    ( v1_xboole_0(X1)
    | v4_waybel_7(X3,X2)
    | ~ v1_waybel_0(X1,X2)
    | ~ v12_waybel_0(X1,X2)
    | ~ v1_waybel_7(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | X3 != k1_yellow_0(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ v1_lattice3(X2)
    | ~ v2_lattice3(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k5_waybel_0(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( v1_waybel_7(k5_waybel_0(X1,X2),X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_waybel_6(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,negated_conjecture,
    ( v5_waybel_6(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_24,negated_conjecture,
    ( v2_lattice3(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_25,negated_conjecture,
    ( v1_lattice3(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_26,negated_conjecture,
    ( v5_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_27,negated_conjecture,
    ( v4_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_28,negated_conjecture,
    ( v3_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_29,plain,
    ( v1_waybel_0(k5_waybel_0(X1,X2),X1)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_30,plain,
    ( v2_struct_0(X1)
    | v12_waybel_0(k5_waybel_0(X1,X2),X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_31,plain,(
    ! [X31,X32] :
      ( ( r1_yellow_0(X31,k5_waybel_0(X31,X32))
        | ~ m1_subset_1(X32,u1_struct_0(X31))
        | v2_struct_0(X31)
        | ~ v3_orders_2(X31)
        | ~ v4_orders_2(X31)
        | ~ v5_orders_2(X31)
        | ~ l1_orders_2(X31) )
      & ( k1_yellow_0(X31,k5_waybel_0(X31,X32)) = X32
        | ~ m1_subset_1(X32,u1_struct_0(X31))
        | v2_struct_0(X31)
        | ~ v3_orders_2(X31)
        | ~ v4_orders_2(X31)
        | ~ v5_orders_2(X31)
        | ~ l1_orders_2(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_waybel_0])])])])])).

cnf(c_0_32,plain,
    ( v1_xboole_0(X1)
    | v4_waybel_7(k1_yellow_0(X2,X1),X2)
    | ~ v1_waybel_7(X1,X2)
    | ~ v12_waybel_0(X1,X2)
    | ~ v1_waybel_0(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2)
    | ~ v2_lattice3(X2)
    | ~ v1_lattice3(X2)
    | ~ v5_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v3_orders_2(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_17]),c_0_18])).

cnf(c_0_33,negated_conjecture,
    ( v2_struct_0(esk1_0)
    | m1_subset_1(k5_waybel_0(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])])).

cnf(c_0_34,negated_conjecture,
    ( v1_waybel_7(k5_waybel_0(esk1_0,esk2_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_20]),c_0_23]),c_0_21]),c_0_24]),c_0_25]),c_0_26]),c_0_27]),c_0_28])])).

cnf(c_0_35,negated_conjecture,
    ( v2_struct_0(esk1_0)
    | v1_waybel_0(k5_waybel_0(esk1_0,esk2_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_20]),c_0_21]),c_0_28])])).

cnf(c_0_36,negated_conjecture,
    ( v2_struct_0(esk1_0)
    | v12_waybel_0(k5_waybel_0(esk1_0,esk2_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_20]),c_0_21]),c_0_27])])).

cnf(c_0_37,plain,
    ( k1_yellow_0(X1,k5_waybel_0(X1,X2)) = X2
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( v2_struct_0(esk1_0)
    | v1_xboole_0(k5_waybel_0(esk1_0,esk2_0))
    | v4_waybel_7(k1_yellow_0(esk1_0,k5_waybel_0(esk1_0,esk2_0)),esk1_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_21]),c_0_24]),c_0_25]),c_0_26]),c_0_27]),c_0_28])]),c_0_35]),c_0_36])).

cnf(c_0_39,negated_conjecture,
    ( k1_yellow_0(esk1_0,k5_waybel_0(esk1_0,esk2_0)) = esk2_0
    | v2_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_20]),c_0_21]),c_0_26]),c_0_27]),c_0_28])])).

cnf(c_0_40,negated_conjecture,
    ( ~ v4_waybel_7(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_41,plain,(
    ! [X48] :
      ( ~ l1_orders_2(X48)
      | ~ v2_lattice3(X48)
      | ~ v2_struct_0(X48) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_lattice3])])])).

cnf(c_0_42,plain,
    ( v2_struct_0(X1)
    | ~ v1_xboole_0(k5_waybel_0(X1,X2))
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_43,negated_conjecture,
    ( v2_struct_0(esk1_0)
    | v1_xboole_0(k5_waybel_0(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40])).

cnf(c_0_44,plain,
    ( ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v2_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_45,negated_conjecture,
    ( v2_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_20]),c_0_21]),c_0_28])])).

cnf(c_0_46,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_21]),c_0_24])]),
    [proof]).
%------------------------------------------------------------------------------
