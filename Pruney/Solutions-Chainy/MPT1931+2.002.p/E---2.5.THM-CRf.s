%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:11 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 373 expanded)
%              Number of clauses        :   35 ( 143 expanded)
%              Number of leaves         :    6 (  91 expanded)
%              Depth                    :   23
%              Number of atoms          :  202 (2017 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   35 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(d11_waybel_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3] :
              ( r1_waybel_0(X1,X2,X3)
            <=> ? [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X2))
                  & ! [X5] :
                      ( m1_subset_1(X5,u1_struct_0(X2))
                     => ( r1_orders_2(X2,X4,X5)
                       => r2_hidden(k2_waybel_0(X1,X2,X5),X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_waybel_0)).

fof(t29_yellow_6,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v4_orders_2(X2)
            & v7_waybel_0(X2)
            & l1_waybel_0(X2,X1) )
         => r1_waybel_0(X1,X2,u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_yellow_6)).

fof(dt_k2_waybel_0,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1)
        & ~ v2_struct_0(X2)
        & l1_waybel_0(X2,X1)
        & m1_subset_1(X3,u1_struct_0(X2)) )
     => m1_subset_1(k2_waybel_0(X1,X2,X3),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_waybel_0)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(c_0_6,plain,(
    ! [X10,X11] :
      ( ( ~ m1_subset_1(X11,X10)
        | r2_hidden(X11,X10)
        | v1_xboole_0(X10) )
      & ( ~ r2_hidden(X11,X10)
        | m1_subset_1(X11,X10)
        | v1_xboole_0(X10) )
      & ( ~ m1_subset_1(X11,X10)
        | v1_xboole_0(X11)
        | ~ v1_xboole_0(X10) )
      & ( ~ v1_xboole_0(X11)
        | m1_subset_1(X11,X10)
        | ~ v1_xboole_0(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_7,plain,(
    ! [X6,X7,X8] :
      ( ( ~ v1_xboole_0(X6)
        | ~ r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_1(X8),X8)
        | v1_xboole_0(X8) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_8,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_11,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( m1_subset_1(X1,X2)
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_13,plain,
    ( m1_subset_1(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_14,plain,
    ( m1_subset_1(esk1_1(X1),X1)
    | m1_subset_1(X2,X1)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

fof(c_0_15,plain,(
    ! [X13,X14,X15,X17,X18,X19] :
      ( ( m1_subset_1(esk2_3(X13,X14,X15),u1_struct_0(X14))
        | ~ r1_waybel_0(X13,X14,X15)
        | v2_struct_0(X14)
        | ~ l1_waybel_0(X14,X13)
        | v2_struct_0(X13)
        | ~ l1_struct_0(X13) )
      & ( ~ m1_subset_1(X17,u1_struct_0(X14))
        | ~ r1_orders_2(X14,esk2_3(X13,X14,X15),X17)
        | r2_hidden(k2_waybel_0(X13,X14,X17),X15)
        | ~ r1_waybel_0(X13,X14,X15)
        | v2_struct_0(X14)
        | ~ l1_waybel_0(X14,X13)
        | v2_struct_0(X13)
        | ~ l1_struct_0(X13) )
      & ( m1_subset_1(esk3_4(X13,X14,X18,X19),u1_struct_0(X14))
        | ~ m1_subset_1(X19,u1_struct_0(X14))
        | r1_waybel_0(X13,X14,X18)
        | v2_struct_0(X14)
        | ~ l1_waybel_0(X14,X13)
        | v2_struct_0(X13)
        | ~ l1_struct_0(X13) )
      & ( r1_orders_2(X14,X19,esk3_4(X13,X14,X18,X19))
        | ~ m1_subset_1(X19,u1_struct_0(X14))
        | r1_waybel_0(X13,X14,X18)
        | v2_struct_0(X14)
        | ~ l1_waybel_0(X14,X13)
        | v2_struct_0(X13)
        | ~ l1_struct_0(X13) )
      & ( ~ r2_hidden(k2_waybel_0(X13,X14,esk3_4(X13,X14,X18,X19)),X18)
        | ~ m1_subset_1(X19,u1_struct_0(X14))
        | r1_waybel_0(X13,X14,X18)
        | v2_struct_0(X14)
        | ~ l1_waybel_0(X14,X13)
        | v2_struct_0(X13)
        | ~ l1_struct_0(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d11_waybel_0])])])])])])])).

cnf(c_0_16,plain,
    ( m1_subset_1(esk1_1(X1),X1)
    | m1_subset_1(esk1_1(X2),X2)
    | m1_subset_1(X1,X2) ),
    inference(spm,[status(thm)],[c_0_14,c_0_13])).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_struct_0(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & v4_orders_2(X2)
              & v7_waybel_0(X2)
              & l1_waybel_0(X2,X1) )
           => r1_waybel_0(X1,X2,u1_struct_0(X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t29_yellow_6])).

cnf(c_0_18,plain,
    ( m1_subset_1(esk3_4(X1,X2,X3,X4),u1_struct_0(X2))
    | r1_waybel_0(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,plain,
    ( m1_subset_1(esk1_1(X1),X1)
    | m1_subset_1(X1,X1) ),
    inference(ef,[status(thm)],[c_0_16])).

fof(c_0_20,negated_conjecture,
    ( ~ v2_struct_0(esk4_0)
    & l1_struct_0(esk4_0)
    & ~ v2_struct_0(esk5_0)
    & v4_orders_2(esk5_0)
    & v7_waybel_0(esk5_0)
    & l1_waybel_0(esk5_0,esk4_0)
    & ~ r1_waybel_0(esk4_0,esk5_0,u1_struct_0(esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_17])])])])).

cnf(c_0_21,plain,
    ( r1_waybel_0(X1,X2,X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(esk3_4(X1,X2,X3,esk1_1(u1_struct_0(X2))),u1_struct_0(X2))
    | m1_subset_1(u1_struct_0(X2),u1_struct_0(X2))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_22,negated_conjecture,
    ( l1_waybel_0(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_23,negated_conjecture,
    ( l1_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_26,plain,(
    ! [X21,X22,X23] :
      ( v2_struct_0(X21)
      | ~ l1_struct_0(X21)
      | v2_struct_0(X22)
      | ~ l1_waybel_0(X22,X21)
      | ~ m1_subset_1(X23,u1_struct_0(X22))
      | m1_subset_1(k2_waybel_0(X21,X22,X23),u1_struct_0(X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k2_waybel_0])])])).

cnf(c_0_27,negated_conjecture,
    ( ~ r1_waybel_0(esk4_0,esk5_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( r1_waybel_0(esk4_0,esk5_0,X1)
    | m1_subset_1(esk3_4(esk4_0,esk5_0,X1,esk1_1(u1_struct_0(esk5_0))),u1_struct_0(esk5_0))
    | m1_subset_1(u1_struct_0(esk5_0),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])]),c_0_24]),c_0_25])).

cnf(c_0_29,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(k2_waybel_0(X1,X2,X3),u1_struct_0(X1))
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk3_4(esk4_0,esk5_0,u1_struct_0(esk4_0),esk1_1(u1_struct_0(esk5_0))),u1_struct_0(esk5_0))
    | m1_subset_1(u1_struct_0(esk5_0),u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_31,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_subset_1(k2_waybel_0(X1,esk5_0,esk3_4(esk4_0,esk5_0,u1_struct_0(esk4_0),esk1_1(u1_struct_0(esk5_0)))),u1_struct_0(X1))
    | m1_subset_1(u1_struct_0(esk5_0),u1_struct_0(esk5_0))
    | ~ l1_waybel_0(esk5_0,X1)
    | ~ l1_struct_0(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_25])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(k2_waybel_0(esk4_0,esk5_0,esk3_4(esk4_0,esk5_0,u1_struct_0(esk4_0),esk1_1(u1_struct_0(esk5_0)))),u1_struct_0(esk4_0))
    | m1_subset_1(u1_struct_0(esk5_0),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_22]),c_0_23])]),c_0_24])).

fof(c_0_34,plain,(
    ! [X12] :
      ( v2_struct_0(X12)
      | ~ l1_struct_0(X12)
      | ~ v1_xboole_0(u1_struct_0(X12)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_35,plain,
    ( r1_waybel_0(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r2_hidden(k2_waybel_0(X1,X2,esk3_4(X1,X2,X3,X4)),X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk5_0),u1_struct_0(esk5_0))
    | r2_hidden(k2_waybel_0(esk4_0,esk5_0,esk3_4(esk4_0,esk5_0,u1_struct_0(esk4_0),esk1_1(u1_struct_0(esk5_0)))),u1_struct_0(esk4_0))
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_37,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk5_0),u1_struct_0(esk5_0))
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_22]),c_0_23])]),c_0_27]),c_0_25]),c_0_24]),c_0_19])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk5_0),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_23])]),c_0_24])).

cnf(c_0_40,negated_conjecture,
    ( r1_waybel_0(X1,esk5_0,X2)
    | v2_struct_0(X1)
    | m1_subset_1(esk3_4(X1,esk5_0,X2,u1_struct_0(esk5_0)),u1_struct_0(esk5_0))
    | ~ l1_waybel_0(esk5_0,X1)
    | ~ l1_struct_0(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_39]),c_0_25])).

cnf(c_0_41,negated_conjecture,
    ( r1_waybel_0(esk4_0,esk5_0,X1)
    | m1_subset_1(esk3_4(esk4_0,esk5_0,X1,u1_struct_0(esk5_0)),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(esk3_4(esk4_0,esk5_0,u1_struct_0(esk4_0),u1_struct_0(esk5_0)),u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_41])).

cnf(c_0_43,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_subset_1(k2_waybel_0(X1,esk5_0,esk3_4(esk4_0,esk5_0,u1_struct_0(esk4_0),u1_struct_0(esk5_0))),u1_struct_0(X1))
    | ~ l1_waybel_0(esk5_0,X1)
    | ~ l1_struct_0(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_42]),c_0_25])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(k2_waybel_0(esk4_0,esk5_0,esk3_4(esk4_0,esk5_0,u1_struct_0(esk4_0),u1_struct_0(esk5_0))),u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(k2_waybel_0(esk4_0,esk5_0,esk3_4(esk4_0,esk5_0,u1_struct_0(esk4_0),u1_struct_0(esk5_0))),u1_struct_0(esk4_0))
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_44])).

cnf(c_0_46,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_45]),c_0_22]),c_0_23]),c_0_39])]),c_0_27]),c_0_25]),c_0_24])).

cnf(c_0_47,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_46]),c_0_23])]),c_0_24]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:54:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S03EA
% 0.13/0.38  # and selection function SelectLComplex.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.027 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 0.13/0.38  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.13/0.38  fof(d11_waybel_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(r1_waybel_0(X1,X2,X3)<=>?[X4]:(m1_subset_1(X4,u1_struct_0(X2))&![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>(r1_orders_2(X2,X4,X5)=>r2_hidden(k2_waybel_0(X1,X2,X5),X3))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_waybel_0)).
% 0.13/0.38  fof(t29_yellow_6, conjecture, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>r1_waybel_0(X1,X2,u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_yellow_6)).
% 0.13/0.38  fof(dt_k2_waybel_0, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&l1_struct_0(X1))&~(v2_struct_0(X2)))&l1_waybel_0(X2,X1))&m1_subset_1(X3,u1_struct_0(X2)))=>m1_subset_1(k2_waybel_0(X1,X2,X3),u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_waybel_0)).
% 0.13/0.38  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.13/0.38  fof(c_0_6, plain, ![X10, X11]:(((~m1_subset_1(X11,X10)|r2_hidden(X11,X10)|v1_xboole_0(X10))&(~r2_hidden(X11,X10)|m1_subset_1(X11,X10)|v1_xboole_0(X10)))&((~m1_subset_1(X11,X10)|v1_xboole_0(X11)|~v1_xboole_0(X10))&(~v1_xboole_0(X11)|m1_subset_1(X11,X10)|~v1_xboole_0(X10)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.13/0.38  fof(c_0_7, plain, ![X6, X7, X8]:((~v1_xboole_0(X6)|~r2_hidden(X7,X6))&(r2_hidden(esk1_1(X8),X8)|v1_xboole_0(X8))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.13/0.38  cnf(c_0_8, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.38  cnf(c_0_9, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.38  cnf(c_0_10, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(csr,[status(thm)],[c_0_8, c_0_9])).
% 0.13/0.38  cnf(c_0_11, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.38  cnf(c_0_12, plain, (m1_subset_1(X1,X2)|~v1_xboole_0(X1)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.38  cnf(c_0_13, plain, (m1_subset_1(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.13/0.38  cnf(c_0_14, plain, (m1_subset_1(esk1_1(X1),X1)|m1_subset_1(X2,X1)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.13/0.38  fof(c_0_15, plain, ![X13, X14, X15, X17, X18, X19]:(((m1_subset_1(esk2_3(X13,X14,X15),u1_struct_0(X14))|~r1_waybel_0(X13,X14,X15)|(v2_struct_0(X14)|~l1_waybel_0(X14,X13))|(v2_struct_0(X13)|~l1_struct_0(X13)))&(~m1_subset_1(X17,u1_struct_0(X14))|(~r1_orders_2(X14,esk2_3(X13,X14,X15),X17)|r2_hidden(k2_waybel_0(X13,X14,X17),X15))|~r1_waybel_0(X13,X14,X15)|(v2_struct_0(X14)|~l1_waybel_0(X14,X13))|(v2_struct_0(X13)|~l1_struct_0(X13))))&((m1_subset_1(esk3_4(X13,X14,X18,X19),u1_struct_0(X14))|~m1_subset_1(X19,u1_struct_0(X14))|r1_waybel_0(X13,X14,X18)|(v2_struct_0(X14)|~l1_waybel_0(X14,X13))|(v2_struct_0(X13)|~l1_struct_0(X13)))&((r1_orders_2(X14,X19,esk3_4(X13,X14,X18,X19))|~m1_subset_1(X19,u1_struct_0(X14))|r1_waybel_0(X13,X14,X18)|(v2_struct_0(X14)|~l1_waybel_0(X14,X13))|(v2_struct_0(X13)|~l1_struct_0(X13)))&(~r2_hidden(k2_waybel_0(X13,X14,esk3_4(X13,X14,X18,X19)),X18)|~m1_subset_1(X19,u1_struct_0(X14))|r1_waybel_0(X13,X14,X18)|(v2_struct_0(X14)|~l1_waybel_0(X14,X13))|(v2_struct_0(X13)|~l1_struct_0(X13)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d11_waybel_0])])])])])])])).
% 0.13/0.38  cnf(c_0_16, plain, (m1_subset_1(esk1_1(X1),X1)|m1_subset_1(esk1_1(X2),X2)|m1_subset_1(X1,X2)), inference(spm,[status(thm)],[c_0_14, c_0_13])).
% 0.13/0.38  fof(c_0_17, negated_conjecture, ~(![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>r1_waybel_0(X1,X2,u1_struct_0(X1))))), inference(assume_negation,[status(cth)],[t29_yellow_6])).
% 0.13/0.38  cnf(c_0_18, plain, (m1_subset_1(esk3_4(X1,X2,X3,X4),u1_struct_0(X2))|r1_waybel_0(X1,X2,X3)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_subset_1(X4,u1_struct_0(X2))|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_19, plain, (m1_subset_1(esk1_1(X1),X1)|m1_subset_1(X1,X1)), inference(ef,[status(thm)],[c_0_16])).
% 0.13/0.38  fof(c_0_20, negated_conjecture, ((~v2_struct_0(esk4_0)&l1_struct_0(esk4_0))&((((~v2_struct_0(esk5_0)&v4_orders_2(esk5_0))&v7_waybel_0(esk5_0))&l1_waybel_0(esk5_0,esk4_0))&~r1_waybel_0(esk4_0,esk5_0,u1_struct_0(esk4_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_17])])])])).
% 0.13/0.38  cnf(c_0_21, plain, (r1_waybel_0(X1,X2,X3)|v2_struct_0(X1)|v2_struct_0(X2)|m1_subset_1(esk3_4(X1,X2,X3,esk1_1(u1_struct_0(X2))),u1_struct_0(X2))|m1_subset_1(u1_struct_0(X2),u1_struct_0(X2))|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.13/0.38  cnf(c_0_22, negated_conjecture, (l1_waybel_0(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.38  cnf(c_0_23, negated_conjecture, (l1_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.38  cnf(c_0_24, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.38  cnf(c_0_25, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.38  fof(c_0_26, plain, ![X21, X22, X23]:(v2_struct_0(X21)|~l1_struct_0(X21)|v2_struct_0(X22)|~l1_waybel_0(X22,X21)|~m1_subset_1(X23,u1_struct_0(X22))|m1_subset_1(k2_waybel_0(X21,X22,X23),u1_struct_0(X21))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k2_waybel_0])])])).
% 0.13/0.38  cnf(c_0_27, negated_conjecture, (~r1_waybel_0(esk4_0,esk5_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.38  cnf(c_0_28, negated_conjecture, (r1_waybel_0(esk4_0,esk5_0,X1)|m1_subset_1(esk3_4(esk4_0,esk5_0,X1,esk1_1(u1_struct_0(esk5_0))),u1_struct_0(esk5_0))|m1_subset_1(u1_struct_0(esk5_0),u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23])]), c_0_24]), c_0_25])).
% 0.13/0.38  cnf(c_0_29, plain, (v2_struct_0(X1)|v2_struct_0(X2)|m1_subset_1(k2_waybel_0(X1,X2,X3),u1_struct_0(X1))|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)|~m1_subset_1(X3,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.38  cnf(c_0_30, negated_conjecture, (m1_subset_1(esk3_4(esk4_0,esk5_0,u1_struct_0(esk4_0),esk1_1(u1_struct_0(esk5_0))),u1_struct_0(esk5_0))|m1_subset_1(u1_struct_0(esk5_0),u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.13/0.38  cnf(c_0_31, negated_conjecture, (v2_struct_0(X1)|m1_subset_1(k2_waybel_0(X1,esk5_0,esk3_4(esk4_0,esk5_0,u1_struct_0(esk4_0),esk1_1(u1_struct_0(esk5_0)))),u1_struct_0(X1))|m1_subset_1(u1_struct_0(esk5_0),u1_struct_0(esk5_0))|~l1_waybel_0(esk5_0,X1)|~l1_struct_0(X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_25])).
% 0.13/0.38  cnf(c_0_32, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.38  cnf(c_0_33, negated_conjecture, (m1_subset_1(k2_waybel_0(esk4_0,esk5_0,esk3_4(esk4_0,esk5_0,u1_struct_0(esk4_0),esk1_1(u1_struct_0(esk5_0)))),u1_struct_0(esk4_0))|m1_subset_1(u1_struct_0(esk5_0),u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_22]), c_0_23])]), c_0_24])).
% 0.13/0.38  fof(c_0_34, plain, ![X12]:(v2_struct_0(X12)|~l1_struct_0(X12)|~v1_xboole_0(u1_struct_0(X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.13/0.38  cnf(c_0_35, plain, (r1_waybel_0(X1,X2,X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r2_hidden(k2_waybel_0(X1,X2,esk3_4(X1,X2,X3,X4)),X3)|~m1_subset_1(X4,u1_struct_0(X2))|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_36, negated_conjecture, (m1_subset_1(u1_struct_0(esk5_0),u1_struct_0(esk5_0))|r2_hidden(k2_waybel_0(esk4_0,esk5_0,esk3_4(esk4_0,esk5_0,u1_struct_0(esk4_0),esk1_1(u1_struct_0(esk5_0)))),u1_struct_0(esk4_0))|v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.13/0.38  cnf(c_0_37, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.13/0.38  cnf(c_0_38, negated_conjecture, (m1_subset_1(u1_struct_0(esk5_0),u1_struct_0(esk5_0))|v1_xboole_0(u1_struct_0(esk4_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_22]), c_0_23])]), c_0_27]), c_0_25]), c_0_24]), c_0_19])).
% 0.13/0.38  cnf(c_0_39, negated_conjecture, (m1_subset_1(u1_struct_0(esk5_0),u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_23])]), c_0_24])).
% 0.13/0.38  cnf(c_0_40, negated_conjecture, (r1_waybel_0(X1,esk5_0,X2)|v2_struct_0(X1)|m1_subset_1(esk3_4(X1,esk5_0,X2,u1_struct_0(esk5_0)),u1_struct_0(esk5_0))|~l1_waybel_0(esk5_0,X1)|~l1_struct_0(X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_39]), c_0_25])).
% 0.13/0.38  cnf(c_0_41, negated_conjecture, (r1_waybel_0(esk4_0,esk5_0,X1)|m1_subset_1(esk3_4(esk4_0,esk5_0,X1,u1_struct_0(esk5_0)),u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_22]), c_0_23])]), c_0_24])).
% 0.13/0.38  cnf(c_0_42, negated_conjecture, (m1_subset_1(esk3_4(esk4_0,esk5_0,u1_struct_0(esk4_0),u1_struct_0(esk5_0)),u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_27, c_0_41])).
% 0.13/0.38  cnf(c_0_43, negated_conjecture, (v2_struct_0(X1)|m1_subset_1(k2_waybel_0(X1,esk5_0,esk3_4(esk4_0,esk5_0,u1_struct_0(esk4_0),u1_struct_0(esk5_0))),u1_struct_0(X1))|~l1_waybel_0(esk5_0,X1)|~l1_struct_0(X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_42]), c_0_25])).
% 0.13/0.38  cnf(c_0_44, negated_conjecture, (m1_subset_1(k2_waybel_0(esk4_0,esk5_0,esk3_4(esk4_0,esk5_0,u1_struct_0(esk4_0),u1_struct_0(esk5_0))),u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_22]), c_0_23])]), c_0_24])).
% 0.13/0.38  cnf(c_0_45, negated_conjecture, (r2_hidden(k2_waybel_0(esk4_0,esk5_0,esk3_4(esk4_0,esk5_0,u1_struct_0(esk4_0),u1_struct_0(esk5_0))),u1_struct_0(esk4_0))|v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_32, c_0_44])).
% 0.13/0.38  cnf(c_0_46, negated_conjecture, (v1_xboole_0(u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_45]), c_0_22]), c_0_23]), c_0_39])]), c_0_27]), c_0_25]), c_0_24])).
% 0.13/0.38  cnf(c_0_47, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_46]), c_0_23])]), c_0_24]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 48
% 0.13/0.38  # Proof object clause steps            : 35
% 0.13/0.38  # Proof object formula steps           : 13
% 0.13/0.38  # Proof object conjectures             : 23
% 0.13/0.38  # Proof object clause conjectures      : 20
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 14
% 0.13/0.38  # Proof object initial formulas used   : 6
% 0.13/0.38  # Proof object generating inferences   : 20
% 0.13/0.38  # Proof object simplifying inferences  : 37
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 6
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 20
% 0.13/0.38  # Removed in clause preprocessing      : 0
% 0.13/0.38  # Initial clauses in saturation        : 20
% 0.13/0.38  # Processed clauses                    : 139
% 0.13/0.38  # ...of these trivial                  : 0
% 0.13/0.38  # ...subsumed                          : 25
% 0.13/0.38  # ...remaining for further processing  : 114
% 0.13/0.38  # Other redundant clauses eliminated   : 0
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 2
% 0.13/0.38  # Backward-rewritten                   : 28
% 0.13/0.38  # Generated clauses                    : 203
% 0.13/0.38  # ...of the previous two non-trivial   : 182
% 0.13/0.38  # Contextual simplify-reflections      : 2
% 0.13/0.38  # Paramodulations                      : 199
% 0.13/0.38  # Factorizations                       : 4
% 0.13/0.38  # Equation resolutions                 : 0
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 64
% 0.13/0.38  #    Positive orientable unit clauses  : 10
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 3
% 0.13/0.38  #    Non-unit-clauses                  : 51
% 0.13/0.38  # Current number of unprocessed clauses: 58
% 0.13/0.38  # ...number of literals in the above   : 322
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 50
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 1012
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 360
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 29
% 0.13/0.38  # Unit Clause-clause subsumption calls : 56
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 9
% 0.13/0.38  # BW rewrite match successes           : 3
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 6744
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.039 s
% 0.13/0.38  # System time              : 0.002 s
% 0.13/0.38  # Total time               : 0.041 s
% 0.13/0.38  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
