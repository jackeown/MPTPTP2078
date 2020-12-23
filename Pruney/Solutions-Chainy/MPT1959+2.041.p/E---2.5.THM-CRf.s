%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:29 EST 2020

% Result     : Theorem 0.51s
% Output     : CNFRefutation 0.51s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 256 expanded)
%              Number of clauses        :   39 ( 107 expanded)
%              Number of leaves         :   12 (  61 expanded)
%              Depth                    :   12
%              Number of atoms          :  240 (1633 expanded)
%              Number of equality atoms :   22 (  73 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t8_waybel_7,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & v1_yellow_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v2_waybel_0(X2,X1)
            & v13_waybel_0(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => ( v1_subset_1(X2,u1_struct_0(X1))
          <=> ~ r2_hidden(k3_yellow_0(X1),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_waybel_7)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(t2_tarski,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
        <=> r2_hidden(X3,X2) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

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

fof(d20_waybel_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v13_waybel_0(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( ( r2_hidden(X3,X2)
                        & r1_orders_2(X1,X3,X4) )
                     => r2_hidden(X4,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_waybel_0)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(d7_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( v1_subset_1(X2,X1)
      <=> X2 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

fof(t44_yellow_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v5_orders_2(X1)
        & v1_yellow_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => r1_orders_2(X1,k3_yellow_0(X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_yellow_0)).

fof(fc14_subset_1,axiom,(
    ! [X1] : ~ v1_subset_1(k2_subset_1(X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc14_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(dt_k3_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => m1_subset_1(k3_yellow_0(X1),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_yellow_0)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & v1_yellow_0(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( ( ~ v1_xboole_0(X2)
              & v2_waybel_0(X2,X1)
              & v13_waybel_0(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
           => ( v1_subset_1(X2,u1_struct_0(X1))
            <=> ~ r2_hidden(k3_yellow_0(X1),X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t8_waybel_7])).

fof(c_0_13,plain,(
    ! [X15,X16,X17] :
      ( ~ m1_subset_1(X16,k1_zfmisc_1(X15))
      | ~ r2_hidden(X17,X16)
      | r2_hidden(X17,X15) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

fof(c_0_14,negated_conjecture,
    ( ~ v2_struct_0(esk5_0)
    & v3_orders_2(esk5_0)
    & v4_orders_2(esk5_0)
    & v5_orders_2(esk5_0)
    & v1_yellow_0(esk5_0)
    & l1_orders_2(esk5_0)
    & ~ v1_xboole_0(esk6_0)
    & v2_waybel_0(esk6_0,esk5_0)
    & v13_waybel_0(esk6_0,esk5_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))
    & ( ~ v1_subset_1(esk6_0,u1_struct_0(esk5_0))
      | r2_hidden(k3_yellow_0(esk5_0),esk6_0) )
    & ( v1_subset_1(esk6_0,u1_struct_0(esk5_0))
      | ~ r2_hidden(k3_yellow_0(esk5_0),esk6_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])).

cnf(c_0_15,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_17,plain,(
    ! [X9,X10] :
      ( ( ~ r2_hidden(esk2_2(X9,X10),X9)
        | ~ r2_hidden(esk2_2(X9,X10),X10)
        | X9 = X10 )
      & ( r2_hidden(esk2_2(X9,X10),X9)
        | r2_hidden(esk2_2(X9,X10),X10)
        | X9 = X10 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).

fof(c_0_18,plain,(
    ! [X12,X13] :
      ( ( ~ m1_subset_1(X13,X12)
        | r2_hidden(X13,X12)
        | v1_xboole_0(X12) )
      & ( ~ r2_hidden(X13,X12)
        | m1_subset_1(X13,X12)
        | v1_xboole_0(X12) )
      & ( ~ m1_subset_1(X13,X12)
        | v1_xboole_0(X13)
        | ~ v1_xboole_0(X12) )
      & ( ~ v1_xboole_0(X13)
        | m1_subset_1(X13,X12)
        | ~ v1_xboole_0(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_19,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(X1,u1_struct_0(esk5_0))
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_21,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r2_hidden(esk2_2(X1,X2),X2)
    | X1 = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_22,plain,(
    ! [X25,X26,X27,X28] :
      ( ( ~ v13_waybel_0(X26,X25)
        | ~ m1_subset_1(X27,u1_struct_0(X25))
        | ~ m1_subset_1(X28,u1_struct_0(X25))
        | ~ r2_hidden(X27,X26)
        | ~ r1_orders_2(X25,X27,X28)
        | r2_hidden(X28,X26)
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ l1_orders_2(X25) )
      & ( m1_subset_1(esk3_2(X25,X26),u1_struct_0(X25))
        | v13_waybel_0(X26,X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ l1_orders_2(X25) )
      & ( m1_subset_1(esk4_2(X25,X26),u1_struct_0(X25))
        | v13_waybel_0(X26,X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ l1_orders_2(X25) )
      & ( r2_hidden(esk3_2(X25,X26),X26)
        | v13_waybel_0(X26,X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ l1_orders_2(X25) )
      & ( r1_orders_2(X25,esk3_2(X25,X26),esk4_2(X25,X26))
        | v13_waybel_0(X26,X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ l1_orders_2(X25) )
      & ( ~ r2_hidden(esk4_2(X25,X26),X26)
        | v13_waybel_0(X26,X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ l1_orders_2(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d20_waybel_0])])])])])).

fof(c_0_23,plain,(
    ! [X19,X20,X21] :
      ( ~ r2_hidden(X19,X20)
      | ~ m1_subset_1(X20,k1_zfmisc_1(X21))
      | m1_subset_1(X19,X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_24,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( esk6_0 = X1
    | r2_hidden(esk2_2(esk6_0,X1),u1_struct_0(esk5_0))
    | r2_hidden(esk2_2(esk6_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_27,plain,
    ( r2_hidden(X4,X1)
    | ~ v13_waybel_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r2_hidden(X3,X1)
    | ~ r1_orders_2(X2,X3,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( u1_struct_0(esk5_0) = esk6_0
    | r2_hidden(esk2_2(esk6_0,u1_struct_0(esk5_0)),u1_struct_0(esk5_0)) ),
    inference(ef,[status(thm)],[c_0_26])).

fof(c_0_31,plain,(
    ! [X31,X32] :
      ( ( ~ v1_subset_1(X32,X31)
        | X32 != X31
        | ~ m1_subset_1(X32,k1_zfmisc_1(X31)) )
      & ( X32 = X31
        | v1_subset_1(X32,X31)
        | ~ m1_subset_1(X32,k1_zfmisc_1(X31)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,X2)
    | ~ v13_waybel_0(X2,X3)
    | ~ r1_orders_2(X3,X4,X1)
    | ~ l1_orders_2(X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ r2_hidden(X4,X2) ),
    inference(csr,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( u1_struct_0(esk5_0) = esk6_0
    | m1_subset_1(esk2_2(esk6_0,u1_struct_0(esk5_0)),u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_34,negated_conjecture,
    ( l1_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_35,plain,
    ( X1 = X2
    | ~ r2_hidden(esk2_2(X1,X2),X1)
    | ~ r2_hidden(esk2_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_36,plain,
    ( X1 = X2
    | v1_subset_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_37,plain,(
    ! [X23,X24] :
      ( v2_struct_0(X23)
      | ~ v5_orders_2(X23)
      | ~ v1_yellow_0(X23)
      | ~ l1_orders_2(X23)
      | ~ m1_subset_1(X24,u1_struct_0(X23))
      | r1_orders_2(X23,k3_yellow_0(X23),X24) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t44_yellow_0])])])])).

cnf(c_0_38,negated_conjecture,
    ( u1_struct_0(esk5_0) = esk6_0
    | r2_hidden(esk2_2(esk6_0,u1_struct_0(esk5_0)),X1)
    | ~ v13_waybel_0(X1,esk5_0)
    | ~ r1_orders_2(esk5_0,X2,esk2_2(esk6_0,u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ r2_hidden(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])])).

cnf(c_0_39,negated_conjecture,
    ( v13_waybel_0(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_40,negated_conjecture,
    ( u1_struct_0(esk5_0) = esk6_0
    | ~ r2_hidden(esk2_2(esk6_0,u1_struct_0(esk5_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_30])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(k3_yellow_0(esk5_0),esk6_0)
    | ~ v1_subset_1(esk6_0,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_42,negated_conjecture,
    ( u1_struct_0(esk5_0) = esk6_0
    | v1_subset_1(esk6_0,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_16])).

cnf(c_0_43,plain,
    ( v2_struct_0(X1)
    | r1_orders_2(X1,k3_yellow_0(X1),X2)
    | ~ v5_orders_2(X1)
    | ~ v1_yellow_0(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_44,negated_conjecture,
    ( v1_yellow_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_45,negated_conjecture,
    ( v5_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_46,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_47,plain,(
    ! [X18] : ~ v1_subset_1(k2_subset_1(X18),X18) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc14_subset_1])])).

fof(c_0_48,plain,(
    ! [X14] : k2_subset_1(X14) = X14 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

fof(c_0_49,plain,(
    ! [X22] :
      ( ~ l1_orders_2(X22)
      | m1_subset_1(k3_yellow_0(X22),u1_struct_0(X22)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_yellow_0])])).

cnf(c_0_50,negated_conjecture,
    ( u1_struct_0(esk5_0) = esk6_0
    | ~ r1_orders_2(esk5_0,X1,esk2_2(esk6_0,u1_struct_0(esk5_0)))
    | ~ r2_hidden(X1,esk6_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_16])]),c_0_40])).

cnf(c_0_51,negated_conjecture,
    ( u1_struct_0(esk5_0) = esk6_0
    | r2_hidden(k3_yellow_0(esk5_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_52,negated_conjecture,
    ( u1_struct_0(esk5_0) = esk6_0
    | r1_orders_2(esk5_0,k3_yellow_0(esk5_0),esk2_2(esk6_0,u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_33]),c_0_44]),c_0_45]),c_0_34])]),c_0_46])).

cnf(c_0_53,plain,
    ( ~ v1_subset_1(k2_subset_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_54,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_55,plain,
    ( m1_subset_1(k3_yellow_0(X1),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_56,negated_conjecture,
    ( u1_struct_0(esk5_0) = esk6_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52])).

cnf(c_0_57,negated_conjecture,
    ( v1_subset_1(esk6_0,u1_struct_0(esk5_0))
    | ~ r2_hidden(k3_yellow_0(esk5_0),esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_58,plain,
    ( ~ v1_subset_1(X1,X1) ),
    inference(rw,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_59,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_60,negated_conjecture,
    ( m1_subset_1(k3_yellow_0(esk5_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_34])])).

cnf(c_0_61,negated_conjecture,
    ( ~ r2_hidden(k3_yellow_0(esk5_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_56]),c_0_58])).

cnf(c_0_62,negated_conjecture,
    ( ~ v1_xboole_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_63,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61]),c_0_62]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.32  % Computer   : n007.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 14:33:06 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  # Version: 2.5pre002
% 0.11/0.32  # No SInE strategy applied
% 0.11/0.32  # Trying AutoSched0 for 299 seconds
% 0.51/0.67  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_SE_CS_SP_PI_PS_S2S
% 0.51/0.67  # and selection function SelectNewComplexAHP.
% 0.51/0.67  #
% 0.51/0.67  # Preprocessing time       : 0.028 s
% 0.51/0.67  # Presaturation interreduction done
% 0.51/0.67  
% 0.51/0.67  # Proof found!
% 0.51/0.67  # SZS status Theorem
% 0.51/0.67  # SZS output start CNFRefutation
% 0.51/0.67  fof(t8_waybel_7, conjecture, ![X1]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&v1_yellow_0(X1))&l1_orders_2(X1))=>![X2]:((((~(v1_xboole_0(X2))&v2_waybel_0(X2,X1))&v13_waybel_0(X2,X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v1_subset_1(X2,u1_struct_0(X1))<=>~(r2_hidden(k3_yellow_0(X1),X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_waybel_7)).
% 0.51/0.67  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 0.51/0.67  fof(t2_tarski, axiom, ![X1, X2]:(![X3]:(r2_hidden(X3,X1)<=>r2_hidden(X3,X2))=>X1=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 0.51/0.67  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 0.51/0.67  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.51/0.67  fof(d20_waybel_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v13_waybel_0(X2,X1)<=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((r2_hidden(X3,X2)&r1_orders_2(X1,X3,X4))=>r2_hidden(X4,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d20_waybel_0)).
% 0.51/0.67  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 0.51/0.67  fof(d7_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(v1_subset_1(X2,X1)<=>X2!=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 0.51/0.67  fof(t44_yellow_0, axiom, ![X1]:((((~(v2_struct_0(X1))&v5_orders_2(X1))&v1_yellow_0(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>r1_orders_2(X1,k3_yellow_0(X1),X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_yellow_0)).
% 0.51/0.67  fof(fc14_subset_1, axiom, ![X1]:~(v1_subset_1(k2_subset_1(X1),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc14_subset_1)).
% 0.51/0.67  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 0.51/0.67  fof(dt_k3_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>m1_subset_1(k3_yellow_0(X1),u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_yellow_0)).
% 0.51/0.67  fof(c_0_12, negated_conjecture, ~(![X1]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&v1_yellow_0(X1))&l1_orders_2(X1))=>![X2]:((((~(v1_xboole_0(X2))&v2_waybel_0(X2,X1))&v13_waybel_0(X2,X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v1_subset_1(X2,u1_struct_0(X1))<=>~(r2_hidden(k3_yellow_0(X1),X2)))))), inference(assume_negation,[status(cth)],[t8_waybel_7])).
% 0.51/0.67  fof(c_0_13, plain, ![X15, X16, X17]:(~m1_subset_1(X16,k1_zfmisc_1(X15))|(~r2_hidden(X17,X16)|r2_hidden(X17,X15))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.51/0.67  fof(c_0_14, negated_conjecture, ((((((~v2_struct_0(esk5_0)&v3_orders_2(esk5_0))&v4_orders_2(esk5_0))&v5_orders_2(esk5_0))&v1_yellow_0(esk5_0))&l1_orders_2(esk5_0))&((((~v1_xboole_0(esk6_0)&v2_waybel_0(esk6_0,esk5_0))&v13_waybel_0(esk6_0,esk5_0))&m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0))))&((~v1_subset_1(esk6_0,u1_struct_0(esk5_0))|r2_hidden(k3_yellow_0(esk5_0),esk6_0))&(v1_subset_1(esk6_0,u1_struct_0(esk5_0))|~r2_hidden(k3_yellow_0(esk5_0),esk6_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])).
% 0.51/0.67  cnf(c_0_15, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.51/0.67  cnf(c_0_16, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.51/0.67  fof(c_0_17, plain, ![X9, X10]:((~r2_hidden(esk2_2(X9,X10),X9)|~r2_hidden(esk2_2(X9,X10),X10)|X9=X10)&(r2_hidden(esk2_2(X9,X10),X9)|r2_hidden(esk2_2(X9,X10),X10)|X9=X10)), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).
% 0.51/0.67  fof(c_0_18, plain, ![X12, X13]:(((~m1_subset_1(X13,X12)|r2_hidden(X13,X12)|v1_xboole_0(X12))&(~r2_hidden(X13,X12)|m1_subset_1(X13,X12)|v1_xboole_0(X12)))&((~m1_subset_1(X13,X12)|v1_xboole_0(X13)|~v1_xboole_0(X12))&(~v1_xboole_0(X13)|m1_subset_1(X13,X12)|~v1_xboole_0(X12)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.51/0.67  fof(c_0_19, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.51/0.67  cnf(c_0_20, negated_conjecture, (r2_hidden(X1,u1_struct_0(esk5_0))|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.51/0.67  cnf(c_0_21, plain, (r2_hidden(esk2_2(X1,X2),X1)|r2_hidden(esk2_2(X1,X2),X2)|X1=X2), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.51/0.67  fof(c_0_22, plain, ![X25, X26, X27, X28]:((~v13_waybel_0(X26,X25)|(~m1_subset_1(X27,u1_struct_0(X25))|(~m1_subset_1(X28,u1_struct_0(X25))|(~r2_hidden(X27,X26)|~r1_orders_2(X25,X27,X28)|r2_hidden(X28,X26))))|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))|~l1_orders_2(X25))&((m1_subset_1(esk3_2(X25,X26),u1_struct_0(X25))|v13_waybel_0(X26,X25)|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))|~l1_orders_2(X25))&((m1_subset_1(esk4_2(X25,X26),u1_struct_0(X25))|v13_waybel_0(X26,X25)|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))|~l1_orders_2(X25))&(((r2_hidden(esk3_2(X25,X26),X26)|v13_waybel_0(X26,X25)|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))|~l1_orders_2(X25))&(r1_orders_2(X25,esk3_2(X25,X26),esk4_2(X25,X26))|v13_waybel_0(X26,X25)|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))|~l1_orders_2(X25)))&(~r2_hidden(esk4_2(X25,X26),X26)|v13_waybel_0(X26,X25)|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))|~l1_orders_2(X25)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d20_waybel_0])])])])])).
% 0.51/0.67  fof(c_0_23, plain, ![X19, X20, X21]:(~r2_hidden(X19,X20)|~m1_subset_1(X20,k1_zfmisc_1(X21))|m1_subset_1(X19,X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.51/0.67  cnf(c_0_24, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.51/0.67  cnf(c_0_25, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.51/0.67  cnf(c_0_26, negated_conjecture, (esk6_0=X1|r2_hidden(esk2_2(esk6_0,X1),u1_struct_0(esk5_0))|r2_hidden(esk2_2(esk6_0,X1),X1)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.51/0.67  cnf(c_0_27, plain, (r2_hidden(X4,X1)|~v13_waybel_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X2))|~m1_subset_1(X4,u1_struct_0(X2))|~r2_hidden(X3,X1)|~r1_orders_2(X2,X3,X4)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.51/0.67  cnf(c_0_28, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.51/0.67  cnf(c_0_29, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(csr,[status(thm)],[c_0_24, c_0_25])).
% 0.51/0.67  cnf(c_0_30, negated_conjecture, (u1_struct_0(esk5_0)=esk6_0|r2_hidden(esk2_2(esk6_0,u1_struct_0(esk5_0)),u1_struct_0(esk5_0))), inference(ef,[status(thm)],[c_0_26])).
% 0.51/0.67  fof(c_0_31, plain, ![X31, X32]:((~v1_subset_1(X32,X31)|X32!=X31|~m1_subset_1(X32,k1_zfmisc_1(X31)))&(X32=X31|v1_subset_1(X32,X31)|~m1_subset_1(X32,k1_zfmisc_1(X31)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).
% 0.51/0.67  cnf(c_0_32, plain, (r2_hidden(X1,X2)|~v13_waybel_0(X2,X3)|~r1_orders_2(X3,X4,X1)|~l1_orders_2(X3)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~m1_subset_1(X1,u1_struct_0(X3))|~r2_hidden(X4,X2)), inference(csr,[status(thm)],[c_0_27, c_0_28])).
% 0.51/0.67  cnf(c_0_33, negated_conjecture, (u1_struct_0(esk5_0)=esk6_0|m1_subset_1(esk2_2(esk6_0,u1_struct_0(esk5_0)),u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.51/0.67  cnf(c_0_34, negated_conjecture, (l1_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.51/0.67  cnf(c_0_35, plain, (X1=X2|~r2_hidden(esk2_2(X1,X2),X1)|~r2_hidden(esk2_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.51/0.67  cnf(c_0_36, plain, (X1=X2|v1_subset_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.51/0.67  fof(c_0_37, plain, ![X23, X24]:(v2_struct_0(X23)|~v5_orders_2(X23)|~v1_yellow_0(X23)|~l1_orders_2(X23)|(~m1_subset_1(X24,u1_struct_0(X23))|r1_orders_2(X23,k3_yellow_0(X23),X24))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t44_yellow_0])])])])).
% 0.51/0.67  cnf(c_0_38, negated_conjecture, (u1_struct_0(esk5_0)=esk6_0|r2_hidden(esk2_2(esk6_0,u1_struct_0(esk5_0)),X1)|~v13_waybel_0(X1,esk5_0)|~r1_orders_2(esk5_0,X2,esk2_2(esk6_0,u1_struct_0(esk5_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))|~r2_hidden(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34])])).
% 0.51/0.67  cnf(c_0_39, negated_conjecture, (v13_waybel_0(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.51/0.67  cnf(c_0_40, negated_conjecture, (u1_struct_0(esk5_0)=esk6_0|~r2_hidden(esk2_2(esk6_0,u1_struct_0(esk5_0)),esk6_0)), inference(spm,[status(thm)],[c_0_35, c_0_30])).
% 0.51/0.67  cnf(c_0_41, negated_conjecture, (r2_hidden(k3_yellow_0(esk5_0),esk6_0)|~v1_subset_1(esk6_0,u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.51/0.67  cnf(c_0_42, negated_conjecture, (u1_struct_0(esk5_0)=esk6_0|v1_subset_1(esk6_0,u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_36, c_0_16])).
% 0.51/0.67  cnf(c_0_43, plain, (v2_struct_0(X1)|r1_orders_2(X1,k3_yellow_0(X1),X2)|~v5_orders_2(X1)|~v1_yellow_0(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.51/0.67  cnf(c_0_44, negated_conjecture, (v1_yellow_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.51/0.67  cnf(c_0_45, negated_conjecture, (v5_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.51/0.67  cnf(c_0_46, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.51/0.67  fof(c_0_47, plain, ![X18]:~v1_subset_1(k2_subset_1(X18),X18), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc14_subset_1])])).
% 0.51/0.67  fof(c_0_48, plain, ![X14]:k2_subset_1(X14)=X14, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.51/0.67  fof(c_0_49, plain, ![X22]:(~l1_orders_2(X22)|m1_subset_1(k3_yellow_0(X22),u1_struct_0(X22))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_yellow_0])])).
% 0.51/0.67  cnf(c_0_50, negated_conjecture, (u1_struct_0(esk5_0)=esk6_0|~r1_orders_2(esk5_0,X1,esk2_2(esk6_0,u1_struct_0(esk5_0)))|~r2_hidden(X1,esk6_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_16])]), c_0_40])).
% 0.51/0.67  cnf(c_0_51, negated_conjecture, (u1_struct_0(esk5_0)=esk6_0|r2_hidden(k3_yellow_0(esk5_0),esk6_0)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.51/0.67  cnf(c_0_52, negated_conjecture, (u1_struct_0(esk5_0)=esk6_0|r1_orders_2(esk5_0,k3_yellow_0(esk5_0),esk2_2(esk6_0,u1_struct_0(esk5_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_33]), c_0_44]), c_0_45]), c_0_34])]), c_0_46])).
% 0.51/0.67  cnf(c_0_53, plain, (~v1_subset_1(k2_subset_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.51/0.67  cnf(c_0_54, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.51/0.67  cnf(c_0_55, plain, (m1_subset_1(k3_yellow_0(X1),u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.51/0.67  cnf(c_0_56, negated_conjecture, (u1_struct_0(esk5_0)=esk6_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52])).
% 0.51/0.67  cnf(c_0_57, negated_conjecture, (v1_subset_1(esk6_0,u1_struct_0(esk5_0))|~r2_hidden(k3_yellow_0(esk5_0),esk6_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.51/0.67  cnf(c_0_58, plain, (~v1_subset_1(X1,X1)), inference(rw,[status(thm)],[c_0_53, c_0_54])).
% 0.51/0.67  cnf(c_0_59, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.51/0.67  cnf(c_0_60, negated_conjecture, (m1_subset_1(k3_yellow_0(esk5_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_34])])).
% 0.51/0.67  cnf(c_0_61, negated_conjecture, (~r2_hidden(k3_yellow_0(esk5_0),esk6_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_56]), c_0_58])).
% 0.51/0.67  cnf(c_0_62, negated_conjecture, (~v1_xboole_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.51/0.67  cnf(c_0_63, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_61]), c_0_62]), ['proof']).
% 0.51/0.67  # SZS output end CNFRefutation
% 0.51/0.67  # Proof object total steps             : 64
% 0.51/0.67  # Proof object clause steps            : 39
% 0.51/0.67  # Proof object formula steps           : 25
% 0.51/0.67  # Proof object conjectures             : 26
% 0.51/0.67  # Proof object clause conjectures      : 23
% 0.51/0.67  # Proof object formula conjectures     : 3
% 0.51/0.67  # Proof object initial clauses used    : 22
% 0.51/0.67  # Proof object initial formulas used   : 12
% 0.51/0.67  # Proof object generating inferences   : 13
% 0.51/0.67  # Proof object simplifying inferences  : 20
% 0.51/0.67  # Training examples: 0 positive, 0 negative
% 0.51/0.67  # Parsed axioms                        : 12
% 0.51/0.67  # Removed by relevancy pruning/SinE    : 0
% 0.51/0.67  # Initial clauses                      : 34
% 0.51/0.67  # Removed in clause preprocessing      : 1
% 0.51/0.67  # Initial clauses in saturation        : 33
% 0.51/0.67  # Processed clauses                    : 2941
% 0.51/0.67  # ...of these trivial                  : 0
% 0.51/0.67  # ...subsumed                          : 2202
% 0.51/0.67  # ...remaining for further processing  : 739
% 0.51/0.67  # Other redundant clauses eliminated   : 1
% 0.51/0.67  # Clauses deleted for lack of memory   : 0
% 0.51/0.67  # Backward-subsumed                    : 15
% 0.51/0.67  # Backward-rewritten                   : 286
% 0.51/0.67  # Generated clauses                    : 11466
% 0.51/0.67  # ...of the previous two non-trivial   : 10946
% 0.51/0.67  # Contextual simplify-reflections      : 27
% 0.51/0.67  # Paramodulations                      : 11442
% 0.51/0.67  # Factorizations                       : 20
% 0.51/0.67  # Equation resolutions                 : 1
% 0.51/0.67  # Propositional unsat checks           : 0
% 0.51/0.67  #    Propositional check models        : 0
% 0.51/0.67  #    Propositional check unsatisfiable : 0
% 0.51/0.67  #    Propositional clauses             : 0
% 0.51/0.67  #    Propositional clauses after purity: 0
% 0.51/0.67  #    Propositional unsat core size     : 0
% 0.51/0.67  #    Propositional preprocessing time  : 0.000
% 0.51/0.67  #    Propositional encoding time       : 0.000
% 0.51/0.67  #    Propositional solver time         : 0.000
% 0.51/0.67  #    Success case prop preproc time    : 0.000
% 0.51/0.67  #    Success case prop encoding time   : 0.000
% 0.51/0.67  #    Success case prop solver time     : 0.000
% 0.51/0.67  # Current number of processed clauses  : 402
% 0.51/0.67  #    Positive orientable unit clauses  : 12
% 0.51/0.67  #    Positive unorientable unit clauses: 0
% 0.51/0.67  #    Negative unit clauses             : 5
% 0.51/0.67  #    Non-unit-clauses                  : 385
% 0.51/0.67  # Current number of unprocessed clauses: 8030
% 0.51/0.67  # ...number of literals in the above   : 61172
% 0.51/0.67  # Current number of archived formulas  : 0
% 0.51/0.67  # Current number of archived clauses   : 337
% 0.51/0.67  # Clause-clause subsumption calls (NU) : 77433
% 0.51/0.67  # Rec. Clause-clause subsumption calls : 12927
% 0.51/0.67  # Non-unit clause-clause subsumptions  : 1739
% 0.51/0.67  # Unit Clause-clause subsumption calls : 118
% 0.51/0.67  # Rewrite failures with RHS unbound    : 0
% 0.51/0.67  # BW rewrite match attempts            : 1
% 0.51/0.67  # BW rewrite match successes           : 1
% 0.51/0.67  # Condensation attempts                : 0
% 0.51/0.67  # Condensation successes               : 0
% 0.51/0.67  # Termbank termtop insertions          : 255228
% 0.51/0.68  
% 0.51/0.68  # -------------------------------------------------
% 0.51/0.68  # User time                : 0.344 s
% 0.51/0.68  # System time              : 0.013 s
% 0.51/0.68  # Total time               : 0.358 s
% 0.51/0.68  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
