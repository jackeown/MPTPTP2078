%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : waybel_7__t8_waybel_7.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:08 EDT 2019

% Result     : Theorem 28.51s
% Output     : CNFRefutation 28.51s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 499 expanded)
%              Number of clauses        :   49 ( 217 expanded)
%              Number of leaves         :   11 ( 118 expanded)
%              Depth                    :   14
%              Number of atoms          :  256 (2863 expanded)
%              Number of equality atoms :   29 ( 175 expanded)
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
    file('/export/starexec/sandbox2/benchmark/waybel_7__t8_waybel_7.p',t8_waybel_7)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t8_waybel_7.p',t4_subset)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t8_waybel_7.p',t1_subset)).

fof(t2_tarski,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
        <=> r2_hidden(X3,X2) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t8_waybel_7.p',t2_tarski)).

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
    file('/export/starexec/sandbox2/benchmark/waybel_7__t8_waybel_7.p',d20_waybel_0)).

fof(d7_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( v1_subset_1(X2,X1)
      <=> X2 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t8_waybel_7.p',d7_subset_1)).

fof(t44_yellow_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v5_orders_2(X1)
        & v1_yellow_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => r1_orders_2(X1,k3_yellow_0(X1),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t8_waybel_7.p',t44_yellow_0)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t8_waybel_7.p',t2_subset)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t8_waybel_7.p',t5_subset)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t8_waybel_7.p',t7_boole)).

fof(dt_k3_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => m1_subset_1(k3_yellow_0(X1),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t8_waybel_7.p',dt_k3_yellow_0)).

fof(c_0_11,negated_conjecture,(
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

fof(c_0_12,plain,(
    ! [X36,X37,X38] :
      ( ~ r2_hidden(X36,X37)
      | ~ m1_subset_1(X37,k1_zfmisc_1(X38))
      | m1_subset_1(X36,X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_13,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v3_orders_2(esk1_0)
    & v4_orders_2(esk1_0)
    & v5_orders_2(esk1_0)
    & v1_yellow_0(esk1_0)
    & l1_orders_2(esk1_0)
    & ~ v1_xboole_0(esk2_0)
    & v2_waybel_0(esk2_0,esk1_0)
    & v13_waybel_0(esk2_0,esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & ( ~ v1_subset_1(esk2_0,u1_struct_0(esk1_0))
      | r2_hidden(k3_yellow_0(esk1_0),esk2_0) )
    & ( v1_subset_1(esk2_0,u1_struct_0(esk1_0))
      | ~ r2_hidden(k3_yellow_0(esk1_0),esk2_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])).

fof(c_0_14,plain,(
    ! [X25,X26] :
      ( ~ r2_hidden(X25,X26)
      | m1_subset_1(X25,X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

fof(c_0_15,plain,(
    ! [X29,X30] :
      ( ( ~ r2_hidden(esk8_2(X29,X30),X29)
        | ~ r2_hidden(esk8_2(X29,X30),X30)
        | X29 = X30 )
      & ( r2_hidden(esk8_2(X29,X30),X29)
        | r2_hidden(esk8_2(X29,X30),X30)
        | X29 = X30 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).

cnf(c_0_16,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( r2_hidden(esk8_2(X1,X2),X1)
    | r2_hidden(esk8_2(X1,X2),X2)
    | X1 = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_20,plain,(
    ! [X9,X10,X11,X12] :
      ( ( ~ v13_waybel_0(X10,X9)
        | ~ m1_subset_1(X11,u1_struct_0(X9))
        | ~ m1_subset_1(X12,u1_struct_0(X9))
        | ~ r2_hidden(X11,X10)
        | ~ r1_orders_2(X9,X11,X12)
        | r2_hidden(X12,X10)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
        | ~ l1_orders_2(X9) )
      & ( m1_subset_1(esk3_2(X9,X10),u1_struct_0(X9))
        | v13_waybel_0(X10,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
        | ~ l1_orders_2(X9) )
      & ( m1_subset_1(esk4_2(X9,X10),u1_struct_0(X9))
        | v13_waybel_0(X10,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
        | ~ l1_orders_2(X9) )
      & ( r2_hidden(esk3_2(X9,X10),X10)
        | v13_waybel_0(X10,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
        | ~ l1_orders_2(X9) )
      & ( r1_orders_2(X9,esk3_2(X9,X10),esk4_2(X9,X10))
        | v13_waybel_0(X10,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
        | ~ l1_orders_2(X9) )
      & ( ~ r2_hidden(esk4_2(X9,X10),X10)
        | v13_waybel_0(X10,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
        | ~ l1_orders_2(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d20_waybel_0])])])])])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_22,plain,
    ( X1 = X2
    | r2_hidden(esk8_2(X1,X2),X2)
    | m1_subset_1(esk8_2(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_23,plain,
    ( r2_hidden(X4,X1)
    | ~ v13_waybel_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r2_hidden(X3,X1)
    | ~ r1_orders_2(X2,X3,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( X1 = esk2_0
    | m1_subset_1(esk8_2(X1,esk2_0),u1_struct_0(esk1_0))
    | m1_subset_1(esk8_2(X1,esk2_0),X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

fof(c_0_25,plain,(
    ! [X15,X16] :
      ( ( ~ v1_subset_1(X16,X15)
        | X16 != X15
        | ~ m1_subset_1(X16,k1_zfmisc_1(X15)) )
      & ( X16 = X15
        | v1_subset_1(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(X15)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).

cnf(c_0_26,plain,
    ( X1 = X2
    | r2_hidden(esk8_2(X1,X2),X1)
    | m1_subset_1(esk8_2(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_orders_2(X3,X4,X1)
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ v13_waybel_0(X2,X3)
    | ~ l1_orders_2(X3) ),
    inference(csr,[status(thm)],[c_0_23,c_0_16])).

cnf(c_0_28,negated_conjecture,
    ( u1_struct_0(esk1_0) = esk2_0
    | m1_subset_1(esk8_2(u1_struct_0(esk1_0),esk2_0),u1_struct_0(esk1_0)) ),
    inference(ef,[status(thm)],[c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_30,plain,
    ( X1 = X2
    | v1_subset_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_31,plain,(
    ! [X34,X35] :
      ( v2_struct_0(X34)
      | ~ v5_orders_2(X34)
      | ~ v1_yellow_0(X34)
      | ~ l1_orders_2(X34)
      | ~ m1_subset_1(X35,u1_struct_0(X34))
      | r1_orders_2(X34,k3_yellow_0(X34),X35) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t44_yellow_0])])])])).

fof(c_0_32,plain,(
    ! [X27,X28] :
      ( ~ m1_subset_1(X27,X28)
      | v1_xboole_0(X28)
      | r2_hidden(X27,X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_33,negated_conjecture,
    ( esk2_0 = X1
    | m1_subset_1(esk8_2(esk2_0,X1),u1_struct_0(esk1_0))
    | m1_subset_1(esk8_2(esk2_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_26])).

fof(c_0_34,plain,(
    ! [X39,X40,X41] :
      ( ~ r2_hidden(X39,X40)
      | ~ m1_subset_1(X40,k1_zfmisc_1(X41))
      | ~ v1_xboole_0(X41) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_35,negated_conjecture,
    ( u1_struct_0(esk1_0) = esk2_0
    | r2_hidden(esk8_2(u1_struct_0(esk1_0),esk2_0),X1)
    | ~ r1_orders_2(esk1_0,X2,esk8_2(u1_struct_0(esk1_0),esk2_0))
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ v13_waybel_0(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])])).

cnf(c_0_36,negated_conjecture,
    ( v13_waybel_0(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(k3_yellow_0(esk1_0),esk2_0)
    | ~ v1_subset_1(esk2_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_38,negated_conjecture,
    ( u1_struct_0(esk1_0) = esk2_0
    | v1_subset_1(esk2_0,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_17])).

cnf(c_0_39,plain,
    ( v2_struct_0(X1)
    | r1_orders_2(X1,k3_yellow_0(X1),X2)
    | ~ v5_orders_2(X1)
    | ~ v1_yellow_0(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_40,negated_conjecture,
    ( v1_yellow_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_41,negated_conjecture,
    ( v5_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_42,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_43,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_44,negated_conjecture,
    ( u1_struct_0(esk1_0) = esk2_0
    | m1_subset_1(esk8_2(esk2_0,u1_struct_0(esk1_0)),u1_struct_0(esk1_0)) ),
    inference(ef,[status(thm)],[c_0_33])).

cnf(c_0_45,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_46,plain,(
    ! [X43,X44] :
      ( ~ r2_hidden(X43,X44)
      | ~ v1_xboole_0(X44) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_47,negated_conjecture,
    ( u1_struct_0(esk1_0) = esk2_0
    | r2_hidden(esk8_2(u1_struct_0(esk1_0),esk2_0),esk2_0)
    | ~ r1_orders_2(esk1_0,X1,esk8_2(u1_struct_0(esk1_0),esk2_0))
    | ~ r2_hidden(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_17])])).

cnf(c_0_48,negated_conjecture,
    ( u1_struct_0(esk1_0) = esk2_0
    | r2_hidden(k3_yellow_0(esk1_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_49,negated_conjecture,
    ( u1_struct_0(esk1_0) = esk2_0
    | r1_orders_2(esk1_0,k3_yellow_0(esk1_0),esk8_2(u1_struct_0(esk1_0),esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_28]),c_0_29]),c_0_40]),c_0_41])]),c_0_42])).

cnf(c_0_50,plain,
    ( X1 = X2
    | ~ r2_hidden(esk8_2(X1,X2),X1)
    | ~ r2_hidden(esk8_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_51,negated_conjecture,
    ( u1_struct_0(esk1_0) = esk2_0
    | r2_hidden(esk8_2(esk2_0,u1_struct_0(esk1_0)),u1_struct_0(esk1_0))
    | v1_xboole_0(u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_52,negated_conjecture,
    ( ~ r2_hidden(X1,esk2_0)
    | ~ v1_xboole_0(u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_17])).

cnf(c_0_53,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_54,negated_conjecture,
    ( u1_struct_0(esk1_0) = esk2_0
    | r2_hidden(esk8_2(u1_struct_0(esk1_0),esk2_0),esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49])).

cnf(c_0_55,negated_conjecture,
    ( u1_struct_0(esk1_0) = esk2_0
    | ~ r2_hidden(esk8_2(esk2_0,u1_struct_0(esk1_0)),esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52])).

cnf(c_0_56,plain,
    ( X1 = X2
    | r2_hidden(esk8_2(X1,X2),X1)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_53,c_0_19])).

fof(c_0_57,plain,(
    ! [X19] :
      ( ~ l1_orders_2(X19)
      | m1_subset_1(k3_yellow_0(X19),u1_struct_0(X19)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_yellow_0])])).

cnf(c_0_58,negated_conjecture,
    ( u1_struct_0(esk1_0) = esk2_0
    | ~ r2_hidden(esk8_2(u1_struct_0(esk1_0),esk2_0),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_54])).

cnf(c_0_59,negated_conjecture,
    ( u1_struct_0(esk1_0) = esk2_0
    | r2_hidden(esk8_2(u1_struct_0(esk1_0),esk2_0),u1_struct_0(esk1_0))
    | v1_xboole_0(u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_28])).

cnf(c_0_60,negated_conjecture,
    ( u1_struct_0(esk1_0) = esk2_0
    | ~ v1_xboole_0(u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_61,plain,
    ( m1_subset_1(k3_yellow_0(X1),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_62,plain,
    ( ~ v1_subset_1(X1,X2)
    | X1 != X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_63,negated_conjecture,
    ( u1_struct_0(esk1_0) = esk2_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_60])).

cnf(c_0_64,plain,
    ( r2_hidden(k3_yellow_0(X1),u1_struct_0(X1))
    | v1_xboole_0(u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_61])).

cnf(c_0_65,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_66,plain,
    ( ~ v1_subset_1(X1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(er,[status(thm)],[c_0_62])).

cnf(c_0_67,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_17,c_0_63])).

cnf(c_0_68,negated_conjecture,
    ( v1_subset_1(esk2_0,u1_struct_0(esk1_0))
    | ~ r2_hidden(k3_yellow_0(esk1_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_69,negated_conjecture,
    ( r2_hidden(k3_yellow_0(esk1_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_63]),c_0_29])]),c_0_65])).

cnf(c_0_70,negated_conjecture,
    ( ~ v1_subset_1(esk2_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_71,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_63]),c_0_69])]),c_0_70]),
    [proof]).
%------------------------------------------------------------------------------
