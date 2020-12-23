%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:24 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 338 expanded)
%              Number of clauses        :   51 ( 123 expanded)
%              Number of leaves         :   15 (  82 expanded)
%              Depth                    :   11
%              Number of atoms          :  308 (2563 expanded)
%              Number of equality atoms :   34 (  85 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    5 (   1 average)

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

fof(t49_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( ! [X3] :
            ( m1_subset_1(X3,X1)
           => r2_hidden(X3,X2) )
       => X1 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_subset_1)).

fof(dt_k1_yellow_0,axiom,(
    ! [X1,X2] :
      ( l1_orders_2(X1)
     => m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_yellow_0)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_waybel_0)).

fof(d11_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => k3_yellow_0(X1) = k1_yellow_0(X1,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_yellow_0)).

fof(t34_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2,X3] :
          ( ( r1_tarski(X2,X3)
            & r1_yellow_0(X1,X2)
            & r1_yellow_0(X1,X3) )
         => r1_orders_2(X1,k1_yellow_0(X1,X2),k1_yellow_0(X1,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_yellow_0)).

fof(t42_yellow_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v5_orders_2(X1)
        & v1_yellow_0(X1)
        & l1_orders_2(X1) )
     => ( r1_yellow_0(X1,k1_xboole_0)
        & r2_yellow_0(X1,u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_yellow_0)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(dt_k3_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => m1_subset_1(k3_yellow_0(X1),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_yellow_0)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(c_0_15,negated_conjecture,(
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

fof(c_0_16,plain,(
    ! [X26,X27,X28,X29] :
      ( ( ~ v13_waybel_0(X27,X26)
        | ~ m1_subset_1(X28,u1_struct_0(X26))
        | ~ m1_subset_1(X29,u1_struct_0(X26))
        | ~ r2_hidden(X28,X27)
        | ~ r1_orders_2(X26,X28,X29)
        | r2_hidden(X29,X27)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ l1_orders_2(X26) )
      & ( m1_subset_1(esk2_2(X26,X27),u1_struct_0(X26))
        | v13_waybel_0(X27,X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ l1_orders_2(X26) )
      & ( m1_subset_1(esk3_2(X26,X27),u1_struct_0(X26))
        | v13_waybel_0(X27,X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ l1_orders_2(X26) )
      & ( r2_hidden(esk2_2(X26,X27),X27)
        | v13_waybel_0(X27,X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ l1_orders_2(X26) )
      & ( r1_orders_2(X26,esk2_2(X26,X27),esk3_2(X26,X27))
        | v13_waybel_0(X27,X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ l1_orders_2(X26) )
      & ( ~ r2_hidden(esk3_2(X26,X27),X27)
        | v13_waybel_0(X27,X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ l1_orders_2(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d20_waybel_0])])])])])).

fof(c_0_17,plain,(
    ! [X15,X16,X17] :
      ( ~ r2_hidden(X15,X16)
      | ~ m1_subset_1(X16,k1_zfmisc_1(X17))
      | m1_subset_1(X15,X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_18,plain,(
    ! [X34,X35] :
      ( ( ~ v1_subset_1(X35,X34)
        | X35 != X34
        | ~ m1_subset_1(X35,k1_zfmisc_1(X34)) )
      & ( X35 = X34
        | v1_subset_1(X35,X34)
        | ~ m1_subset_1(X35,k1_zfmisc_1(X34)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).

fof(c_0_19,negated_conjecture,
    ( ~ v2_struct_0(esk4_0)
    & v3_orders_2(esk4_0)
    & v4_orders_2(esk4_0)
    & v5_orders_2(esk4_0)
    & v1_yellow_0(esk4_0)
    & l1_orders_2(esk4_0)
    & ~ v1_xboole_0(esk5_0)
    & v2_waybel_0(esk5_0,esk4_0)
    & v13_waybel_0(esk5_0,esk4_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))
    & ( ~ v1_subset_1(esk5_0,u1_struct_0(esk4_0))
      | r2_hidden(k3_yellow_0(esk4_0),esk5_0) )
    & ( v1_subset_1(esk5_0,u1_struct_0(esk4_0))
      | ~ r2_hidden(k3_yellow_0(esk4_0),esk5_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).

fof(c_0_20,plain,(
    ! [X8,X9] :
      ( ( m1_subset_1(esk1_2(X8,X9),X8)
        | X8 = X9
        | ~ m1_subset_1(X9,k1_zfmisc_1(X8)) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | X8 = X9
        | ~ m1_subset_1(X9,k1_zfmisc_1(X8)) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t49_subset_1])])])])).

cnf(c_0_21,plain,
    ( r2_hidden(X4,X1)
    | ~ v13_waybel_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r2_hidden(X3,X1)
    | ~ r1_orders_2(X2,X3,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_23,plain,(
    ! [X19,X20] :
      ( ~ l1_orders_2(X19)
      | m1_subset_1(k1_yellow_0(X19,X20),u1_struct_0(X19)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_yellow_0])])).

cnf(c_0_24,plain,
    ( X1 = X2
    | v1_subset_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_26,plain,(
    ! [X32,X33] :
      ( ( r1_yellow_0(X32,k5_waybel_0(X32,X33))
        | ~ m1_subset_1(X33,u1_struct_0(X32))
        | v2_struct_0(X32)
        | ~ v3_orders_2(X32)
        | ~ v4_orders_2(X32)
        | ~ v5_orders_2(X32)
        | ~ l1_orders_2(X32) )
      & ( k1_yellow_0(X32,k5_waybel_0(X32,X33)) = X33
        | ~ m1_subset_1(X33,u1_struct_0(X32))
        | v2_struct_0(X32)
        | ~ v3_orders_2(X32)
        | ~ v4_orders_2(X32)
        | ~ v5_orders_2(X32)
        | ~ l1_orders_2(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_waybel_0])])])])])).

cnf(c_0_27,plain,
    ( m1_subset_1(esk1_2(X1,X2),X1)
    | X1 = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,X2)
    | ~ v13_waybel_0(X2,X3)
    | ~ r1_orders_2(X3,X4,X1)
    | ~ l1_orders_2(X3)
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X1,u1_struct_0(X3)) ),
    inference(csr,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_29,plain,
    ( m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(k3_yellow_0(esk4_0),esk5_0)
    | ~ v1_subset_1(esk5_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_31,negated_conjecture,
    ( u1_struct_0(esk4_0) = esk5_0
    | v1_subset_1(esk5_0,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

fof(c_0_32,plain,(
    ! [X18] :
      ( ~ l1_orders_2(X18)
      | k3_yellow_0(X18) = k1_yellow_0(X18,k1_xboole_0) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_yellow_0])])).

fof(c_0_33,plain,(
    ! [X22,X23,X24] :
      ( ~ l1_orders_2(X22)
      | ~ r1_tarski(X23,X24)
      | ~ r1_yellow_0(X22,X23)
      | ~ r1_yellow_0(X22,X24)
      | r1_orders_2(X22,k1_yellow_0(X22,X23),k1_yellow_0(X22,X24)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_yellow_0])])])).

cnf(c_0_34,plain,
    ( r1_yellow_0(X1,k5_waybel_0(X1,X2))
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,negated_conjecture,
    ( u1_struct_0(esk4_0) = esk5_0
    | m1_subset_1(esk1_2(u1_struct_0(esk4_0),esk5_0),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_25])).

cnf(c_0_36,negated_conjecture,
    ( v4_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_37,negated_conjecture,
    ( v3_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_38,negated_conjecture,
    ( v5_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_39,negated_conjecture,
    ( l1_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_40,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_41,plain,(
    ! [X25] :
      ( ( r1_yellow_0(X25,k1_xboole_0)
        | v2_struct_0(X25)
        | ~ v5_orders_2(X25)
        | ~ v1_yellow_0(X25)
        | ~ l1_orders_2(X25) )
      & ( r2_yellow_0(X25,u1_struct_0(X25))
        | v2_struct_0(X25)
        | ~ v5_orders_2(X25)
        | ~ v1_yellow_0(X25)
        | ~ l1_orders_2(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t42_yellow_0])])])])).

cnf(c_0_42,plain,
    ( r2_hidden(k1_yellow_0(X1,X2),X3)
    | ~ v13_waybel_0(X3,X1)
    | ~ r1_orders_2(X1,X4,k1_yellow_0(X1,X2))
    | ~ l1_orders_2(X1)
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_43,negated_conjecture,
    ( v13_waybel_0(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_44,negated_conjecture,
    ( u1_struct_0(esk4_0) = esk5_0
    | r2_hidden(k3_yellow_0(esk4_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_45,plain,
    ( k3_yellow_0(X1) = k1_yellow_0(X1,k1_xboole_0)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_46,plain,
    ( r1_orders_2(X1,k1_yellow_0(X1,X2),k1_yellow_0(X1,X3))
    | ~ l1_orders_2(X1)
    | ~ r1_tarski(X2,X3)
    | ~ r1_yellow_0(X1,X2)
    | ~ r1_yellow_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_47,negated_conjecture,
    ( u1_struct_0(esk4_0) = esk5_0
    | r1_yellow_0(esk4_0,k5_waybel_0(esk4_0,esk1_2(u1_struct_0(esk4_0),esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36]),c_0_37]),c_0_38]),c_0_39])]),c_0_40])).

cnf(c_0_48,plain,
    ( r1_yellow_0(X1,k1_xboole_0)
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_yellow_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_49,negated_conjecture,
    ( v1_yellow_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_50,plain,(
    ! [X7] : r1_tarski(k1_xboole_0,X7) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_51,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(k1_yellow_0(esk4_0,X1),esk5_0)
    | ~ r1_orders_2(esk4_0,X2,k1_yellow_0(esk4_0,X1))
    | ~ r2_hidden(X2,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_25]),c_0_43]),c_0_39])])).

cnf(c_0_53,negated_conjecture,
    ( u1_struct_0(esk4_0) = esk5_0
    | r2_hidden(k1_yellow_0(esk4_0,k1_xboole_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_39])])).

cnf(c_0_54,negated_conjecture,
    ( u1_struct_0(esk4_0) = esk5_0
    | r1_orders_2(esk4_0,k1_yellow_0(esk4_0,X1),k1_yellow_0(esk4_0,k5_waybel_0(esk4_0,esk1_2(u1_struct_0(esk4_0),esk5_0))))
    | ~ r1_yellow_0(esk4_0,X1)
    | ~ r1_tarski(X1,k5_waybel_0(esk4_0,esk1_2(u1_struct_0(esk4_0),esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_39])])).

cnf(c_0_55,negated_conjecture,
    ( r1_yellow_0(esk4_0,k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_38]),c_0_39])]),c_0_40])).

cnf(c_0_56,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

fof(c_0_57,plain,(
    ! [X13,X14] :
      ( ( ~ m1_subset_1(X13,k1_zfmisc_1(X14))
        | r1_tarski(X13,X14) )
      & ( ~ r1_tarski(X13,X14)
        | m1_subset_1(X13,k1_zfmisc_1(X14)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_58,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_59,negated_conjecture,
    ( u1_struct_0(esk4_0) = esk5_0
    | r2_hidden(k1_yellow_0(esk4_0,X1),esk5_0)
    | ~ r1_orders_2(esk4_0,k1_yellow_0(esk4_0,k1_xboole_0),k1_yellow_0(esk4_0,X1)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_60,negated_conjecture,
    ( u1_struct_0(esk4_0) = esk5_0
    | r1_orders_2(esk4_0,k1_yellow_0(esk4_0,k1_xboole_0),k1_yellow_0(esk4_0,k5_waybel_0(esk4_0,esk1_2(u1_struct_0(esk4_0),esk5_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56])])).

cnf(c_0_61,plain,
    ( k1_yellow_0(X1,k5_waybel_0(X1,X2)) = X2
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_62,plain,
    ( X1 = X2
    | ~ r2_hidden(esk1_2(X1,X2),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_63,plain,
    ( ~ v1_subset_1(X1,X2)
    | X1 != X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_64,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_65,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_58])).

fof(c_0_66,plain,(
    ! [X21] :
      ( ~ l1_orders_2(X21)
      | m1_subset_1(k3_yellow_0(X21),u1_struct_0(X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_yellow_0])])).

cnf(c_0_67,negated_conjecture,
    ( u1_struct_0(esk4_0) = esk5_0
    | r2_hidden(k1_yellow_0(esk4_0,k5_waybel_0(esk4_0,esk1_2(u1_struct_0(esk4_0),esk5_0))),esk5_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_68,negated_conjecture,
    ( k1_yellow_0(esk4_0,k5_waybel_0(esk4_0,esk1_2(u1_struct_0(esk4_0),esk5_0))) = esk1_2(u1_struct_0(esk4_0),esk5_0)
    | u1_struct_0(esk4_0) = esk5_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_35]),c_0_36]),c_0_37]),c_0_38]),c_0_39])]),c_0_40])).

cnf(c_0_69,negated_conjecture,
    ( u1_struct_0(esk4_0) = esk5_0
    | ~ r2_hidden(esk1_2(u1_struct_0(esk4_0),esk5_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_25])).

cnf(c_0_70,plain,
    ( ~ v1_subset_1(X1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(er,[status(thm)],[c_0_63])).

cnf(c_0_71,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

fof(c_0_72,plain,(
    ! [X11,X12] :
      ( ~ m1_subset_1(X11,X12)
      | v1_xboole_0(X12)
      | r2_hidden(X11,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_73,plain,
    ( m1_subset_1(k3_yellow_0(X1),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_74,negated_conjecture,
    ( u1_struct_0(esk4_0) = esk5_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_69])).

cnf(c_0_75,negated_conjecture,
    ( v1_subset_1(esk5_0,u1_struct_0(esk4_0))
    | ~ r2_hidden(k3_yellow_0(esk4_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_76,plain,
    ( ~ v1_subset_1(X1,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_71])])).

cnf(c_0_77,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_78,negated_conjecture,
    ( m1_subset_1(k3_yellow_0(esk4_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_39])])).

cnf(c_0_79,negated_conjecture,
    ( ~ v1_xboole_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_80,negated_conjecture,
    ( ~ r2_hidden(k3_yellow_0(esk4_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_74]),c_0_76])).

cnf(c_0_81,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_79]),c_0_80]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:29:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.39  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_SE_CS_SP_PI_PS_S2S
% 0.12/0.39  # and selection function SelectNewComplexAHP.
% 0.12/0.39  #
% 0.12/0.39  # Preprocessing time       : 0.028 s
% 0.12/0.39  # Presaturation interreduction done
% 0.12/0.39  
% 0.12/0.39  # Proof found!
% 0.12/0.39  # SZS status Theorem
% 0.12/0.39  # SZS output start CNFRefutation
% 0.12/0.39  fof(t8_waybel_7, conjecture, ![X1]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&v1_yellow_0(X1))&l1_orders_2(X1))=>![X2]:((((~(v1_xboole_0(X2))&v2_waybel_0(X2,X1))&v13_waybel_0(X2,X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v1_subset_1(X2,u1_struct_0(X1))<=>~(r2_hidden(k3_yellow_0(X1),X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_waybel_7)).
% 0.12/0.39  fof(d20_waybel_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v13_waybel_0(X2,X1)<=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((r2_hidden(X3,X2)&r1_orders_2(X1,X3,X4))=>r2_hidden(X4,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d20_waybel_0)).
% 0.12/0.39  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 0.12/0.39  fof(d7_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(v1_subset_1(X2,X1)<=>X2!=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 0.12/0.39  fof(t49_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(![X3]:(m1_subset_1(X3,X1)=>r2_hidden(X3,X2))=>X1=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_subset_1)).
% 0.12/0.39  fof(dt_k1_yellow_0, axiom, ![X1, X2]:(l1_orders_2(X1)=>m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_yellow_0)).
% 0.12/0.39  fof(t34_waybel_0, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(r1_yellow_0(X1,k5_waybel_0(X1,X2))&k1_yellow_0(X1,k5_waybel_0(X1,X2))=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_waybel_0)).
% 0.12/0.39  fof(d11_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>k3_yellow_0(X1)=k1_yellow_0(X1,k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_yellow_0)).
% 0.12/0.39  fof(t34_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(((r1_tarski(X2,X3)&r1_yellow_0(X1,X2))&r1_yellow_0(X1,X3))=>r1_orders_2(X1,k1_yellow_0(X1,X2),k1_yellow_0(X1,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_yellow_0)).
% 0.12/0.39  fof(t42_yellow_0, axiom, ![X1]:((((~(v2_struct_0(X1))&v5_orders_2(X1))&v1_yellow_0(X1))&l1_orders_2(X1))=>(r1_yellow_0(X1,k1_xboole_0)&r2_yellow_0(X1,u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_yellow_0)).
% 0.12/0.39  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.12/0.39  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.12/0.39  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.12/0.39  fof(dt_k3_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>m1_subset_1(k3_yellow_0(X1),u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_yellow_0)).
% 0.12/0.39  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 0.12/0.39  fof(c_0_15, negated_conjecture, ~(![X1]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&v1_yellow_0(X1))&l1_orders_2(X1))=>![X2]:((((~(v1_xboole_0(X2))&v2_waybel_0(X2,X1))&v13_waybel_0(X2,X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v1_subset_1(X2,u1_struct_0(X1))<=>~(r2_hidden(k3_yellow_0(X1),X2)))))), inference(assume_negation,[status(cth)],[t8_waybel_7])).
% 0.12/0.39  fof(c_0_16, plain, ![X26, X27, X28, X29]:((~v13_waybel_0(X27,X26)|(~m1_subset_1(X28,u1_struct_0(X26))|(~m1_subset_1(X29,u1_struct_0(X26))|(~r2_hidden(X28,X27)|~r1_orders_2(X26,X28,X29)|r2_hidden(X29,X27))))|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))|~l1_orders_2(X26))&((m1_subset_1(esk2_2(X26,X27),u1_struct_0(X26))|v13_waybel_0(X27,X26)|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))|~l1_orders_2(X26))&((m1_subset_1(esk3_2(X26,X27),u1_struct_0(X26))|v13_waybel_0(X27,X26)|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))|~l1_orders_2(X26))&(((r2_hidden(esk2_2(X26,X27),X27)|v13_waybel_0(X27,X26)|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))|~l1_orders_2(X26))&(r1_orders_2(X26,esk2_2(X26,X27),esk3_2(X26,X27))|v13_waybel_0(X27,X26)|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))|~l1_orders_2(X26)))&(~r2_hidden(esk3_2(X26,X27),X27)|v13_waybel_0(X27,X26)|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))|~l1_orders_2(X26)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d20_waybel_0])])])])])).
% 0.12/0.39  fof(c_0_17, plain, ![X15, X16, X17]:(~r2_hidden(X15,X16)|~m1_subset_1(X16,k1_zfmisc_1(X17))|m1_subset_1(X15,X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.12/0.39  fof(c_0_18, plain, ![X34, X35]:((~v1_subset_1(X35,X34)|X35!=X34|~m1_subset_1(X35,k1_zfmisc_1(X34)))&(X35=X34|v1_subset_1(X35,X34)|~m1_subset_1(X35,k1_zfmisc_1(X34)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).
% 0.12/0.39  fof(c_0_19, negated_conjecture, ((((((~v2_struct_0(esk4_0)&v3_orders_2(esk4_0))&v4_orders_2(esk4_0))&v5_orders_2(esk4_0))&v1_yellow_0(esk4_0))&l1_orders_2(esk4_0))&((((~v1_xboole_0(esk5_0)&v2_waybel_0(esk5_0,esk4_0))&v13_waybel_0(esk5_0,esk4_0))&m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0))))&((~v1_subset_1(esk5_0,u1_struct_0(esk4_0))|r2_hidden(k3_yellow_0(esk4_0),esk5_0))&(v1_subset_1(esk5_0,u1_struct_0(esk4_0))|~r2_hidden(k3_yellow_0(esk4_0),esk5_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).
% 0.12/0.39  fof(c_0_20, plain, ![X8, X9]:((m1_subset_1(esk1_2(X8,X9),X8)|X8=X9|~m1_subset_1(X9,k1_zfmisc_1(X8)))&(~r2_hidden(esk1_2(X8,X9),X9)|X8=X9|~m1_subset_1(X9,k1_zfmisc_1(X8)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t49_subset_1])])])])).
% 0.12/0.39  cnf(c_0_21, plain, (r2_hidden(X4,X1)|~v13_waybel_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X2))|~m1_subset_1(X4,u1_struct_0(X2))|~r2_hidden(X3,X1)|~r1_orders_2(X2,X3,X4)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.39  cnf(c_0_22, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.39  fof(c_0_23, plain, ![X19, X20]:(~l1_orders_2(X19)|m1_subset_1(k1_yellow_0(X19,X20),u1_struct_0(X19))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_yellow_0])])).
% 0.12/0.39  cnf(c_0_24, plain, (X1=X2|v1_subset_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.12/0.39  cnf(c_0_25, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.39  fof(c_0_26, plain, ![X32, X33]:((r1_yellow_0(X32,k5_waybel_0(X32,X33))|~m1_subset_1(X33,u1_struct_0(X32))|(v2_struct_0(X32)|~v3_orders_2(X32)|~v4_orders_2(X32)|~v5_orders_2(X32)|~l1_orders_2(X32)))&(k1_yellow_0(X32,k5_waybel_0(X32,X33))=X33|~m1_subset_1(X33,u1_struct_0(X32))|(v2_struct_0(X32)|~v3_orders_2(X32)|~v4_orders_2(X32)|~v5_orders_2(X32)|~l1_orders_2(X32)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_waybel_0])])])])])).
% 0.12/0.39  cnf(c_0_27, plain, (m1_subset_1(esk1_2(X1,X2),X1)|X1=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.39  cnf(c_0_28, plain, (r2_hidden(X1,X2)|~v13_waybel_0(X2,X3)|~r1_orders_2(X3,X4,X1)|~l1_orders_2(X3)|~r2_hidden(X4,X2)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~m1_subset_1(X1,u1_struct_0(X3))), inference(csr,[status(thm)],[c_0_21, c_0_22])).
% 0.12/0.39  cnf(c_0_29, plain, (m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.12/0.39  cnf(c_0_30, negated_conjecture, (r2_hidden(k3_yellow_0(esk4_0),esk5_0)|~v1_subset_1(esk5_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.39  cnf(c_0_31, negated_conjecture, (u1_struct_0(esk4_0)=esk5_0|v1_subset_1(esk5_0,u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.12/0.39  fof(c_0_32, plain, ![X18]:(~l1_orders_2(X18)|k3_yellow_0(X18)=k1_yellow_0(X18,k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_yellow_0])])).
% 0.12/0.39  fof(c_0_33, plain, ![X22, X23, X24]:(~l1_orders_2(X22)|(~r1_tarski(X23,X24)|~r1_yellow_0(X22,X23)|~r1_yellow_0(X22,X24)|r1_orders_2(X22,k1_yellow_0(X22,X23),k1_yellow_0(X22,X24)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_yellow_0])])])).
% 0.12/0.39  cnf(c_0_34, plain, (r1_yellow_0(X1,k5_waybel_0(X1,X2))|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.12/0.39  cnf(c_0_35, negated_conjecture, (u1_struct_0(esk4_0)=esk5_0|m1_subset_1(esk1_2(u1_struct_0(esk4_0),esk5_0),u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_27, c_0_25])).
% 0.12/0.39  cnf(c_0_36, negated_conjecture, (v4_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.39  cnf(c_0_37, negated_conjecture, (v3_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.39  cnf(c_0_38, negated_conjecture, (v5_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.39  cnf(c_0_39, negated_conjecture, (l1_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.39  cnf(c_0_40, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.39  fof(c_0_41, plain, ![X25]:((r1_yellow_0(X25,k1_xboole_0)|(v2_struct_0(X25)|~v5_orders_2(X25)|~v1_yellow_0(X25)|~l1_orders_2(X25)))&(r2_yellow_0(X25,u1_struct_0(X25))|(v2_struct_0(X25)|~v5_orders_2(X25)|~v1_yellow_0(X25)|~l1_orders_2(X25)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t42_yellow_0])])])])).
% 0.12/0.39  cnf(c_0_42, plain, (r2_hidden(k1_yellow_0(X1,X2),X3)|~v13_waybel_0(X3,X1)|~r1_orders_2(X1,X4,k1_yellow_0(X1,X2))|~l1_orders_2(X1)|~r2_hidden(X4,X3)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.12/0.39  cnf(c_0_43, negated_conjecture, (v13_waybel_0(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.39  cnf(c_0_44, negated_conjecture, (u1_struct_0(esk4_0)=esk5_0|r2_hidden(k3_yellow_0(esk4_0),esk5_0)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.12/0.39  cnf(c_0_45, plain, (k3_yellow_0(X1)=k1_yellow_0(X1,k1_xboole_0)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.12/0.39  cnf(c_0_46, plain, (r1_orders_2(X1,k1_yellow_0(X1,X2),k1_yellow_0(X1,X3))|~l1_orders_2(X1)|~r1_tarski(X2,X3)|~r1_yellow_0(X1,X2)|~r1_yellow_0(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.12/0.39  cnf(c_0_47, negated_conjecture, (u1_struct_0(esk4_0)=esk5_0|r1_yellow_0(esk4_0,k5_waybel_0(esk4_0,esk1_2(u1_struct_0(esk4_0),esk5_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36]), c_0_37]), c_0_38]), c_0_39])]), c_0_40])).
% 0.12/0.39  cnf(c_0_48, plain, (r1_yellow_0(X1,k1_xboole_0)|v2_struct_0(X1)|~v5_orders_2(X1)|~v1_yellow_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.12/0.39  cnf(c_0_49, negated_conjecture, (v1_yellow_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.39  fof(c_0_50, plain, ![X7]:r1_tarski(k1_xboole_0,X7), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.12/0.39  fof(c_0_51, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.12/0.39  cnf(c_0_52, negated_conjecture, (r2_hidden(k1_yellow_0(esk4_0,X1),esk5_0)|~r1_orders_2(esk4_0,X2,k1_yellow_0(esk4_0,X1))|~r2_hidden(X2,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_25]), c_0_43]), c_0_39])])).
% 0.12/0.39  cnf(c_0_53, negated_conjecture, (u1_struct_0(esk4_0)=esk5_0|r2_hidden(k1_yellow_0(esk4_0,k1_xboole_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_39])])).
% 0.12/0.39  cnf(c_0_54, negated_conjecture, (u1_struct_0(esk4_0)=esk5_0|r1_orders_2(esk4_0,k1_yellow_0(esk4_0,X1),k1_yellow_0(esk4_0,k5_waybel_0(esk4_0,esk1_2(u1_struct_0(esk4_0),esk5_0))))|~r1_yellow_0(esk4_0,X1)|~r1_tarski(X1,k5_waybel_0(esk4_0,esk1_2(u1_struct_0(esk4_0),esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_39])])).
% 0.12/0.39  cnf(c_0_55, negated_conjecture, (r1_yellow_0(esk4_0,k1_xboole_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_38]), c_0_39])]), c_0_40])).
% 0.12/0.39  cnf(c_0_56, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.12/0.39  fof(c_0_57, plain, ![X13, X14]:((~m1_subset_1(X13,k1_zfmisc_1(X14))|r1_tarski(X13,X14))&(~r1_tarski(X13,X14)|m1_subset_1(X13,k1_zfmisc_1(X14)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.12/0.39  cnf(c_0_58, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.12/0.39  cnf(c_0_59, negated_conjecture, (u1_struct_0(esk4_0)=esk5_0|r2_hidden(k1_yellow_0(esk4_0,X1),esk5_0)|~r1_orders_2(esk4_0,k1_yellow_0(esk4_0,k1_xboole_0),k1_yellow_0(esk4_0,X1))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.12/0.39  cnf(c_0_60, negated_conjecture, (u1_struct_0(esk4_0)=esk5_0|r1_orders_2(esk4_0,k1_yellow_0(esk4_0,k1_xboole_0),k1_yellow_0(esk4_0,k5_waybel_0(esk4_0,esk1_2(u1_struct_0(esk4_0),esk5_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56])])).
% 0.12/0.39  cnf(c_0_61, plain, (k1_yellow_0(X1,k5_waybel_0(X1,X2))=X2|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.12/0.39  cnf(c_0_62, plain, (X1=X2|~r2_hidden(esk1_2(X1,X2),X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.39  cnf(c_0_63, plain, (~v1_subset_1(X1,X2)|X1!=X2|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.12/0.39  cnf(c_0_64, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.12/0.39  cnf(c_0_65, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_58])).
% 0.12/0.39  fof(c_0_66, plain, ![X21]:(~l1_orders_2(X21)|m1_subset_1(k3_yellow_0(X21),u1_struct_0(X21))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_yellow_0])])).
% 0.12/0.39  cnf(c_0_67, negated_conjecture, (u1_struct_0(esk4_0)=esk5_0|r2_hidden(k1_yellow_0(esk4_0,k5_waybel_0(esk4_0,esk1_2(u1_struct_0(esk4_0),esk5_0))),esk5_0)), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.12/0.39  cnf(c_0_68, negated_conjecture, (k1_yellow_0(esk4_0,k5_waybel_0(esk4_0,esk1_2(u1_struct_0(esk4_0),esk5_0)))=esk1_2(u1_struct_0(esk4_0),esk5_0)|u1_struct_0(esk4_0)=esk5_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_35]), c_0_36]), c_0_37]), c_0_38]), c_0_39])]), c_0_40])).
% 0.12/0.39  cnf(c_0_69, negated_conjecture, (u1_struct_0(esk4_0)=esk5_0|~r2_hidden(esk1_2(u1_struct_0(esk4_0),esk5_0),esk5_0)), inference(spm,[status(thm)],[c_0_62, c_0_25])).
% 0.12/0.39  cnf(c_0_70, plain, (~v1_subset_1(X1,X1)|~m1_subset_1(X1,k1_zfmisc_1(X1))), inference(er,[status(thm)],[c_0_63])).
% 0.12/0.39  cnf(c_0_71, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.12/0.39  fof(c_0_72, plain, ![X11, X12]:(~m1_subset_1(X11,X12)|(v1_xboole_0(X12)|r2_hidden(X11,X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.12/0.39  cnf(c_0_73, plain, (m1_subset_1(k3_yellow_0(X1),u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.12/0.39  cnf(c_0_74, negated_conjecture, (u1_struct_0(esk4_0)=esk5_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_69])).
% 0.12/0.39  cnf(c_0_75, negated_conjecture, (v1_subset_1(esk5_0,u1_struct_0(esk4_0))|~r2_hidden(k3_yellow_0(esk4_0),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.39  cnf(c_0_76, plain, (~v1_subset_1(X1,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_71])])).
% 0.12/0.39  cnf(c_0_77, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.12/0.39  cnf(c_0_78, negated_conjecture, (m1_subset_1(k3_yellow_0(esk4_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_39])])).
% 0.12/0.39  cnf(c_0_79, negated_conjecture, (~v1_xboole_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.39  cnf(c_0_80, negated_conjecture, (~r2_hidden(k3_yellow_0(esk4_0),esk5_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_75, c_0_74]), c_0_76])).
% 0.12/0.39  cnf(c_0_81, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_79]), c_0_80]), ['proof']).
% 0.12/0.39  # SZS output end CNFRefutation
% 0.12/0.39  # Proof object total steps             : 82
% 0.12/0.39  # Proof object clause steps            : 51
% 0.12/0.39  # Proof object formula steps           : 31
% 0.12/0.39  # Proof object conjectures             : 31
% 0.12/0.39  # Proof object clause conjectures      : 28
% 0.12/0.39  # Proof object formula conjectures     : 3
% 0.12/0.39  # Proof object initial clauses used    : 28
% 0.12/0.39  # Proof object initial formulas used   : 15
% 0.12/0.39  # Proof object generating inferences   : 18
% 0.12/0.39  # Proof object simplifying inferences  : 37
% 0.12/0.39  # Training examples: 0 positive, 0 negative
% 0.12/0.39  # Parsed axioms                        : 15
% 0.12/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.39  # Initial clauses                      : 38
% 0.12/0.39  # Removed in clause preprocessing      : 0
% 0.12/0.39  # Initial clauses in saturation        : 38
% 0.12/0.39  # Processed clauses                    : 346
% 0.12/0.39  # ...of these trivial                  : 1
% 0.12/0.39  # ...subsumed                          : 144
% 0.12/0.39  # ...remaining for further processing  : 201
% 0.12/0.39  # Other redundant clauses eliminated   : 3
% 0.12/0.39  # Clauses deleted for lack of memory   : 0
% 0.12/0.39  # Backward-subsumed                    : 5
% 0.12/0.39  # Backward-rewritten                   : 73
% 0.12/0.39  # Generated clauses                    : 417
% 0.12/0.39  # ...of the previous two non-trivial   : 401
% 0.12/0.39  # Contextual simplify-reflections      : 3
% 0.12/0.39  # Paramodulations                      : 414
% 0.12/0.39  # Factorizations                       : 0
% 0.12/0.39  # Equation resolutions                 : 3
% 0.12/0.39  # Propositional unsat checks           : 0
% 0.12/0.39  #    Propositional check models        : 0
% 0.12/0.39  #    Propositional check unsatisfiable : 0
% 0.12/0.39  #    Propositional clauses             : 0
% 0.12/0.39  #    Propositional clauses after purity: 0
% 0.12/0.39  #    Propositional unsat core size     : 0
% 0.12/0.39  #    Propositional preprocessing time  : 0.000
% 0.12/0.39  #    Propositional encoding time       : 0.000
% 0.12/0.39  #    Propositional solver time         : 0.000
% 0.12/0.39  #    Success case prop preproc time    : 0.000
% 0.12/0.39  #    Success case prop encoding time   : 0.000
% 0.12/0.39  #    Success case prop solver time     : 0.000
% 0.12/0.39  # Current number of processed clauses  : 83
% 0.12/0.39  #    Positive orientable unit clauses  : 15
% 0.12/0.39  #    Positive unorientable unit clauses: 0
% 0.12/0.39  #    Negative unit clauses             : 5
% 0.12/0.39  #    Non-unit-clauses                  : 63
% 0.12/0.39  # Current number of unprocessed clauses: 129
% 0.12/0.39  # ...number of literals in the above   : 529
% 0.12/0.39  # Current number of archived formulas  : 0
% 0.12/0.39  # Current number of archived clauses   : 115
% 0.12/0.39  # Clause-clause subsumption calls (NU) : 1760
% 0.12/0.39  # Rec. Clause-clause subsumption calls : 768
% 0.12/0.39  # Non-unit clause-clause subsumptions  : 152
% 0.12/0.39  # Unit Clause-clause subsumption calls : 57
% 0.12/0.39  # Rewrite failures with RHS unbound    : 0
% 0.12/0.39  # BW rewrite match attempts            : 14
% 0.12/0.39  # BW rewrite match successes           : 2
% 0.12/0.39  # Condensation attempts                : 0
% 0.12/0.39  # Condensation successes               : 0
% 0.12/0.39  # Termbank termtop insertions          : 11547
% 0.12/0.39  
% 0.12/0.39  # -------------------------------------------------
% 0.12/0.39  # User time                : 0.047 s
% 0.12/0.39  # System time              : 0.004 s
% 0.12/0.39  # Total time               : 0.052 s
% 0.12/0.39  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
