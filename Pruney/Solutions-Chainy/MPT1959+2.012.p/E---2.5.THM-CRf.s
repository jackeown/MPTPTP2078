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
% DateTime   : Thu Dec  3 11:21:24 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 381 expanded)
%              Number of clauses        :   58 ( 147 expanded)
%              Number of leaves         :   16 (  92 expanded)
%              Depth                    :   14
%              Number of atoms          :  337 (2655 expanded)
%              Number of equality atoms :   37 ( 104 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   28 (   3 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_7)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(t2_tarski,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
        <=> r2_hidden(X3,X2) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_waybel_0)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(d7_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( v1_subset_1(X2,X1)
      <=> X2 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(dt_k1_yellow_0,axiom,(
    ! [X1,X2] :
      ( l1_orders_2(X1)
     => m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_0)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_waybel_0)).

fof(d11_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => k3_yellow_0(X1) = k1_yellow_0(X1,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_yellow_0)).

fof(t34_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2,X3] :
          ( ( r1_tarski(X2,X3)
            & r1_yellow_0(X1,X2)
            & r1_yellow_0(X1,X3) )
         => r1_orders_2(X1,k1_yellow_0(X1,X2),k1_yellow_0(X1,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_yellow_0)).

fof(t42_yellow_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v5_orders_2(X1)
        & v1_yellow_0(X1)
        & l1_orders_2(X1) )
     => ( r1_yellow_0(X1,k1_xboole_0)
        & r2_yellow_0(X1,u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_yellow_0)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(c_0_16,negated_conjecture,(
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

fof(c_0_17,plain,(
    ! [X11,X12,X13] :
      ( ~ m1_subset_1(X12,k1_zfmisc_1(X11))
      | ~ r2_hidden(X13,X12)
      | r2_hidden(X13,X11) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

fof(c_0_18,negated_conjecture,
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
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])).

cnf(c_0_19,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_21,plain,(
    ! [X5,X6] :
      ( ( ~ r2_hidden(esk1_2(X5,X6),X5)
        | ~ r2_hidden(esk1_2(X5,X6),X6)
        | X5 = X6 )
      & ( r2_hidden(esk1_2(X5,X6),X5)
        | r2_hidden(esk1_2(X5,X6),X6)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(X1,u1_struct_0(esk4_0))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_23,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r2_hidden(esk1_2(X1,X2),X2)
    | X1 = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_24,plain,(
    ! [X30,X31,X32,X33] :
      ( ( ~ v13_waybel_0(X31,X30)
        | ~ m1_subset_1(X32,u1_struct_0(X30))
        | ~ m1_subset_1(X33,u1_struct_0(X30))
        | ~ r2_hidden(X32,X31)
        | ~ r1_orders_2(X30,X32,X33)
        | r2_hidden(X33,X31)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ l1_orders_2(X30) )
      & ( m1_subset_1(esk2_2(X30,X31),u1_struct_0(X30))
        | v13_waybel_0(X31,X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ l1_orders_2(X30) )
      & ( m1_subset_1(esk3_2(X30,X31),u1_struct_0(X30))
        | v13_waybel_0(X31,X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ l1_orders_2(X30) )
      & ( r2_hidden(esk2_2(X30,X31),X31)
        | v13_waybel_0(X31,X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ l1_orders_2(X30) )
      & ( r1_orders_2(X30,esk2_2(X30,X31),esk3_2(X30,X31))
        | v13_waybel_0(X31,X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ l1_orders_2(X30) )
      & ( ~ r2_hidden(esk3_2(X30,X31),X31)
        | v13_waybel_0(X31,X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ l1_orders_2(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d20_waybel_0])])])])])).

fof(c_0_25,plain,(
    ! [X20,X21,X22] :
      ( ~ r2_hidden(X20,X21)
      | ~ m1_subset_1(X21,k1_zfmisc_1(X22))
      | m1_subset_1(X20,X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_26,plain,(
    ! [X38,X39] :
      ( ( ~ v1_subset_1(X39,X38)
        | X39 != X38
        | ~ m1_subset_1(X39,k1_zfmisc_1(X38)) )
      & ( X39 = X38
        | v1_subset_1(X39,X38)
        | ~ m1_subset_1(X39,k1_zfmisc_1(X38)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).

fof(c_0_27,plain,(
    ! [X14,X15] :
      ( ~ r2_hidden(X14,X15)
      | m1_subset_1(X14,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_28,negated_conjecture,
    ( esk5_0 = X1
    | r2_hidden(esk1_2(esk5_0,X1),u1_struct_0(esk4_0))
    | r2_hidden(esk1_2(esk5_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_29,plain,
    ( r2_hidden(X4,X1)
    | ~ v13_waybel_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r2_hidden(X3,X1)
    | ~ r1_orders_2(X2,X3,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_31,plain,(
    ! [X24,X25] :
      ( ~ l1_orders_2(X24)
      | m1_subset_1(k1_yellow_0(X24,X25),u1_struct_0(X24)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_yellow_0])])).

cnf(c_0_32,plain,
    ( X1 = X2
    | v1_subset_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_33,plain,(
    ! [X36,X37] :
      ( ( r1_yellow_0(X36,k5_waybel_0(X36,X37))
        | ~ m1_subset_1(X37,u1_struct_0(X36))
        | v2_struct_0(X36)
        | ~ v3_orders_2(X36)
        | ~ v4_orders_2(X36)
        | ~ v5_orders_2(X36)
        | ~ l1_orders_2(X36) )
      & ( k1_yellow_0(X36,k5_waybel_0(X36,X37)) = X37
        | ~ m1_subset_1(X37,u1_struct_0(X36))
        | v2_struct_0(X36)
        | ~ v3_orders_2(X36)
        | ~ v4_orders_2(X36)
        | ~ v5_orders_2(X36)
        | ~ l1_orders_2(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_waybel_0])])])])])).

cnf(c_0_34,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,negated_conjecture,
    ( u1_struct_0(esk4_0) = esk5_0
    | r2_hidden(esk1_2(esk5_0,u1_struct_0(esk4_0)),u1_struct_0(esk4_0)) ),
    inference(ef,[status(thm)],[c_0_28])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,X2)
    | ~ v13_waybel_0(X2,X3)
    | ~ r1_orders_2(X3,X4,X1)
    | ~ l1_orders_2(X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ r2_hidden(X4,X2) ),
    inference(csr,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_37,plain,
    ( m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(k3_yellow_0(esk4_0),esk5_0)
    | ~ v1_subset_1(esk5_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_39,negated_conjecture,
    ( u1_struct_0(esk4_0) = esk5_0
    | v1_subset_1(esk5_0,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_20])).

fof(c_0_40,plain,(
    ! [X23] :
      ( ~ l1_orders_2(X23)
      | k3_yellow_0(X23) = k1_yellow_0(X23,k1_xboole_0) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_yellow_0])])).

fof(c_0_41,plain,(
    ! [X26,X27,X28] :
      ( ~ l1_orders_2(X26)
      | ~ r1_tarski(X27,X28)
      | ~ r1_yellow_0(X26,X27)
      | ~ r1_yellow_0(X26,X28)
      | r1_orders_2(X26,k1_yellow_0(X26,X27),k1_yellow_0(X26,X28)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_yellow_0])])])).

cnf(c_0_42,plain,
    ( r1_yellow_0(X1,k5_waybel_0(X1,X2))
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_43,negated_conjecture,
    ( u1_struct_0(esk4_0) = esk5_0
    | m1_subset_1(esk1_2(esk5_0,u1_struct_0(esk4_0)),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_44,negated_conjecture,
    ( v4_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_45,negated_conjecture,
    ( v3_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_46,negated_conjecture,
    ( v5_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_47,negated_conjecture,
    ( l1_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_48,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_49,plain,(
    ! [X29] :
      ( ( r1_yellow_0(X29,k1_xboole_0)
        | v2_struct_0(X29)
        | ~ v5_orders_2(X29)
        | ~ v1_yellow_0(X29)
        | ~ l1_orders_2(X29) )
      & ( r2_yellow_0(X29,u1_struct_0(X29))
        | v2_struct_0(X29)
        | ~ v5_orders_2(X29)
        | ~ v1_yellow_0(X29)
        | ~ l1_orders_2(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t42_yellow_0])])])])).

cnf(c_0_50,plain,
    ( r2_hidden(k1_yellow_0(X1,X2),X3)
    | ~ v13_waybel_0(X3,X1)
    | ~ r1_orders_2(X1,X4,k1_yellow_0(X1,X2))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X4,X3) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_51,negated_conjecture,
    ( v13_waybel_0(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_52,negated_conjecture,
    ( u1_struct_0(esk4_0) = esk5_0
    | r2_hidden(k3_yellow_0(esk4_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_53,plain,
    ( k3_yellow_0(X1) = k1_yellow_0(X1,k1_xboole_0)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_54,plain,
    ( r1_orders_2(X1,k1_yellow_0(X1,X2),k1_yellow_0(X1,X3))
    | ~ l1_orders_2(X1)
    | ~ r1_tarski(X2,X3)
    | ~ r1_yellow_0(X1,X2)
    | ~ r1_yellow_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_55,negated_conjecture,
    ( u1_struct_0(esk4_0) = esk5_0
    | r1_yellow_0(esk4_0,k5_waybel_0(esk4_0,esk1_2(esk5_0,u1_struct_0(esk4_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44]),c_0_45]),c_0_46]),c_0_47])]),c_0_48])).

cnf(c_0_56,plain,
    ( r1_yellow_0(X1,k1_xboole_0)
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_yellow_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_57,negated_conjecture,
    ( v1_yellow_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_58,plain,(
    ! [X10] : r1_tarski(k1_xboole_0,X10) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_59,plain,(
    ! [X8,X9] :
      ( ( r1_tarski(X8,X9)
        | X8 != X9 )
      & ( r1_tarski(X9,X8)
        | X8 != X9 )
      & ( ~ r1_tarski(X8,X9)
        | ~ r1_tarski(X9,X8)
        | X8 = X9 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(k1_yellow_0(esk4_0,X1),esk5_0)
    | ~ r1_orders_2(esk4_0,X2,k1_yellow_0(esk4_0,X1))
    | ~ r2_hidden(X2,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_20]),c_0_51]),c_0_47])])).

cnf(c_0_61,negated_conjecture,
    ( u1_struct_0(esk4_0) = esk5_0
    | r2_hidden(k1_yellow_0(esk4_0,k1_xboole_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_47])])).

cnf(c_0_62,negated_conjecture,
    ( u1_struct_0(esk4_0) = esk5_0
    | r1_orders_2(esk4_0,k1_yellow_0(esk4_0,X1),k1_yellow_0(esk4_0,k5_waybel_0(esk4_0,esk1_2(esk5_0,u1_struct_0(esk4_0)))))
    | ~ r1_yellow_0(esk4_0,X1)
    | ~ r1_tarski(X1,k5_waybel_0(esk4_0,esk1_2(esk5_0,u1_struct_0(esk4_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_47])])).

cnf(c_0_63,negated_conjecture,
    ( r1_yellow_0(esk4_0,k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_46]),c_0_47])]),c_0_48])).

cnf(c_0_64,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

fof(c_0_65,plain,(
    ! [X18,X19] :
      ( ( ~ m1_subset_1(X18,k1_zfmisc_1(X19))
        | r1_tarski(X18,X19) )
      & ( ~ r1_tarski(X18,X19)
        | m1_subset_1(X18,k1_zfmisc_1(X19)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_66,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_67,negated_conjecture,
    ( u1_struct_0(esk4_0) = esk5_0
    | r2_hidden(k1_yellow_0(esk4_0,X1),esk5_0)
    | ~ r1_orders_2(esk4_0,k1_yellow_0(esk4_0,k1_xboole_0),k1_yellow_0(esk4_0,X1)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_68,negated_conjecture,
    ( u1_struct_0(esk4_0) = esk5_0
    | r1_orders_2(esk4_0,k1_yellow_0(esk4_0,k1_xboole_0),k1_yellow_0(esk4_0,k5_waybel_0(esk4_0,esk1_2(esk5_0,u1_struct_0(esk4_0))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64])])).

cnf(c_0_69,plain,
    ( k1_yellow_0(X1,k5_waybel_0(X1,X2)) = X2
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_70,plain,
    ( X1 = X2
    | m1_subset_1(esk1_2(X1,X2),X2)
    | r2_hidden(esk1_2(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_23])).

cnf(c_0_71,plain,
    ( X1 = X2
    | ~ r2_hidden(esk1_2(X1,X2),X1)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_72,plain,
    ( ~ v1_subset_1(X1,X2)
    | X1 != X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_73,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_74,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_66])).

fof(c_0_75,plain,(
    ! [X16,X17] :
      ( ~ m1_subset_1(X16,X17)
      | v1_xboole_0(X17)
      | r2_hidden(X16,X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_76,negated_conjecture,
    ( v1_subset_1(esk5_0,u1_struct_0(esk4_0))
    | ~ r2_hidden(k3_yellow_0(esk4_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_77,negated_conjecture,
    ( u1_struct_0(esk4_0) = esk5_0
    | r2_hidden(k1_yellow_0(esk4_0,k5_waybel_0(esk4_0,esk1_2(esk5_0,u1_struct_0(esk4_0)))),esk5_0) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_78,plain,
    ( k1_yellow_0(X1,k5_waybel_0(X1,esk1_2(X2,u1_struct_0(X1)))) = esk1_2(X2,u1_struct_0(X1))
    | X2 = u1_struct_0(X1)
    | v2_struct_0(X1)
    | r2_hidden(esk1_2(X2,u1_struct_0(X1)),X2)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_79,negated_conjecture,
    ( u1_struct_0(esk4_0) = esk5_0
    | ~ r2_hidden(esk1_2(esk5_0,u1_struct_0(esk4_0)),esk5_0) ),
    inference(spm,[status(thm)],[c_0_71,c_0_35])).

cnf(c_0_80,plain,
    ( ~ v1_subset_1(X1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(er,[status(thm)],[c_0_72])).

cnf(c_0_81,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_82,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_83,negated_conjecture,
    ( v1_subset_1(esk5_0,u1_struct_0(esk4_0))
    | ~ r2_hidden(k1_yellow_0(esk4_0,k1_xboole_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_53]),c_0_47])])).

cnf(c_0_84,negated_conjecture,
    ( u1_struct_0(esk4_0) = esk5_0 ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_44]),c_0_45]),c_0_46]),c_0_47])]),c_0_48]),c_0_79])).

cnf(c_0_85,plain,
    ( ~ v1_subset_1(X1,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_81])])).

cnf(c_0_86,plain,
    ( v1_xboole_0(u1_struct_0(X1))
    | r2_hidden(k1_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_82,c_0_37])).

cnf(c_0_87,negated_conjecture,
    ( ~ v1_xboole_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_88,negated_conjecture,
    ( ~ r2_hidden(k1_yellow_0(esk4_0,k1_xboole_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_83,c_0_84]),c_0_85])).

cnf(c_0_89,negated_conjecture,
    ( r2_hidden(k1_yellow_0(esk4_0,X1),esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_84]),c_0_47])]),c_0_87])).

cnf(c_0_90,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_88,c_0_89])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:11:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.45  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_SE_CS_SP_PI_PS_S2S
% 0.19/0.45  # and selection function SelectNewComplexAHP.
% 0.19/0.45  #
% 0.19/0.45  # Preprocessing time       : 0.028 s
% 0.19/0.45  # Presaturation interreduction done
% 0.19/0.45  
% 0.19/0.45  # Proof found!
% 0.19/0.45  # SZS status Theorem
% 0.19/0.45  # SZS output start CNFRefutation
% 0.19/0.45  fof(t8_waybel_7, conjecture, ![X1]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&v1_yellow_0(X1))&l1_orders_2(X1))=>![X2]:((((~(v1_xboole_0(X2))&v2_waybel_0(X2,X1))&v13_waybel_0(X2,X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v1_subset_1(X2,u1_struct_0(X1))<=>~(r2_hidden(k3_yellow_0(X1),X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_waybel_7)).
% 0.19/0.45  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 0.19/0.45  fof(t2_tarski, axiom, ![X1, X2]:(![X3]:(r2_hidden(X3,X1)<=>r2_hidden(X3,X2))=>X1=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 0.19/0.45  fof(d20_waybel_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v13_waybel_0(X2,X1)<=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((r2_hidden(X3,X2)&r1_orders_2(X1,X3,X4))=>r2_hidden(X4,X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d20_waybel_0)).
% 0.19/0.45  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.19/0.45  fof(d7_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(v1_subset_1(X2,X1)<=>X2!=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 0.19/0.45  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 0.19/0.45  fof(dt_k1_yellow_0, axiom, ![X1, X2]:(l1_orders_2(X1)=>m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_yellow_0)).
% 0.19/0.45  fof(t34_waybel_0, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(r1_yellow_0(X1,k5_waybel_0(X1,X2))&k1_yellow_0(X1,k5_waybel_0(X1,X2))=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_waybel_0)).
% 0.19/0.45  fof(d11_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>k3_yellow_0(X1)=k1_yellow_0(X1,k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_yellow_0)).
% 0.19/0.45  fof(t34_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(((r1_tarski(X2,X3)&r1_yellow_0(X1,X2))&r1_yellow_0(X1,X3))=>r1_orders_2(X1,k1_yellow_0(X1,X2),k1_yellow_0(X1,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_yellow_0)).
% 0.19/0.45  fof(t42_yellow_0, axiom, ![X1]:((((~(v2_struct_0(X1))&v5_orders_2(X1))&v1_yellow_0(X1))&l1_orders_2(X1))=>(r1_yellow_0(X1,k1_xboole_0)&r2_yellow_0(X1,u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_yellow_0)).
% 0.19/0.45  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.19/0.45  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.45  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.45  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 0.19/0.45  fof(c_0_16, negated_conjecture, ~(![X1]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&v1_yellow_0(X1))&l1_orders_2(X1))=>![X2]:((((~(v1_xboole_0(X2))&v2_waybel_0(X2,X1))&v13_waybel_0(X2,X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v1_subset_1(X2,u1_struct_0(X1))<=>~(r2_hidden(k3_yellow_0(X1),X2)))))), inference(assume_negation,[status(cth)],[t8_waybel_7])).
% 0.19/0.45  fof(c_0_17, plain, ![X11, X12, X13]:(~m1_subset_1(X12,k1_zfmisc_1(X11))|(~r2_hidden(X13,X12)|r2_hidden(X13,X11))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.19/0.45  fof(c_0_18, negated_conjecture, ((((((~v2_struct_0(esk4_0)&v3_orders_2(esk4_0))&v4_orders_2(esk4_0))&v5_orders_2(esk4_0))&v1_yellow_0(esk4_0))&l1_orders_2(esk4_0))&((((~v1_xboole_0(esk5_0)&v2_waybel_0(esk5_0,esk4_0))&v13_waybel_0(esk5_0,esk4_0))&m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0))))&((~v1_subset_1(esk5_0,u1_struct_0(esk4_0))|r2_hidden(k3_yellow_0(esk4_0),esk5_0))&(v1_subset_1(esk5_0,u1_struct_0(esk4_0))|~r2_hidden(k3_yellow_0(esk4_0),esk5_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])).
% 0.19/0.45  cnf(c_0_19, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.45  cnf(c_0_20, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.45  fof(c_0_21, plain, ![X5, X6]:((~r2_hidden(esk1_2(X5,X6),X5)|~r2_hidden(esk1_2(X5,X6),X6)|X5=X6)&(r2_hidden(esk1_2(X5,X6),X5)|r2_hidden(esk1_2(X5,X6),X6)|X5=X6)), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).
% 0.19/0.45  cnf(c_0_22, negated_conjecture, (r2_hidden(X1,u1_struct_0(esk4_0))|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.19/0.45  cnf(c_0_23, plain, (r2_hidden(esk1_2(X1,X2),X1)|r2_hidden(esk1_2(X1,X2),X2)|X1=X2), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.45  fof(c_0_24, plain, ![X30, X31, X32, X33]:((~v13_waybel_0(X31,X30)|(~m1_subset_1(X32,u1_struct_0(X30))|(~m1_subset_1(X33,u1_struct_0(X30))|(~r2_hidden(X32,X31)|~r1_orders_2(X30,X32,X33)|r2_hidden(X33,X31))))|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))|~l1_orders_2(X30))&((m1_subset_1(esk2_2(X30,X31),u1_struct_0(X30))|v13_waybel_0(X31,X30)|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))|~l1_orders_2(X30))&((m1_subset_1(esk3_2(X30,X31),u1_struct_0(X30))|v13_waybel_0(X31,X30)|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))|~l1_orders_2(X30))&(((r2_hidden(esk2_2(X30,X31),X31)|v13_waybel_0(X31,X30)|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))|~l1_orders_2(X30))&(r1_orders_2(X30,esk2_2(X30,X31),esk3_2(X30,X31))|v13_waybel_0(X31,X30)|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))|~l1_orders_2(X30)))&(~r2_hidden(esk3_2(X30,X31),X31)|v13_waybel_0(X31,X30)|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))|~l1_orders_2(X30)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d20_waybel_0])])])])])).
% 0.19/0.45  fof(c_0_25, plain, ![X20, X21, X22]:(~r2_hidden(X20,X21)|~m1_subset_1(X21,k1_zfmisc_1(X22))|m1_subset_1(X20,X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.19/0.45  fof(c_0_26, plain, ![X38, X39]:((~v1_subset_1(X39,X38)|X39!=X38|~m1_subset_1(X39,k1_zfmisc_1(X38)))&(X39=X38|v1_subset_1(X39,X38)|~m1_subset_1(X39,k1_zfmisc_1(X38)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).
% 0.19/0.45  fof(c_0_27, plain, ![X14, X15]:(~r2_hidden(X14,X15)|m1_subset_1(X14,X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.19/0.45  cnf(c_0_28, negated_conjecture, (esk5_0=X1|r2_hidden(esk1_2(esk5_0,X1),u1_struct_0(esk4_0))|r2_hidden(esk1_2(esk5_0,X1),X1)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.19/0.45  cnf(c_0_29, plain, (r2_hidden(X4,X1)|~v13_waybel_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X2))|~m1_subset_1(X4,u1_struct_0(X2))|~r2_hidden(X3,X1)|~r1_orders_2(X2,X3,X4)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.45  cnf(c_0_30, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.45  fof(c_0_31, plain, ![X24, X25]:(~l1_orders_2(X24)|m1_subset_1(k1_yellow_0(X24,X25),u1_struct_0(X24))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_yellow_0])])).
% 0.19/0.45  cnf(c_0_32, plain, (X1=X2|v1_subset_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.45  fof(c_0_33, plain, ![X36, X37]:((r1_yellow_0(X36,k5_waybel_0(X36,X37))|~m1_subset_1(X37,u1_struct_0(X36))|(v2_struct_0(X36)|~v3_orders_2(X36)|~v4_orders_2(X36)|~v5_orders_2(X36)|~l1_orders_2(X36)))&(k1_yellow_0(X36,k5_waybel_0(X36,X37))=X37|~m1_subset_1(X37,u1_struct_0(X36))|(v2_struct_0(X36)|~v3_orders_2(X36)|~v4_orders_2(X36)|~v5_orders_2(X36)|~l1_orders_2(X36)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_waybel_0])])])])])).
% 0.19/0.45  cnf(c_0_34, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.45  cnf(c_0_35, negated_conjecture, (u1_struct_0(esk4_0)=esk5_0|r2_hidden(esk1_2(esk5_0,u1_struct_0(esk4_0)),u1_struct_0(esk4_0))), inference(ef,[status(thm)],[c_0_28])).
% 0.19/0.45  cnf(c_0_36, plain, (r2_hidden(X1,X2)|~v13_waybel_0(X2,X3)|~r1_orders_2(X3,X4,X1)|~l1_orders_2(X3)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~m1_subset_1(X1,u1_struct_0(X3))|~r2_hidden(X4,X2)), inference(csr,[status(thm)],[c_0_29, c_0_30])).
% 0.19/0.45  cnf(c_0_37, plain, (m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.45  cnf(c_0_38, negated_conjecture, (r2_hidden(k3_yellow_0(esk4_0),esk5_0)|~v1_subset_1(esk5_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.45  cnf(c_0_39, negated_conjecture, (u1_struct_0(esk4_0)=esk5_0|v1_subset_1(esk5_0,u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_32, c_0_20])).
% 0.19/0.45  fof(c_0_40, plain, ![X23]:(~l1_orders_2(X23)|k3_yellow_0(X23)=k1_yellow_0(X23,k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_yellow_0])])).
% 0.19/0.45  fof(c_0_41, plain, ![X26, X27, X28]:(~l1_orders_2(X26)|(~r1_tarski(X27,X28)|~r1_yellow_0(X26,X27)|~r1_yellow_0(X26,X28)|r1_orders_2(X26,k1_yellow_0(X26,X27),k1_yellow_0(X26,X28)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_yellow_0])])])).
% 0.19/0.45  cnf(c_0_42, plain, (r1_yellow_0(X1,k5_waybel_0(X1,X2))|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.45  cnf(c_0_43, negated_conjecture, (u1_struct_0(esk4_0)=esk5_0|m1_subset_1(esk1_2(esk5_0,u1_struct_0(esk4_0)),u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.19/0.45  cnf(c_0_44, negated_conjecture, (v4_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.45  cnf(c_0_45, negated_conjecture, (v3_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.45  cnf(c_0_46, negated_conjecture, (v5_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.45  cnf(c_0_47, negated_conjecture, (l1_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.45  cnf(c_0_48, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.45  fof(c_0_49, plain, ![X29]:((r1_yellow_0(X29,k1_xboole_0)|(v2_struct_0(X29)|~v5_orders_2(X29)|~v1_yellow_0(X29)|~l1_orders_2(X29)))&(r2_yellow_0(X29,u1_struct_0(X29))|(v2_struct_0(X29)|~v5_orders_2(X29)|~v1_yellow_0(X29)|~l1_orders_2(X29)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t42_yellow_0])])])])).
% 0.19/0.45  cnf(c_0_50, plain, (r2_hidden(k1_yellow_0(X1,X2),X3)|~v13_waybel_0(X3,X1)|~r1_orders_2(X1,X4,k1_yellow_0(X1,X2))|~l1_orders_2(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(X4,X3)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.19/0.45  cnf(c_0_51, negated_conjecture, (v13_waybel_0(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.45  cnf(c_0_52, negated_conjecture, (u1_struct_0(esk4_0)=esk5_0|r2_hidden(k3_yellow_0(esk4_0),esk5_0)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.19/0.45  cnf(c_0_53, plain, (k3_yellow_0(X1)=k1_yellow_0(X1,k1_xboole_0)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.45  cnf(c_0_54, plain, (r1_orders_2(X1,k1_yellow_0(X1,X2),k1_yellow_0(X1,X3))|~l1_orders_2(X1)|~r1_tarski(X2,X3)|~r1_yellow_0(X1,X2)|~r1_yellow_0(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.19/0.45  cnf(c_0_55, negated_conjecture, (u1_struct_0(esk4_0)=esk5_0|r1_yellow_0(esk4_0,k5_waybel_0(esk4_0,esk1_2(esk5_0,u1_struct_0(esk4_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44]), c_0_45]), c_0_46]), c_0_47])]), c_0_48])).
% 0.19/0.45  cnf(c_0_56, plain, (r1_yellow_0(X1,k1_xboole_0)|v2_struct_0(X1)|~v5_orders_2(X1)|~v1_yellow_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.19/0.45  cnf(c_0_57, negated_conjecture, (v1_yellow_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.45  fof(c_0_58, plain, ![X10]:r1_tarski(k1_xboole_0,X10), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.19/0.45  fof(c_0_59, plain, ![X8, X9]:(((r1_tarski(X8,X9)|X8!=X9)&(r1_tarski(X9,X8)|X8!=X9))&(~r1_tarski(X8,X9)|~r1_tarski(X9,X8)|X8=X9)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.45  cnf(c_0_60, negated_conjecture, (r2_hidden(k1_yellow_0(esk4_0,X1),esk5_0)|~r1_orders_2(esk4_0,X2,k1_yellow_0(esk4_0,X1))|~r2_hidden(X2,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_20]), c_0_51]), c_0_47])])).
% 0.19/0.45  cnf(c_0_61, negated_conjecture, (u1_struct_0(esk4_0)=esk5_0|r2_hidden(k1_yellow_0(esk4_0,k1_xboole_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_47])])).
% 0.19/0.45  cnf(c_0_62, negated_conjecture, (u1_struct_0(esk4_0)=esk5_0|r1_orders_2(esk4_0,k1_yellow_0(esk4_0,X1),k1_yellow_0(esk4_0,k5_waybel_0(esk4_0,esk1_2(esk5_0,u1_struct_0(esk4_0)))))|~r1_yellow_0(esk4_0,X1)|~r1_tarski(X1,k5_waybel_0(esk4_0,esk1_2(esk5_0,u1_struct_0(esk4_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_47])])).
% 0.19/0.45  cnf(c_0_63, negated_conjecture, (r1_yellow_0(esk4_0,k1_xboole_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_46]), c_0_47])]), c_0_48])).
% 0.19/0.45  cnf(c_0_64, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.19/0.45  fof(c_0_65, plain, ![X18, X19]:((~m1_subset_1(X18,k1_zfmisc_1(X19))|r1_tarski(X18,X19))&(~r1_tarski(X18,X19)|m1_subset_1(X18,k1_zfmisc_1(X19)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.45  cnf(c_0_66, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.19/0.45  cnf(c_0_67, negated_conjecture, (u1_struct_0(esk4_0)=esk5_0|r2_hidden(k1_yellow_0(esk4_0,X1),esk5_0)|~r1_orders_2(esk4_0,k1_yellow_0(esk4_0,k1_xboole_0),k1_yellow_0(esk4_0,X1))), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.19/0.45  cnf(c_0_68, negated_conjecture, (u1_struct_0(esk4_0)=esk5_0|r1_orders_2(esk4_0,k1_yellow_0(esk4_0,k1_xboole_0),k1_yellow_0(esk4_0,k5_waybel_0(esk4_0,esk1_2(esk5_0,u1_struct_0(esk4_0)))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_64])])).
% 0.19/0.45  cnf(c_0_69, plain, (k1_yellow_0(X1,k5_waybel_0(X1,X2))=X2|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.45  cnf(c_0_70, plain, (X1=X2|m1_subset_1(esk1_2(X1,X2),X2)|r2_hidden(esk1_2(X1,X2),X1)), inference(spm,[status(thm)],[c_0_34, c_0_23])).
% 0.19/0.45  cnf(c_0_71, plain, (X1=X2|~r2_hidden(esk1_2(X1,X2),X1)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.45  cnf(c_0_72, plain, (~v1_subset_1(X1,X2)|X1!=X2|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.45  cnf(c_0_73, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.19/0.45  cnf(c_0_74, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_66])).
% 0.19/0.45  fof(c_0_75, plain, ![X16, X17]:(~m1_subset_1(X16,X17)|(v1_xboole_0(X17)|r2_hidden(X16,X17))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.19/0.45  cnf(c_0_76, negated_conjecture, (v1_subset_1(esk5_0,u1_struct_0(esk4_0))|~r2_hidden(k3_yellow_0(esk4_0),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.45  cnf(c_0_77, negated_conjecture, (u1_struct_0(esk4_0)=esk5_0|r2_hidden(k1_yellow_0(esk4_0,k5_waybel_0(esk4_0,esk1_2(esk5_0,u1_struct_0(esk4_0)))),esk5_0)), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.19/0.45  cnf(c_0_78, plain, (k1_yellow_0(X1,k5_waybel_0(X1,esk1_2(X2,u1_struct_0(X1))))=esk1_2(X2,u1_struct_0(X1))|X2=u1_struct_0(X1)|v2_struct_0(X1)|r2_hidden(esk1_2(X2,u1_struct_0(X1)),X2)|~v4_orders_2(X1)|~v3_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.19/0.45  cnf(c_0_79, negated_conjecture, (u1_struct_0(esk4_0)=esk5_0|~r2_hidden(esk1_2(esk5_0,u1_struct_0(esk4_0)),esk5_0)), inference(spm,[status(thm)],[c_0_71, c_0_35])).
% 0.19/0.45  cnf(c_0_80, plain, (~v1_subset_1(X1,X1)|~m1_subset_1(X1,k1_zfmisc_1(X1))), inference(er,[status(thm)],[c_0_72])).
% 0.19/0.45  cnf(c_0_81, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.19/0.45  cnf(c_0_82, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.19/0.45  cnf(c_0_83, negated_conjecture, (v1_subset_1(esk5_0,u1_struct_0(esk4_0))|~r2_hidden(k1_yellow_0(esk4_0,k1_xboole_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_53]), c_0_47])])).
% 0.19/0.45  cnf(c_0_84, negated_conjecture, (u1_struct_0(esk4_0)=esk5_0), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_44]), c_0_45]), c_0_46]), c_0_47])]), c_0_48]), c_0_79])).
% 0.19/0.45  cnf(c_0_85, plain, (~v1_subset_1(X1,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_80, c_0_81])])).
% 0.19/0.45  cnf(c_0_86, plain, (v1_xboole_0(u1_struct_0(X1))|r2_hidden(k1_yellow_0(X1,X2),u1_struct_0(X1))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_82, c_0_37])).
% 0.19/0.45  cnf(c_0_87, negated_conjecture, (~v1_xboole_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.45  cnf(c_0_88, negated_conjecture, (~r2_hidden(k1_yellow_0(esk4_0,k1_xboole_0),esk5_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_83, c_0_84]), c_0_85])).
% 0.19/0.45  cnf(c_0_89, negated_conjecture, (r2_hidden(k1_yellow_0(esk4_0,X1),esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_84]), c_0_47])]), c_0_87])).
% 0.19/0.45  cnf(c_0_90, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_88, c_0_89])]), ['proof']).
% 0.19/0.45  # SZS output end CNFRefutation
% 0.19/0.45  # Proof object total steps             : 91
% 0.19/0.45  # Proof object clause steps            : 58
% 0.19/0.45  # Proof object formula steps           : 33
% 0.19/0.45  # Proof object conjectures             : 34
% 0.19/0.45  # Proof object clause conjectures      : 31
% 0.19/0.45  # Proof object formula conjectures     : 3
% 0.19/0.45  # Proof object initial clauses used    : 29
% 0.19/0.45  # Proof object initial formulas used   : 16
% 0.19/0.45  # Proof object generating inferences   : 23
% 0.19/0.45  # Proof object simplifying inferences  : 40
% 0.19/0.45  # Training examples: 0 positive, 0 negative
% 0.19/0.45  # Parsed axioms                        : 16
% 0.19/0.45  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.45  # Initial clauses                      : 39
% 0.19/0.45  # Removed in clause preprocessing      : 0
% 0.19/0.45  # Initial clauses in saturation        : 39
% 0.19/0.45  # Processed clauses                    : 817
% 0.19/0.45  # ...of these trivial                  : 1
% 0.19/0.45  # ...subsumed                          : 424
% 0.19/0.45  # ...remaining for further processing  : 392
% 0.19/0.45  # Other redundant clauses eliminated   : 3
% 0.19/0.45  # Clauses deleted for lack of memory   : 0
% 0.19/0.45  # Backward-subsumed                    : 28
% 0.19/0.45  # Backward-rewritten                   : 169
% 0.19/0.45  # Generated clauses                    : 2036
% 0.19/0.45  # ...of the previous two non-trivial   : 2016
% 0.19/0.45  # Contextual simplify-reflections      : 7
% 0.19/0.45  # Paramodulations                      : 2015
% 0.19/0.45  # Factorizations                       : 18
% 0.19/0.45  # Equation resolutions                 : 3
% 0.19/0.45  # Propositional unsat checks           : 0
% 0.19/0.45  #    Propositional check models        : 0
% 0.19/0.45  #    Propositional check unsatisfiable : 0
% 0.19/0.45  #    Propositional clauses             : 0
% 0.19/0.45  #    Propositional clauses after purity: 0
% 0.19/0.45  #    Propositional unsat core size     : 0
% 0.19/0.45  #    Propositional preprocessing time  : 0.000
% 0.19/0.45  #    Propositional encoding time       : 0.000
% 0.19/0.45  #    Propositional solver time         : 0.000
% 0.19/0.45  #    Success case prop preproc time    : 0.000
% 0.19/0.45  #    Success case prop encoding time   : 0.000
% 0.19/0.45  #    Success case prop solver time     : 0.000
% 0.19/0.45  # Current number of processed clauses  : 154
% 0.19/0.45  #    Positive orientable unit clauses  : 17
% 0.19/0.45  #    Positive unorientable unit clauses: 0
% 0.19/0.45  #    Negative unit clauses             : 5
% 0.19/0.45  #    Non-unit-clauses                  : 132
% 0.19/0.45  # Current number of unprocessed clauses: 1249
% 0.19/0.45  # ...number of literals in the above   : 6901
% 0.19/0.45  # Current number of archived formulas  : 0
% 0.19/0.45  # Current number of archived clauses   : 235
% 0.19/0.45  # Clause-clause subsumption calls (NU) : 19152
% 0.19/0.45  # Rec. Clause-clause subsumption calls : 5849
% 0.19/0.45  # Non-unit clause-clause subsumptions  : 457
% 0.19/0.45  # Unit Clause-clause subsumption calls : 156
% 0.19/0.45  # Rewrite failures with RHS unbound    : 0
% 0.19/0.45  # BW rewrite match attempts            : 15
% 0.19/0.45  # BW rewrite match successes           : 4
% 0.19/0.45  # Condensation attempts                : 0
% 0.19/0.45  # Condensation successes               : 0
% 0.19/0.45  # Termbank termtop insertions          : 52325
% 0.19/0.45  
% 0.19/0.45  # -------------------------------------------------
% 0.19/0.45  # User time                : 0.108 s
% 0.19/0.45  # System time              : 0.008 s
% 0.19/0.45  # Total time               : 0.116 s
% 0.19/0.45  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
