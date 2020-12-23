%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:26 EST 2020

% Result     : Theorem 0.37s
% Output     : CNFRefutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 379 expanded)
%              Number of clauses        :   56 ( 144 expanded)
%              Number of leaves         :   16 (  93 expanded)
%              Depth                    :   12
%              Number of atoms          :  323 (2693 expanded)
%              Number of equality atoms :   29 (  80 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

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

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

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

fof(t49_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( ! [X3] :
            ( m1_subset_1(X3,X1)
           => r2_hidden(X3,X2) )
       => X1 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_subset_1)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

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

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(dt_k3_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => m1_subset_1(k3_yellow_0(X1),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow_0)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(c_0_16,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_17,negated_conjecture,(
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

fof(c_0_18,plain,(
    ! [X16,X17] :
      ( ( ~ m1_subset_1(X16,k1_zfmisc_1(X17))
        | r1_tarski(X16,X17) )
      & ( ~ r1_tarski(X16,X17)
        | m1_subset_1(X16,k1_zfmisc_1(X17)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_19,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_21,plain,(
    ! [X32,X33,X34,X35] :
      ( ( ~ v13_waybel_0(X33,X32)
        | ~ m1_subset_1(X34,u1_struct_0(X32))
        | ~ m1_subset_1(X35,u1_struct_0(X32))
        | ~ r2_hidden(X34,X33)
        | ~ r1_orders_2(X32,X34,X35)
        | r2_hidden(X35,X33)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))
        | ~ l1_orders_2(X32) )
      & ( m1_subset_1(esk3_2(X32,X33),u1_struct_0(X32))
        | v13_waybel_0(X33,X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))
        | ~ l1_orders_2(X32) )
      & ( m1_subset_1(esk4_2(X32,X33),u1_struct_0(X32))
        | v13_waybel_0(X33,X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))
        | ~ l1_orders_2(X32) )
      & ( r2_hidden(esk3_2(X32,X33),X33)
        | v13_waybel_0(X33,X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))
        | ~ l1_orders_2(X32) )
      & ( r1_orders_2(X32,esk3_2(X32,X33),esk4_2(X32,X33))
        | v13_waybel_0(X33,X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))
        | ~ l1_orders_2(X32) )
      & ( ~ r2_hidden(esk4_2(X32,X33),X33)
        | v13_waybel_0(X33,X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))
        | ~ l1_orders_2(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d20_waybel_0])])])])])).

fof(c_0_22,plain,(
    ! [X18,X19,X20] :
      ( ~ r2_hidden(X18,X19)
      | ~ m1_subset_1(X19,k1_zfmisc_1(X20))
      | m1_subset_1(X18,X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_23,plain,(
    ! [X40,X41] :
      ( ( ~ v1_subset_1(X41,X40)
        | X41 != X40
        | ~ m1_subset_1(X41,k1_zfmisc_1(X40)) )
      & ( X41 = X40
        | v1_subset_1(X41,X40)
        | ~ m1_subset_1(X41,k1_zfmisc_1(X40)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).

fof(c_0_24,negated_conjecture,
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
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_17])])])])).

fof(c_0_25,plain,(
    ! [X11,X12] :
      ( ( m1_subset_1(esk2_2(X11,X12),X11)
        | X11 = X12
        | ~ m1_subset_1(X12,k1_zfmisc_1(X11)) )
      & ( ~ r2_hidden(esk2_2(X11,X12),X12)
        | X11 = X12
        | ~ m1_subset_1(X12,k1_zfmisc_1(X11)) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t49_subset_1])])])])).

fof(c_0_26,plain,(
    ! [X21,X22,X23] :
      ( ~ r2_hidden(X21,X22)
      | ~ m1_subset_1(X22,k1_zfmisc_1(X23))
      | ~ v1_xboole_0(X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_27,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_29,plain,
    ( r2_hidden(X4,X1)
    | ~ v13_waybel_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r2_hidden(X3,X1)
    | ~ r1_orders_2(X2,X3,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_31,plain,(
    ! [X25,X26] :
      ( ~ l1_orders_2(X25)
      | m1_subset_1(k1_yellow_0(X25,X26),u1_struct_0(X25)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_yellow_0])])).

cnf(c_0_32,plain,
    ( X1 = X2
    | v1_subset_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_34,plain,(
    ! [X38,X39] :
      ( ( r1_yellow_0(X38,k5_waybel_0(X38,X39))
        | ~ m1_subset_1(X39,u1_struct_0(X38))
        | v2_struct_0(X38)
        | ~ v3_orders_2(X38)
        | ~ v4_orders_2(X38)
        | ~ v5_orders_2(X38)
        | ~ l1_orders_2(X38) )
      & ( k1_yellow_0(X38,k5_waybel_0(X38,X39)) = X39
        | ~ m1_subset_1(X39,u1_struct_0(X38))
        | v2_struct_0(X38)
        | ~ v3_orders_2(X38)
        | ~ v4_orders_2(X38)
        | ~ v5_orders_2(X38)
        | ~ l1_orders_2(X38) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_waybel_0])])])])])).

cnf(c_0_35,plain,
    ( m1_subset_1(esk2_2(X1,X2),X1)
    | X1 = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_36,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_37,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,X2)
    | ~ v13_waybel_0(X2,X3)
    | ~ r1_orders_2(X3,X4,X1)
    | ~ l1_orders_2(X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ r2_hidden(X4,X2) ),
    inference(csr,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_39,plain,
    ( m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(k3_yellow_0(esk5_0),esk6_0)
    | ~ v1_subset_1(esk6_0,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_41,negated_conjecture,
    ( u1_struct_0(esk5_0) = esk6_0
    | v1_subset_1(esk6_0,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

fof(c_0_42,plain,(
    ! [X24] :
      ( ~ l1_orders_2(X24)
      | k3_yellow_0(X24) = k1_yellow_0(X24,k1_xboole_0) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_yellow_0])])).

fof(c_0_43,plain,(
    ! [X28,X29,X30] :
      ( ~ l1_orders_2(X28)
      | ~ r1_tarski(X29,X30)
      | ~ r1_yellow_0(X28,X29)
      | ~ r1_yellow_0(X28,X30)
      | r1_orders_2(X28,k1_yellow_0(X28,X29),k1_yellow_0(X28,X30)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_yellow_0])])])).

cnf(c_0_44,plain,
    ( r1_yellow_0(X1,k5_waybel_0(X1,X2))
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_45,negated_conjecture,
    ( u1_struct_0(esk5_0) = esk6_0
    | m1_subset_1(esk2_2(u1_struct_0(esk5_0),esk6_0),u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_33])).

cnf(c_0_46,negated_conjecture,
    ( v4_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_47,negated_conjecture,
    ( v3_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_48,negated_conjecture,
    ( v5_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_49,negated_conjecture,
    ( l1_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_50,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_51,plain,(
    ! [X31] :
      ( ( r1_yellow_0(X31,k1_xboole_0)
        | v2_struct_0(X31)
        | ~ v5_orders_2(X31)
        | ~ v1_yellow_0(X31)
        | ~ l1_orders_2(X31) )
      & ( r2_yellow_0(X31,u1_struct_0(X31))
        | v2_struct_0(X31)
        | ~ v5_orders_2(X31)
        | ~ v1_yellow_0(X31)
        | ~ l1_orders_2(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t42_yellow_0])])])])).

cnf(c_0_52,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_53,plain,
    ( r2_hidden(k1_yellow_0(X1,X2),X3)
    | ~ v13_waybel_0(X3,X1)
    | ~ r1_orders_2(X1,X4,k1_yellow_0(X1,X2))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X4,X3) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_54,negated_conjecture,
    ( v13_waybel_0(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_55,negated_conjecture,
    ( u1_struct_0(esk5_0) = esk6_0
    | r2_hidden(k3_yellow_0(esk5_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_56,plain,
    ( k3_yellow_0(X1) = k1_yellow_0(X1,k1_xboole_0)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_57,plain,
    ( r1_orders_2(X1,k1_yellow_0(X1,X2),k1_yellow_0(X1,X3))
    | ~ l1_orders_2(X1)
    | ~ r1_tarski(X2,X3)
    | ~ r1_yellow_0(X1,X2)
    | ~ r1_yellow_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_58,negated_conjecture,
    ( u1_struct_0(esk5_0) = esk6_0
    | r1_yellow_0(esk5_0,k5_waybel_0(esk5_0,esk2_2(u1_struct_0(esk5_0),esk6_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46]),c_0_47]),c_0_48]),c_0_49])]),c_0_50])).

cnf(c_0_59,plain,
    ( r1_yellow_0(X1,k1_xboole_0)
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_yellow_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_60,negated_conjecture,
    ( v1_yellow_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_61,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_20])).

cnf(c_0_62,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(k1_yellow_0(esk5_0,X1),esk6_0)
    | ~ r1_orders_2(esk5_0,X2,k1_yellow_0(esk5_0,X1))
    | ~ r2_hidden(X2,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_33]),c_0_54]),c_0_49])])).

cnf(c_0_64,negated_conjecture,
    ( u1_struct_0(esk5_0) = esk6_0
    | r2_hidden(k1_yellow_0(esk5_0,k1_xboole_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_49])])).

cnf(c_0_65,negated_conjecture,
    ( u1_struct_0(esk5_0) = esk6_0
    | r1_orders_2(esk5_0,k1_yellow_0(esk5_0,X1),k1_yellow_0(esk5_0,k5_waybel_0(esk5_0,esk2_2(u1_struct_0(esk5_0),esk6_0))))
    | ~ r1_yellow_0(esk5_0,X1)
    | ~ r1_tarski(X1,k5_waybel_0(esk5_0,esk2_2(u1_struct_0(esk5_0),esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_49])])).

cnf(c_0_66,negated_conjecture,
    ( r1_yellow_0(esk5_0,k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_48]),c_0_49])]),c_0_50])).

cnf(c_0_67,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_68,negated_conjecture,
    ( u1_struct_0(esk5_0) = esk6_0
    | r2_hidden(k1_yellow_0(esk5_0,X1),esk6_0)
    | ~ r1_orders_2(esk5_0,k1_yellow_0(esk5_0,k1_xboole_0),k1_yellow_0(esk5_0,X1)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_69,negated_conjecture,
    ( u1_struct_0(esk5_0) = esk6_0
    | r1_orders_2(esk5_0,k1_yellow_0(esk5_0,k1_xboole_0),k1_yellow_0(esk5_0,k5_waybel_0(esk5_0,esk2_2(u1_struct_0(esk5_0),esk6_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67])])).

cnf(c_0_70,plain,
    ( k1_yellow_0(X1,k5_waybel_0(X1,X2)) = X2
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_71,plain,
    ( X1 = X2
    | ~ r2_hidden(esk2_2(X1,X2),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_72,plain,
    ( ~ v1_subset_1(X1,X2)
    | X1 != X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_73,plain,(
    ! [X27] :
      ( ~ l1_orders_2(X27)
      | m1_subset_1(k3_yellow_0(X27),u1_struct_0(X27)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_yellow_0])])).

cnf(c_0_74,negated_conjecture,
    ( u1_struct_0(esk5_0) = esk6_0
    | r2_hidden(k1_yellow_0(esk5_0,k5_waybel_0(esk5_0,esk2_2(u1_struct_0(esk5_0),esk6_0))),esk6_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_75,negated_conjecture,
    ( k1_yellow_0(esk5_0,k5_waybel_0(esk5_0,esk2_2(u1_struct_0(esk5_0),esk6_0))) = esk2_2(u1_struct_0(esk5_0),esk6_0)
    | u1_struct_0(esk5_0) = esk6_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_45]),c_0_46]),c_0_47]),c_0_48]),c_0_49])]),c_0_50])).

cnf(c_0_76,negated_conjecture,
    ( u1_struct_0(esk5_0) = esk6_0
    | ~ r2_hidden(esk2_2(u1_struct_0(esk5_0),esk6_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_71,c_0_33])).

cnf(c_0_77,plain,
    ( ~ v1_subset_1(X1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(er,[status(thm)],[c_0_72])).

fof(c_0_78,plain,(
    ! [X14,X15] :
      ( ~ m1_subset_1(X14,X15)
      | v1_xboole_0(X15)
      | r2_hidden(X14,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_79,plain,
    ( m1_subset_1(k3_yellow_0(X1),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_80,negated_conjecture,
    ( u1_struct_0(esk5_0) = esk6_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_76])).

cnf(c_0_81,negated_conjecture,
    ( v1_subset_1(esk6_0,u1_struct_0(esk5_0))
    | ~ r2_hidden(k3_yellow_0(esk5_0),esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_82,plain,
    ( ~ v1_subset_1(X1,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_77,c_0_37])])).

cnf(c_0_83,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_84,negated_conjecture,
    ( m1_subset_1(k3_yellow_0(esk5_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_49])])).

cnf(c_0_85,negated_conjecture,
    ( ~ v1_xboole_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_86,negated_conjecture,
    ( ~ r2_hidden(k3_yellow_0(esk5_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_80]),c_0_82])).

cnf(c_0_87,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_85]),c_0_86]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:36:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.37/0.56  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_SE_CS_SP_PI_PS_S2S
% 0.37/0.56  # and selection function SelectNewComplexAHP.
% 0.37/0.56  #
% 0.37/0.56  # Preprocessing time       : 0.028 s
% 0.37/0.56  # Presaturation interreduction done
% 0.37/0.56  
% 0.37/0.56  # Proof found!
% 0.37/0.56  # SZS status Theorem
% 0.37/0.56  # SZS output start CNFRefutation
% 0.37/0.56  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.37/0.56  fof(t8_waybel_7, conjecture, ![X1]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&v1_yellow_0(X1))&l1_orders_2(X1))=>![X2]:((((~(v1_xboole_0(X2))&v2_waybel_0(X2,X1))&v13_waybel_0(X2,X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v1_subset_1(X2,u1_struct_0(X1))<=>~(r2_hidden(k3_yellow_0(X1),X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_waybel_7)).
% 0.37/0.56  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.37/0.56  fof(d20_waybel_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v13_waybel_0(X2,X1)<=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((r2_hidden(X3,X2)&r1_orders_2(X1,X3,X4))=>r2_hidden(X4,X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d20_waybel_0)).
% 0.37/0.56  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.37/0.56  fof(d7_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(v1_subset_1(X2,X1)<=>X2!=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 0.37/0.56  fof(t49_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(![X3]:(m1_subset_1(X3,X1)=>r2_hidden(X3,X2))=>X1=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_subset_1)).
% 0.37/0.56  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 0.37/0.56  fof(dt_k1_yellow_0, axiom, ![X1, X2]:(l1_orders_2(X1)=>m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_yellow_0)).
% 0.37/0.56  fof(t34_waybel_0, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(r1_yellow_0(X1,k5_waybel_0(X1,X2))&k1_yellow_0(X1,k5_waybel_0(X1,X2))=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_waybel_0)).
% 0.37/0.56  fof(d11_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>k3_yellow_0(X1)=k1_yellow_0(X1,k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_yellow_0)).
% 0.37/0.56  fof(t34_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(((r1_tarski(X2,X3)&r1_yellow_0(X1,X2))&r1_yellow_0(X1,X3))=>r1_orders_2(X1,k1_yellow_0(X1,X2),k1_yellow_0(X1,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_yellow_0)).
% 0.37/0.56  fof(t42_yellow_0, axiom, ![X1]:((((~(v2_struct_0(X1))&v5_orders_2(X1))&v1_yellow_0(X1))&l1_orders_2(X1))=>(r1_yellow_0(X1,k1_xboole_0)&r2_yellow_0(X1,u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_yellow_0)).
% 0.37/0.56  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.37/0.56  fof(dt_k3_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>m1_subset_1(k3_yellow_0(X1),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_yellow_0)).
% 0.37/0.56  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 0.37/0.56  fof(c_0_16, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.37/0.56  fof(c_0_17, negated_conjecture, ~(![X1]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&v1_yellow_0(X1))&l1_orders_2(X1))=>![X2]:((((~(v1_xboole_0(X2))&v2_waybel_0(X2,X1))&v13_waybel_0(X2,X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v1_subset_1(X2,u1_struct_0(X1))<=>~(r2_hidden(k3_yellow_0(X1),X2)))))), inference(assume_negation,[status(cth)],[t8_waybel_7])).
% 0.37/0.56  fof(c_0_18, plain, ![X16, X17]:((~m1_subset_1(X16,k1_zfmisc_1(X17))|r1_tarski(X16,X17))&(~r1_tarski(X16,X17)|m1_subset_1(X16,k1_zfmisc_1(X17)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.37/0.56  cnf(c_0_19, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.37/0.56  cnf(c_0_20, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.37/0.56  fof(c_0_21, plain, ![X32, X33, X34, X35]:((~v13_waybel_0(X33,X32)|(~m1_subset_1(X34,u1_struct_0(X32))|(~m1_subset_1(X35,u1_struct_0(X32))|(~r2_hidden(X34,X33)|~r1_orders_2(X32,X34,X35)|r2_hidden(X35,X33))))|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))|~l1_orders_2(X32))&((m1_subset_1(esk3_2(X32,X33),u1_struct_0(X32))|v13_waybel_0(X33,X32)|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))|~l1_orders_2(X32))&((m1_subset_1(esk4_2(X32,X33),u1_struct_0(X32))|v13_waybel_0(X33,X32)|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))|~l1_orders_2(X32))&(((r2_hidden(esk3_2(X32,X33),X33)|v13_waybel_0(X33,X32)|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))|~l1_orders_2(X32))&(r1_orders_2(X32,esk3_2(X32,X33),esk4_2(X32,X33))|v13_waybel_0(X33,X32)|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))|~l1_orders_2(X32)))&(~r2_hidden(esk4_2(X32,X33),X33)|v13_waybel_0(X33,X32)|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))|~l1_orders_2(X32)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d20_waybel_0])])])])])).
% 0.37/0.56  fof(c_0_22, plain, ![X18, X19, X20]:(~r2_hidden(X18,X19)|~m1_subset_1(X19,k1_zfmisc_1(X20))|m1_subset_1(X18,X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.37/0.56  fof(c_0_23, plain, ![X40, X41]:((~v1_subset_1(X41,X40)|X41!=X40|~m1_subset_1(X41,k1_zfmisc_1(X40)))&(X41=X40|v1_subset_1(X41,X40)|~m1_subset_1(X41,k1_zfmisc_1(X40)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).
% 0.37/0.56  fof(c_0_24, negated_conjecture, ((((((~v2_struct_0(esk5_0)&v3_orders_2(esk5_0))&v4_orders_2(esk5_0))&v5_orders_2(esk5_0))&v1_yellow_0(esk5_0))&l1_orders_2(esk5_0))&((((~v1_xboole_0(esk6_0)&v2_waybel_0(esk6_0,esk5_0))&v13_waybel_0(esk6_0,esk5_0))&m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0))))&((~v1_subset_1(esk6_0,u1_struct_0(esk5_0))|r2_hidden(k3_yellow_0(esk5_0),esk6_0))&(v1_subset_1(esk6_0,u1_struct_0(esk5_0))|~r2_hidden(k3_yellow_0(esk5_0),esk6_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_17])])])])).
% 0.37/0.56  fof(c_0_25, plain, ![X11, X12]:((m1_subset_1(esk2_2(X11,X12),X11)|X11=X12|~m1_subset_1(X12,k1_zfmisc_1(X11)))&(~r2_hidden(esk2_2(X11,X12),X12)|X11=X12|~m1_subset_1(X12,k1_zfmisc_1(X11)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t49_subset_1])])])])).
% 0.37/0.56  fof(c_0_26, plain, ![X21, X22, X23]:(~r2_hidden(X21,X22)|~m1_subset_1(X22,k1_zfmisc_1(X23))|~v1_xboole_0(X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.37/0.56  cnf(c_0_27, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.37/0.56  cnf(c_0_28, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.37/0.56  cnf(c_0_29, plain, (r2_hidden(X4,X1)|~v13_waybel_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X2))|~m1_subset_1(X4,u1_struct_0(X2))|~r2_hidden(X3,X1)|~r1_orders_2(X2,X3,X4)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.37/0.56  cnf(c_0_30, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.37/0.56  fof(c_0_31, plain, ![X25, X26]:(~l1_orders_2(X25)|m1_subset_1(k1_yellow_0(X25,X26),u1_struct_0(X25))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_yellow_0])])).
% 0.37/0.56  cnf(c_0_32, plain, (X1=X2|v1_subset_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.37/0.56  cnf(c_0_33, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.37/0.56  fof(c_0_34, plain, ![X38, X39]:((r1_yellow_0(X38,k5_waybel_0(X38,X39))|~m1_subset_1(X39,u1_struct_0(X38))|(v2_struct_0(X38)|~v3_orders_2(X38)|~v4_orders_2(X38)|~v5_orders_2(X38)|~l1_orders_2(X38)))&(k1_yellow_0(X38,k5_waybel_0(X38,X39))=X39|~m1_subset_1(X39,u1_struct_0(X38))|(v2_struct_0(X38)|~v3_orders_2(X38)|~v4_orders_2(X38)|~v5_orders_2(X38)|~l1_orders_2(X38)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_waybel_0])])])])])).
% 0.37/0.56  cnf(c_0_35, plain, (m1_subset_1(esk2_2(X1,X2),X1)|X1=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.37/0.56  cnf(c_0_36, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.37/0.56  cnf(c_0_37, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.37/0.56  cnf(c_0_38, plain, (r2_hidden(X1,X2)|~v13_waybel_0(X2,X3)|~r1_orders_2(X3,X4,X1)|~l1_orders_2(X3)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~m1_subset_1(X1,u1_struct_0(X3))|~r2_hidden(X4,X2)), inference(csr,[status(thm)],[c_0_29, c_0_30])).
% 0.37/0.56  cnf(c_0_39, plain, (m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.37/0.56  cnf(c_0_40, negated_conjecture, (r2_hidden(k3_yellow_0(esk5_0),esk6_0)|~v1_subset_1(esk6_0,u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.37/0.56  cnf(c_0_41, negated_conjecture, (u1_struct_0(esk5_0)=esk6_0|v1_subset_1(esk6_0,u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.37/0.56  fof(c_0_42, plain, ![X24]:(~l1_orders_2(X24)|k3_yellow_0(X24)=k1_yellow_0(X24,k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_yellow_0])])).
% 0.37/0.56  fof(c_0_43, plain, ![X28, X29, X30]:(~l1_orders_2(X28)|(~r1_tarski(X29,X30)|~r1_yellow_0(X28,X29)|~r1_yellow_0(X28,X30)|r1_orders_2(X28,k1_yellow_0(X28,X29),k1_yellow_0(X28,X30)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_yellow_0])])])).
% 0.37/0.56  cnf(c_0_44, plain, (r1_yellow_0(X1,k5_waybel_0(X1,X2))|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.37/0.56  cnf(c_0_45, negated_conjecture, (u1_struct_0(esk5_0)=esk6_0|m1_subset_1(esk2_2(u1_struct_0(esk5_0),esk6_0),u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_35, c_0_33])).
% 0.37/0.56  cnf(c_0_46, negated_conjecture, (v4_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.37/0.56  cnf(c_0_47, negated_conjecture, (v3_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.37/0.56  cnf(c_0_48, negated_conjecture, (v5_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.37/0.56  cnf(c_0_49, negated_conjecture, (l1_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.37/0.56  cnf(c_0_50, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.37/0.56  fof(c_0_51, plain, ![X31]:((r1_yellow_0(X31,k1_xboole_0)|(v2_struct_0(X31)|~v5_orders_2(X31)|~v1_yellow_0(X31)|~l1_orders_2(X31)))&(r2_yellow_0(X31,u1_struct_0(X31))|(v2_struct_0(X31)|~v5_orders_2(X31)|~v1_yellow_0(X31)|~l1_orders_2(X31)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t42_yellow_0])])])])).
% 0.37/0.56  cnf(c_0_52, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.37/0.56  cnf(c_0_53, plain, (r2_hidden(k1_yellow_0(X1,X2),X3)|~v13_waybel_0(X3,X1)|~r1_orders_2(X1,X4,k1_yellow_0(X1,X2))|~l1_orders_2(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(X4,X3)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.37/0.56  cnf(c_0_54, negated_conjecture, (v13_waybel_0(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.37/0.56  cnf(c_0_55, negated_conjecture, (u1_struct_0(esk5_0)=esk6_0|r2_hidden(k3_yellow_0(esk5_0),esk6_0)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.37/0.56  cnf(c_0_56, plain, (k3_yellow_0(X1)=k1_yellow_0(X1,k1_xboole_0)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.37/0.56  cnf(c_0_57, plain, (r1_orders_2(X1,k1_yellow_0(X1,X2),k1_yellow_0(X1,X3))|~l1_orders_2(X1)|~r1_tarski(X2,X3)|~r1_yellow_0(X1,X2)|~r1_yellow_0(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.37/0.56  cnf(c_0_58, negated_conjecture, (u1_struct_0(esk5_0)=esk6_0|r1_yellow_0(esk5_0,k5_waybel_0(esk5_0,esk2_2(u1_struct_0(esk5_0),esk6_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46]), c_0_47]), c_0_48]), c_0_49])]), c_0_50])).
% 0.37/0.56  cnf(c_0_59, plain, (r1_yellow_0(X1,k1_xboole_0)|v2_struct_0(X1)|~v5_orders_2(X1)|~v1_yellow_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.37/0.56  cnf(c_0_60, negated_conjecture, (v1_yellow_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.37/0.56  cnf(c_0_61, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_52, c_0_20])).
% 0.37/0.56  cnf(c_0_62, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.37/0.56  cnf(c_0_63, negated_conjecture, (r2_hidden(k1_yellow_0(esk5_0,X1),esk6_0)|~r1_orders_2(esk5_0,X2,k1_yellow_0(esk5_0,X1))|~r2_hidden(X2,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_33]), c_0_54]), c_0_49])])).
% 0.37/0.56  cnf(c_0_64, negated_conjecture, (u1_struct_0(esk5_0)=esk6_0|r2_hidden(k1_yellow_0(esk5_0,k1_xboole_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_49])])).
% 0.37/0.56  cnf(c_0_65, negated_conjecture, (u1_struct_0(esk5_0)=esk6_0|r1_orders_2(esk5_0,k1_yellow_0(esk5_0,X1),k1_yellow_0(esk5_0,k5_waybel_0(esk5_0,esk2_2(u1_struct_0(esk5_0),esk6_0))))|~r1_yellow_0(esk5_0,X1)|~r1_tarski(X1,k5_waybel_0(esk5_0,esk2_2(u1_struct_0(esk5_0),esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_49])])).
% 0.37/0.56  cnf(c_0_66, negated_conjecture, (r1_yellow_0(esk5_0,k1_xboole_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_48]), c_0_49])]), c_0_50])).
% 0.37/0.56  cnf(c_0_67, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.37/0.56  cnf(c_0_68, negated_conjecture, (u1_struct_0(esk5_0)=esk6_0|r2_hidden(k1_yellow_0(esk5_0,X1),esk6_0)|~r1_orders_2(esk5_0,k1_yellow_0(esk5_0,k1_xboole_0),k1_yellow_0(esk5_0,X1))), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.37/0.56  cnf(c_0_69, negated_conjecture, (u1_struct_0(esk5_0)=esk6_0|r1_orders_2(esk5_0,k1_yellow_0(esk5_0,k1_xboole_0),k1_yellow_0(esk5_0,k5_waybel_0(esk5_0,esk2_2(u1_struct_0(esk5_0),esk6_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_67])])).
% 0.37/0.56  cnf(c_0_70, plain, (k1_yellow_0(X1,k5_waybel_0(X1,X2))=X2|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.37/0.56  cnf(c_0_71, plain, (X1=X2|~r2_hidden(esk2_2(X1,X2),X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.37/0.56  cnf(c_0_72, plain, (~v1_subset_1(X1,X2)|X1!=X2|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.37/0.56  fof(c_0_73, plain, ![X27]:(~l1_orders_2(X27)|m1_subset_1(k3_yellow_0(X27),u1_struct_0(X27))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_yellow_0])])).
% 0.37/0.56  cnf(c_0_74, negated_conjecture, (u1_struct_0(esk5_0)=esk6_0|r2_hidden(k1_yellow_0(esk5_0,k5_waybel_0(esk5_0,esk2_2(u1_struct_0(esk5_0),esk6_0))),esk6_0)), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.37/0.56  cnf(c_0_75, negated_conjecture, (k1_yellow_0(esk5_0,k5_waybel_0(esk5_0,esk2_2(u1_struct_0(esk5_0),esk6_0)))=esk2_2(u1_struct_0(esk5_0),esk6_0)|u1_struct_0(esk5_0)=esk6_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_45]), c_0_46]), c_0_47]), c_0_48]), c_0_49])]), c_0_50])).
% 0.37/0.56  cnf(c_0_76, negated_conjecture, (u1_struct_0(esk5_0)=esk6_0|~r2_hidden(esk2_2(u1_struct_0(esk5_0),esk6_0),esk6_0)), inference(spm,[status(thm)],[c_0_71, c_0_33])).
% 0.37/0.56  cnf(c_0_77, plain, (~v1_subset_1(X1,X1)|~m1_subset_1(X1,k1_zfmisc_1(X1))), inference(er,[status(thm)],[c_0_72])).
% 0.37/0.56  fof(c_0_78, plain, ![X14, X15]:(~m1_subset_1(X14,X15)|(v1_xboole_0(X15)|r2_hidden(X14,X15))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.37/0.56  cnf(c_0_79, plain, (m1_subset_1(k3_yellow_0(X1),u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.37/0.56  cnf(c_0_80, negated_conjecture, (u1_struct_0(esk5_0)=esk6_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_76])).
% 0.37/0.56  cnf(c_0_81, negated_conjecture, (v1_subset_1(esk6_0,u1_struct_0(esk5_0))|~r2_hidden(k3_yellow_0(esk5_0),esk6_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.37/0.56  cnf(c_0_82, plain, (~v1_subset_1(X1,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_77, c_0_37])])).
% 0.37/0.56  cnf(c_0_83, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_78])).
% 0.37/0.56  cnf(c_0_84, negated_conjecture, (m1_subset_1(k3_yellow_0(esk5_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_49])])).
% 0.37/0.56  cnf(c_0_85, negated_conjecture, (~v1_xboole_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.37/0.56  cnf(c_0_86, negated_conjecture, (~r2_hidden(k3_yellow_0(esk5_0),esk6_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_81, c_0_80]), c_0_82])).
% 0.37/0.56  cnf(c_0_87, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_85]), c_0_86]), ['proof']).
% 0.37/0.56  # SZS output end CNFRefutation
% 0.37/0.56  # Proof object total steps             : 88
% 0.37/0.56  # Proof object clause steps            : 56
% 0.37/0.56  # Proof object formula steps           : 32
% 0.37/0.56  # Proof object conjectures             : 31
% 0.37/0.56  # Proof object clause conjectures      : 28
% 0.37/0.56  # Proof object formula conjectures     : 3
% 0.37/0.56  # Proof object initial clauses used    : 30
% 0.37/0.56  # Proof object initial formulas used   : 16
% 0.37/0.56  # Proof object generating inferences   : 22
% 0.37/0.56  # Proof object simplifying inferences  : 36
% 0.37/0.56  # Training examples: 0 positive, 0 negative
% 0.37/0.56  # Parsed axioms                        : 16
% 0.37/0.56  # Removed by relevancy pruning/SinE    : 0
% 0.37/0.56  # Initial clauses                      : 39
% 0.37/0.56  # Removed in clause preprocessing      : 0
% 0.37/0.56  # Initial clauses in saturation        : 39
% 0.37/0.56  # Processed clauses                    : 1442
% 0.37/0.56  # ...of these trivial                  : 0
% 0.37/0.56  # ...subsumed                          : 860
% 0.37/0.56  # ...remaining for further processing  : 582
% 0.37/0.56  # Other redundant clauses eliminated   : 1
% 0.37/0.56  # Clauses deleted for lack of memory   : 0
% 0.37/0.56  # Backward-subsumed                    : 45
% 0.37/0.56  # Backward-rewritten                   : 197
% 0.37/0.56  # Generated clauses                    : 7382
% 0.37/0.56  # ...of the previous two non-trivial   : 7242
% 0.37/0.56  # Contextual simplify-reflections      : 27
% 0.37/0.56  # Paramodulations                      : 7367
% 0.37/0.56  # Factorizations                       : 14
% 0.37/0.56  # Equation resolutions                 : 1
% 0.37/0.56  # Propositional unsat checks           : 0
% 0.37/0.56  #    Propositional check models        : 0
% 0.37/0.56  #    Propositional check unsatisfiable : 0
% 0.37/0.56  #    Propositional clauses             : 0
% 0.37/0.56  #    Propositional clauses after purity: 0
% 0.37/0.56  #    Propositional unsat core size     : 0
% 0.37/0.56  #    Propositional preprocessing time  : 0.000
% 0.37/0.56  #    Propositional encoding time       : 0.000
% 0.37/0.56  #    Propositional solver time         : 0.000
% 0.37/0.56  #    Success case prop preproc time    : 0.000
% 0.37/0.56  #    Success case prop encoding time   : 0.000
% 0.37/0.56  #    Success case prop solver time     : 0.000
% 0.37/0.56  # Current number of processed clauses  : 300
% 0.37/0.56  #    Positive orientable unit clauses  : 16
% 0.37/0.56  #    Positive unorientable unit clauses: 0
% 0.37/0.56  #    Negative unit clauses             : 5
% 0.37/0.56  #    Non-unit-clauses                  : 279
% 0.37/0.56  # Current number of unprocessed clauses: 5561
% 0.37/0.56  # ...number of literals in the above   : 35268
% 0.37/0.56  # Current number of archived formulas  : 0
% 0.37/0.56  # Current number of archived clauses   : 281
% 0.37/0.56  # Clause-clause subsumption calls (NU) : 43218
% 0.37/0.56  # Rec. Clause-clause subsumption calls : 12171
% 0.37/0.56  # Non-unit clause-clause subsumptions  : 918
% 0.37/0.56  # Unit Clause-clause subsumption calls : 116
% 0.37/0.56  # Rewrite failures with RHS unbound    : 0
% 0.37/0.56  # BW rewrite match attempts            : 14
% 0.37/0.56  # BW rewrite match successes           : 3
% 0.37/0.56  # Condensation attempts                : 0
% 0.37/0.56  # Condensation successes               : 0
% 0.37/0.56  # Termbank termtop insertions          : 155255
% 0.37/0.56  
% 0.37/0.56  # -------------------------------------------------
% 0.37/0.56  # User time                : 0.212 s
% 0.37/0.56  # System time              : 0.008 s
% 0.37/0.56  # Total time               : 0.221 s
% 0.37/0.56  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
