%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT2043+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:09 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   45 (  84 expanded)
%              Number of clauses        :   24 (  30 expanded)
%              Number of leaves         :   10 (  24 expanded)
%              Depth                    :    6
%              Number of atoms          :  193 ( 397 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   24 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t2_yellow19,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
            & v2_waybel_0(X2,k3_yellow_1(X1))
            & v13_waybel_0(X2,k3_yellow_1(X1))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) )
         => ! [X3] :
              ~ ( r2_hidden(X3,X2)
                & v1_xboole_0(X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_yellow19)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

fof(cc11_waybel_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v3_lattice3(X1) )
       => ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v24_waybel_0(X1)
          & v25_waybel_0(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc11_waybel_0)).

fof(fc8_yellow_1,axiom,(
    ! [X1] :
      ( v1_orders_2(k3_yellow_1(X1))
      & v3_lattice3(k3_yellow_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_yellow_1)).

fof(fc7_yellow_1,axiom,(
    ! [X1] :
      ( ~ v2_struct_0(k3_yellow_1(X1))
      & v1_orders_2(k3_yellow_1(X1))
      & v3_orders_2(k3_yellow_1(X1))
      & v4_orders_2(k3_yellow_1(X1))
      & v5_orders_2(k3_yellow_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_yellow_1)).

fof(dt_k3_yellow_1,axiom,(
    ! [X1] :
      ( v1_orders_2(k3_yellow_1(X1))
      & l1_orders_2(k3_yellow_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow_1)).

fof(t8_waybel_7,axiom,(
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

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

fof(cc12_waybel_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v25_waybel_0(X1) )
       => ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v1_yellow_0(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc12_waybel_0)).

fof(t18_yellow_1,axiom,(
    ! [X1] : k3_yellow_0(k3_yellow_1(X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_yellow_1)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ( ~ v1_xboole_0(X2)
              & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
              & v2_waybel_0(X2,k3_yellow_1(X1))
              & v13_waybel_0(X2,k3_yellow_1(X1))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) )
           => ! [X3] :
                ~ ( r2_hidden(X3,X2)
                  & v1_xboole_0(X3) ) ) ) ),
    inference(assume_negation,[status(cth)],[t2_yellow19])).

fof(c_0_11,plain,(
    ! [X10] :
      ( ~ v1_xboole_0(X10)
      | X10 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

fof(c_0_12,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0)
    & ~ v1_xboole_0(esk2_0)
    & v1_subset_1(esk2_0,u1_struct_0(k3_yellow_1(esk1_0)))
    & v2_waybel_0(esk2_0,k3_yellow_1(esk1_0))
    & v13_waybel_0(esk2_0,k3_yellow_1(esk1_0))
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(esk1_0))))
    & r2_hidden(esk3_0,esk2_0)
    & v1_xboole_0(esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).

fof(c_0_13,plain,(
    ! [X4] :
      ( ( ~ v2_struct_0(X4)
        | v2_struct_0(X4)
        | ~ v3_orders_2(X4)
        | ~ v3_lattice3(X4)
        | ~ l1_orders_2(X4) )
      & ( v3_orders_2(X4)
        | v2_struct_0(X4)
        | ~ v3_orders_2(X4)
        | ~ v3_lattice3(X4)
        | ~ l1_orders_2(X4) )
      & ( v24_waybel_0(X4)
        | v2_struct_0(X4)
        | ~ v3_orders_2(X4)
        | ~ v3_lattice3(X4)
        | ~ l1_orders_2(X4) )
      & ( v25_waybel_0(X4)
        | v2_struct_0(X4)
        | ~ v3_orders_2(X4)
        | ~ v3_lattice3(X4)
        | ~ l1_orders_2(X4) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc11_waybel_0])])])])).

fof(c_0_14,plain,(
    ! [X8] :
      ( v1_orders_2(k3_yellow_1(X8))
      & v3_lattice3(k3_yellow_1(X8)) ) ),
    inference(variable_rename,[status(thm)],[fc8_yellow_1])).

fof(c_0_15,plain,(
    ! [X7] :
      ( ~ v2_struct_0(k3_yellow_1(X7))
      & v1_orders_2(k3_yellow_1(X7))
      & v3_orders_2(k3_yellow_1(X7))
      & v4_orders_2(k3_yellow_1(X7))
      & v5_orders_2(k3_yellow_1(X7)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc7_yellow_1])])).

fof(c_0_16,plain,(
    ! [X6] :
      ( v1_orders_2(k3_yellow_1(X6))
      & l1_orders_2(k3_yellow_1(X6)) ) ),
    inference(variable_rename,[status(thm)],[dt_k3_yellow_1])).

fof(c_0_17,plain,(
    ! [X13,X14] :
      ( ( ~ v1_subset_1(X14,u1_struct_0(X13))
        | ~ r2_hidden(k3_yellow_0(X13),X14)
        | v1_xboole_0(X14)
        | ~ v2_waybel_0(X14,X13)
        | ~ v13_waybel_0(X14,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ v5_orders_2(X13)
        | ~ v1_yellow_0(X13)
        | ~ l1_orders_2(X13) )
      & ( r2_hidden(k3_yellow_0(X13),X14)
        | v1_subset_1(X14,u1_struct_0(X13))
        | v1_xboole_0(X14)
        | ~ v2_waybel_0(X14,X13)
        | ~ v13_waybel_0(X14,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ v5_orders_2(X13)
        | ~ v1_yellow_0(X13)
        | ~ l1_orders_2(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t8_waybel_7])])])])])).

fof(c_0_18,plain,(
    ! [X11,X12] :
      ( ~ r2_hidden(X11,X12)
      | ~ v1_xboole_0(X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_19,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,negated_conjecture,
    ( v1_xboole_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_21,plain,(
    ! [X5] :
      ( ( ~ v2_struct_0(X5)
        | v2_struct_0(X5)
        | ~ v3_orders_2(X5)
        | ~ v25_waybel_0(X5)
        | ~ l1_orders_2(X5) )
      & ( v3_orders_2(X5)
        | v2_struct_0(X5)
        | ~ v3_orders_2(X5)
        | ~ v25_waybel_0(X5)
        | ~ l1_orders_2(X5) )
      & ( v1_yellow_0(X5)
        | v2_struct_0(X5)
        | ~ v3_orders_2(X5)
        | ~ v25_waybel_0(X5)
        | ~ l1_orders_2(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc12_waybel_0])])])])).

cnf(c_0_22,plain,
    ( v25_waybel_0(X1)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v3_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_23,plain,
    ( v3_lattice3(k3_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,plain,
    ( v3_orders_2(k3_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,plain,
    ( l1_orders_2(k3_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,plain,
    ( ~ v2_struct_0(k3_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_27,plain,
    ( v1_xboole_0(X1)
    | v2_struct_0(X2)
    | ~ v1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_hidden(k3_yellow_0(X2),X1)
    | ~ v2_waybel_0(X1,X2)
    | ~ v13_waybel_0(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ v1_yellow_0(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_29,plain,(
    ! [X9] : k3_yellow_0(k3_yellow_1(X9)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t18_yellow_1])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_31,negated_conjecture,
    ( esk3_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_32,plain,
    ( v1_yellow_0(X1)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v25_waybel_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_33,plain,
    ( v25_waybel_0(k3_yellow_1(X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_34,plain,
    ( v2_struct_0(X1)
    | ~ v1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v13_waybel_0(X2,X1)
    | ~ v2_waybel_0(X2,X1)
    | ~ r2_hidden(k3_yellow_0(X1),X2)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v1_yellow_0(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(esk1_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_36,negated_conjecture,
    ( v1_subset_1(esk2_0,u1_struct_0(k3_yellow_1(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_37,negated_conjecture,
    ( v13_waybel_0(esk2_0,k3_yellow_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_38,negated_conjecture,
    ( v2_waybel_0(esk2_0,k3_yellow_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_39,plain,
    ( k3_yellow_0(k3_yellow_1(X1)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(k1_xboole_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_41,plain,
    ( v5_orders_2(k3_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_42,plain,
    ( v4_orders_2(k3_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_43,plain,
    ( v1_yellow_0(k3_yellow_1(X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_44,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36]),c_0_37]),c_0_38]),c_0_39]),c_0_40]),c_0_41]),c_0_42]),c_0_43]),c_0_24]),c_0_25])]),c_0_26]),
    [proof]).

%------------------------------------------------------------------------------
