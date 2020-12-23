%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : yellow19__t2_yellow19.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:51 EDT 2019

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   45 (  75 expanded)
%              Number of clauses        :   24 (  27 expanded)
%              Number of leaves         :   10 (  21 expanded)
%              Depth                    :    7
%              Number of atoms          :  197 ( 374 expanded)
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
    file('/export/starexec/sandbox2/benchmark/yellow19__t2_yellow19.p',t2_yellow19)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t2_yellow19.p',t6_boole)).

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
    file('/export/starexec/sandbox2/benchmark/yellow19__t2_yellow19.p',t8_waybel_7)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t2_yellow19.p',t7_boole)).

fof(fc7_yellow_1,axiom,(
    ! [X1] :
      ( ~ v2_struct_0(k3_yellow_1(X1))
      & v1_orders_2(k3_yellow_1(X1))
      & v3_orders_2(k3_yellow_1(X1))
      & v4_orders_2(k3_yellow_1(X1))
      & v5_orders_2(k3_yellow_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t2_yellow19.p',fc7_yellow_1)).

fof(dt_k3_yellow_1,axiom,(
    ! [X1] :
      ( v1_orders_2(k3_yellow_1(X1))
      & l1_orders_2(k3_yellow_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t2_yellow19.p',dt_k3_yellow_1)).

fof(t18_yellow_1,axiom,(
    ! [X1] : k3_yellow_0(k3_yellow_1(X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t2_yellow19.p',t18_yellow_1)).

fof(cc12_waybel_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v25_waybel_0(X1) )
       => ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v1_yellow_0(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t2_yellow19.p',cc12_waybel_0)).

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
    file('/export/starexec/sandbox2/benchmark/yellow19__t2_yellow19.p',cc11_waybel_0)).

fof(fc8_yellow_1,axiom,(
    ! [X1] :
      ( v1_orders_2(k3_yellow_1(X1))
      & v3_lattice3(k3_yellow_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t2_yellow19.p',fc8_yellow_1)).

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
    ! [X38] :
      ( ~ v1_xboole_0(X38)
      | X38 = k1_xboole_0 ) ),
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
    ! [X43,X44] :
      ( ( ~ v1_subset_1(X44,u1_struct_0(X43))
        | ~ r2_hidden(k3_yellow_0(X43),X44)
        | v1_xboole_0(X44)
        | ~ v2_waybel_0(X44,X43)
        | ~ v13_waybel_0(X44,X43)
        | ~ m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X43)))
        | v2_struct_0(X43)
        | ~ v3_orders_2(X43)
        | ~ v4_orders_2(X43)
        | ~ v5_orders_2(X43)
        | ~ v1_yellow_0(X43)
        | ~ l1_orders_2(X43) )
      & ( r2_hidden(k3_yellow_0(X43),X44)
        | v1_subset_1(X44,u1_struct_0(X43))
        | v1_xboole_0(X44)
        | ~ v2_waybel_0(X44,X43)
        | ~ v13_waybel_0(X44,X43)
        | ~ m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X43)))
        | v2_struct_0(X43)
        | ~ v3_orders_2(X43)
        | ~ v4_orders_2(X43)
        | ~ v5_orders_2(X43)
        | ~ v1_yellow_0(X43)
        | ~ l1_orders_2(X43) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t8_waybel_7])])])])])).

fof(c_0_14,plain,(
    ! [X39,X40] :
      ( ~ r2_hidden(X39,X40)
      | ~ v1_xboole_0(X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_15,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( v1_xboole_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_19,plain,(
    ! [X47] :
      ( ~ v2_struct_0(k3_yellow_1(X47))
      & v1_orders_2(k3_yellow_1(X47))
      & v3_orders_2(k3_yellow_1(X47))
      & v4_orders_2(k3_yellow_1(X47))
      & v5_orders_2(k3_yellow_1(X47)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc7_yellow_1])])).

fof(c_0_20,plain,(
    ! [X14] :
      ( v1_orders_2(k3_yellow_1(X14))
      & l1_orders_2(k3_yellow_1(X14)) ) ),
    inference(variable_rename,[status(thm)],[dt_k3_yellow_1])).

fof(c_0_21,plain,(
    ! [X25] : k3_yellow_0(k3_yellow_1(X25)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t18_yellow_1])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_23,negated_conjecture,
    ( esk3_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

fof(c_0_24,plain,(
    ! [X46] :
      ( ( ~ v2_struct_0(X46)
        | v2_struct_0(X46)
        | ~ v3_orders_2(X46)
        | ~ v25_waybel_0(X46)
        | ~ l1_orders_2(X46) )
      & ( v3_orders_2(X46)
        | v2_struct_0(X46)
        | ~ v3_orders_2(X46)
        | ~ v25_waybel_0(X46)
        | ~ l1_orders_2(X46) )
      & ( v1_yellow_0(X46)
        | v2_struct_0(X46)
        | ~ v3_orders_2(X46)
        | ~ v25_waybel_0(X46)
        | ~ l1_orders_2(X46) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc12_waybel_0])])])])).

fof(c_0_25,plain,(
    ! [X45] :
      ( ( ~ v2_struct_0(X45)
        | v2_struct_0(X45)
        | ~ v3_orders_2(X45)
        | ~ v3_lattice3(X45)
        | ~ l1_orders_2(X45) )
      & ( v3_orders_2(X45)
        | v2_struct_0(X45)
        | ~ v3_orders_2(X45)
        | ~ v3_lattice3(X45)
        | ~ l1_orders_2(X45) )
      & ( v24_waybel_0(X45)
        | v2_struct_0(X45)
        | ~ v3_orders_2(X45)
        | ~ v3_lattice3(X45)
        | ~ l1_orders_2(X45) )
      & ( v25_waybel_0(X45)
        | v2_struct_0(X45)
        | ~ v3_orders_2(X45)
        | ~ v3_lattice3(X45)
        | ~ l1_orders_2(X45) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc11_waybel_0])])])])).

cnf(c_0_26,plain,
    ( v2_struct_0(X1)
    | ~ v1_yellow_0(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ r2_hidden(k3_yellow_0(X1),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v13_waybel_0(X2,X1)
    | ~ v2_waybel_0(X2,X1)
    | ~ v1_subset_1(X2,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_27,negated_conjecture,
    ( v1_subset_1(esk2_0,u1_struct_0(k3_yellow_1(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_28,plain,
    ( v5_orders_2(k3_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,plain,
    ( v4_orders_2(k3_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,plain,
    ( v3_orders_2(k3_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_31,plain,
    ( l1_orders_2(k3_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_32,plain,
    ( k3_yellow_0(k3_yellow_1(X1)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(esk1_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_34,negated_conjecture,
    ( v13_waybel_0(esk2_0,k3_yellow_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_35,negated_conjecture,
    ( v2_waybel_0(esk2_0,k3_yellow_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_36,plain,
    ( ~ v2_struct_0(k3_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(k1_xboole_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_38,plain,
    ( v1_yellow_0(X1)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v25_waybel_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_39,plain,
    ( v25_waybel_0(X1)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v3_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_40,plain,(
    ! [X48] :
      ( v1_orders_2(k3_yellow_1(X48))
      & v3_lattice3(k3_yellow_1(X48)) ) ),
    inference(variable_rename,[status(thm)],[fc8_yellow_1])).

cnf(c_0_41,negated_conjecture,
    ( ~ v1_yellow_0(k3_yellow_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29]),c_0_30]),c_0_31]),c_0_32]),c_0_33]),c_0_34]),c_0_35])]),c_0_36]),c_0_37])])).

cnf(c_0_42,plain,
    ( v1_yellow_0(X1)
    | v2_struct_0(X1)
    | ~ v3_lattice3(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_43,plain,
    ( v3_lattice3(k3_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_44,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43]),c_0_30]),c_0_31])]),c_0_36]),
    [proof]).
%------------------------------------------------------------------------------
