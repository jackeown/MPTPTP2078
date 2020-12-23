%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:28 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 284 expanded)
%              Number of clauses        :   43 ( 108 expanded)
%              Number of leaves         :   12 (  69 expanded)
%              Depth                    :   10
%              Number of atoms          :  316 (2107 expanded)
%              Number of equality atoms :   32 (  96 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   50 (   3 average)
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

fof(t49_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( ! [X3] :
            ( m1_subset_1(X3,X1)
           => r2_hidden(X3,X2) )
       => X1 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_subset_1)).

fof(d7_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( v1_subset_1(X2,X1)
      <=> X2 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

fof(t30_yellow_0,axiom,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( ( ( X2 = k1_yellow_0(X1,X3)
                  & r1_yellow_0(X1,X3) )
               => ( r2_lattice3(X1,X3,X2)
                  & ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( r2_lattice3(X1,X3,X4)
                       => r1_orders_2(X1,X2,X4) ) ) ) )
              & ( ( r2_lattice3(X1,X3,X2)
                  & ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( r2_lattice3(X1,X3,X4)
                       => r1_orders_2(X1,X2,X4) ) ) )
               => ( X2 = k1_yellow_0(X1,X3)
                  & r1_yellow_0(X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_yellow_0)).

fof(dt_k1_yellow_0,axiom,(
    ! [X1,X2] :
      ( l1_orders_2(X1)
     => m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_yellow_0)).

fof(d11_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => k3_yellow_0(X1) = k1_yellow_0(X1,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_yellow_0)).

fof(t42_yellow_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v5_orders_2(X1)
        & v1_yellow_0(X1)
        & l1_orders_2(X1) )
     => ( r1_yellow_0(X1,k1_xboole_0)
        & r2_yellow_0(X1,u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_yellow_0)).

fof(t6_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( r2_lattice3(X1,k1_xboole_0,X2)
            & r1_lattice3(X1,k1_xboole_0,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_yellow_0)).

fof(rc3_subset_1,axiom,(
    ! [X1] :
    ? [X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
      & ~ v1_subset_1(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_subset_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

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
    ! [X27,X28,X29,X30] :
      ( ( ~ v13_waybel_0(X28,X27)
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | ~ m1_subset_1(X30,u1_struct_0(X27))
        | ~ r2_hidden(X29,X28)
        | ~ r1_orders_2(X27,X29,X30)
        | r2_hidden(X30,X28)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))
        | ~ l1_orders_2(X27) )
      & ( m1_subset_1(esk4_2(X27,X28),u1_struct_0(X27))
        | v13_waybel_0(X28,X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))
        | ~ l1_orders_2(X27) )
      & ( m1_subset_1(esk5_2(X27,X28),u1_struct_0(X27))
        | v13_waybel_0(X28,X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))
        | ~ l1_orders_2(X27) )
      & ( r2_hidden(esk4_2(X27,X28),X28)
        | v13_waybel_0(X28,X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))
        | ~ l1_orders_2(X27) )
      & ( r1_orders_2(X27,esk4_2(X27,X28),esk5_2(X27,X28))
        | v13_waybel_0(X28,X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))
        | ~ l1_orders_2(X27) )
      & ( ~ r2_hidden(esk5_2(X27,X28),X28)
        | v13_waybel_0(X28,X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))
        | ~ l1_orders_2(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d20_waybel_0])])])])])).

fof(c_0_14,plain,(
    ! [X12,X13,X14] :
      ( ~ r2_hidden(X12,X13)
      | ~ m1_subset_1(X13,k1_zfmisc_1(X14))
      | m1_subset_1(X12,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_15,plain,(
    ! [X5,X6] :
      ( ( m1_subset_1(esk1_2(X5,X6),X5)
        | X5 = X6
        | ~ m1_subset_1(X6,k1_zfmisc_1(X5)) )
      & ( ~ r2_hidden(esk1_2(X5,X6),X6)
        | X5 = X6
        | ~ m1_subset_1(X6,k1_zfmisc_1(X5)) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t49_subset_1])])])])).

fof(c_0_16,negated_conjecture,
    ( ~ v2_struct_0(esk6_0)
    & v3_orders_2(esk6_0)
    & v4_orders_2(esk6_0)
    & v5_orders_2(esk6_0)
    & v1_yellow_0(esk6_0)
    & l1_orders_2(esk6_0)
    & ~ v1_xboole_0(esk7_0)
    & v2_waybel_0(esk7_0,esk6_0)
    & v13_waybel_0(esk7_0,esk6_0)
    & m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk6_0)))
    & ( ~ v1_subset_1(esk7_0,u1_struct_0(esk6_0))
      | r2_hidden(k3_yellow_0(esk6_0),esk7_0) )
    & ( v1_subset_1(esk7_0,u1_struct_0(esk6_0))
      | ~ r2_hidden(k3_yellow_0(esk6_0),esk7_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])).

fof(c_0_17,plain,(
    ! [X33,X34] :
      ( ( ~ v1_subset_1(X34,X33)
        | X34 != X33
        | ~ m1_subset_1(X34,k1_zfmisc_1(X33)) )
      & ( X34 = X33
        | v1_subset_1(X34,X33)
        | ~ m1_subset_1(X34,k1_zfmisc_1(X33)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).

cnf(c_0_18,plain,
    ( r2_hidden(X4,X1)
    | ~ v13_waybel_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r2_hidden(X3,X1)
    | ~ r1_orders_2(X2,X3,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( m1_subset_1(esk1_2(X1,X2),X1)
    | X1 = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( X1 = X2
    | v1_subset_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_23,plain,(
    ! [X18,X19,X20,X21,X22] :
      ( ( r2_lattice3(X18,X20,X19)
        | X19 != k1_yellow_0(X18,X20)
        | ~ r1_yellow_0(X18,X20)
        | ~ m1_subset_1(X19,u1_struct_0(X18))
        | ~ v5_orders_2(X18)
        | ~ l1_orders_2(X18) )
      & ( ~ m1_subset_1(X21,u1_struct_0(X18))
        | ~ r2_lattice3(X18,X20,X21)
        | r1_orders_2(X18,X19,X21)
        | X19 != k1_yellow_0(X18,X20)
        | ~ r1_yellow_0(X18,X20)
        | ~ m1_subset_1(X19,u1_struct_0(X18))
        | ~ v5_orders_2(X18)
        | ~ l1_orders_2(X18) )
      & ( X19 = k1_yellow_0(X18,X22)
        | m1_subset_1(esk3_3(X18,X19,X22),u1_struct_0(X18))
        | ~ r2_lattice3(X18,X22,X19)
        | ~ m1_subset_1(X19,u1_struct_0(X18))
        | ~ v5_orders_2(X18)
        | ~ l1_orders_2(X18) )
      & ( r1_yellow_0(X18,X22)
        | m1_subset_1(esk3_3(X18,X19,X22),u1_struct_0(X18))
        | ~ r2_lattice3(X18,X22,X19)
        | ~ m1_subset_1(X19,u1_struct_0(X18))
        | ~ v5_orders_2(X18)
        | ~ l1_orders_2(X18) )
      & ( X19 = k1_yellow_0(X18,X22)
        | r2_lattice3(X18,X22,esk3_3(X18,X19,X22))
        | ~ r2_lattice3(X18,X22,X19)
        | ~ m1_subset_1(X19,u1_struct_0(X18))
        | ~ v5_orders_2(X18)
        | ~ l1_orders_2(X18) )
      & ( r1_yellow_0(X18,X22)
        | r2_lattice3(X18,X22,esk3_3(X18,X19,X22))
        | ~ r2_lattice3(X18,X22,X19)
        | ~ m1_subset_1(X19,u1_struct_0(X18))
        | ~ v5_orders_2(X18)
        | ~ l1_orders_2(X18) )
      & ( X19 = k1_yellow_0(X18,X22)
        | ~ r1_orders_2(X18,X19,esk3_3(X18,X19,X22))
        | ~ r2_lattice3(X18,X22,X19)
        | ~ m1_subset_1(X19,u1_struct_0(X18))
        | ~ v5_orders_2(X18)
        | ~ l1_orders_2(X18) )
      & ( r1_yellow_0(X18,X22)
        | ~ r1_orders_2(X18,X19,esk3_3(X18,X19,X22))
        | ~ r2_lattice3(X18,X22,X19)
        | ~ m1_subset_1(X19,u1_struct_0(X18))
        | ~ v5_orders_2(X18)
        | ~ l1_orders_2(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_yellow_0])])])])])])).

fof(c_0_24,plain,(
    ! [X16,X17] :
      ( ~ l1_orders_2(X16)
      | m1_subset_1(k1_yellow_0(X16,X17),u1_struct_0(X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_yellow_0])])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,X2)
    | ~ v13_waybel_0(X2,X3)
    | ~ r1_orders_2(X3,X4,X1)
    | ~ l1_orders_2(X3)
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X1,u1_struct_0(X3)) ),
    inference(csr,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( u1_struct_0(esk6_0) = esk7_0
    | m1_subset_1(esk1_2(u1_struct_0(esk6_0),esk7_0),u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( l1_orders_2(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_28,plain,
    ( X1 = X2
    | ~ r2_hidden(esk1_2(X1,X2),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(k3_yellow_0(esk6_0),esk7_0)
    | ~ v1_subset_1(esk7_0,u1_struct_0(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_30,negated_conjecture,
    ( u1_struct_0(esk6_0) = esk7_0
    | v1_subset_1(esk7_0,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_21])).

fof(c_0_31,plain,(
    ! [X15] :
      ( ~ l1_orders_2(X15)
      | k3_yellow_0(X15) = k1_yellow_0(X15,k1_xboole_0) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_yellow_0])])).

cnf(c_0_32,plain,
    ( r1_orders_2(X2,X4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X1)
    | X4 != k1_yellow_0(X2,X3)
    | ~ r1_yellow_0(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,plain,
    ( m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_34,plain,(
    ! [X24] :
      ( ( r1_yellow_0(X24,k1_xboole_0)
        | v2_struct_0(X24)
        | ~ v5_orders_2(X24)
        | ~ v1_yellow_0(X24)
        | ~ l1_orders_2(X24) )
      & ( r2_yellow_0(X24,u1_struct_0(X24))
        | v2_struct_0(X24)
        | ~ v5_orders_2(X24)
        | ~ v1_yellow_0(X24)
        | ~ l1_orders_2(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t42_yellow_0])])])])).

fof(c_0_35,plain,(
    ! [X25,X26] :
      ( ( r2_lattice3(X25,k1_xboole_0,X26)
        | ~ m1_subset_1(X26,u1_struct_0(X25))
        | ~ l1_orders_2(X25) )
      & ( r1_lattice3(X25,k1_xboole_0,X26)
        | ~ m1_subset_1(X26,u1_struct_0(X25))
        | ~ l1_orders_2(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_yellow_0])])])])).

cnf(c_0_36,negated_conjecture,
    ( u1_struct_0(esk6_0) = esk7_0
    | r2_hidden(esk1_2(u1_struct_0(esk6_0),esk7_0),X1)
    | ~ v13_waybel_0(X1,esk6_0)
    | ~ r1_orders_2(esk6_0,X2,esk1_2(u1_struct_0(esk6_0),esk7_0))
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])])).

cnf(c_0_37,negated_conjecture,
    ( v13_waybel_0(esk7_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_38,negated_conjecture,
    ( u1_struct_0(esk6_0) = esk7_0
    | ~ r2_hidden(esk1_2(u1_struct_0(esk6_0),esk7_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_21])).

cnf(c_0_39,negated_conjecture,
    ( u1_struct_0(esk6_0) = esk7_0
    | r2_hidden(k3_yellow_0(esk6_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_40,plain,
    ( k3_yellow_0(X1) = k1_yellow_0(X1,k1_xboole_0)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_41,plain,(
    ! [X8] :
      ( m1_subset_1(esk2_1(X8),k1_zfmisc_1(X8))
      & ~ v1_subset_1(esk2_1(X8),X8) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[rc3_subset_1])])])).

cnf(c_0_42,plain,
    ( r1_orders_2(X1,k1_yellow_0(X1,X2),X3)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ r1_yellow_0(X1,X2)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_32]),c_0_33])).

cnf(c_0_43,negated_conjecture,
    ( v5_orders_2(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_44,negated_conjecture,
    ( ~ v2_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_45,plain,
    ( r1_yellow_0(X1,k1_xboole_0)
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_yellow_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_46,negated_conjecture,
    ( v1_yellow_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_47,plain,
    ( r2_lattice3(X1,k1_xboole_0,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_48,negated_conjecture,
    ( u1_struct_0(esk6_0) = esk7_0
    | ~ r1_orders_2(esk6_0,X1,esk1_2(u1_struct_0(esk6_0),esk7_0))
    | ~ r2_hidden(X1,esk7_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_21])]),c_0_38])).

cnf(c_0_49,negated_conjecture,
    ( u1_struct_0(esk6_0) = esk7_0
    | r2_hidden(k1_yellow_0(esk6_0,k1_xboole_0),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_27])])).

cnf(c_0_50,plain,
    ( m1_subset_1(esk2_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_51,plain,
    ( ~ v1_subset_1(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_52,plain,(
    ! [X10,X11] :
      ( ~ m1_subset_1(X10,X11)
      | v1_xboole_0(X11)
      | r2_hidden(X10,X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_53,negated_conjecture,
    ( v1_subset_1(esk7_0,u1_struct_0(esk6_0))
    | ~ r2_hidden(k3_yellow_0(esk6_0),esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_54,negated_conjecture,
    ( u1_struct_0(esk6_0) = esk7_0
    | r1_orders_2(esk6_0,k1_yellow_0(esk6_0,X1),esk1_2(u1_struct_0(esk6_0),esk7_0))
    | ~ r2_lattice3(esk6_0,X1,esk1_2(u1_struct_0(esk6_0),esk7_0))
    | ~ r1_yellow_0(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_26]),c_0_43]),c_0_27])])).

cnf(c_0_55,negated_conjecture,
    ( r1_yellow_0(esk6_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46]),c_0_43]),c_0_27])])).

cnf(c_0_56,negated_conjecture,
    ( u1_struct_0(esk6_0) = esk7_0
    | r2_lattice3(esk6_0,k1_xboole_0,esk1_2(u1_struct_0(esk6_0),esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_26]),c_0_27])])).

cnf(c_0_57,negated_conjecture,
    ( u1_struct_0(esk6_0) = esk7_0
    | ~ r1_orders_2(esk6_0,k1_yellow_0(esk6_0,k1_xboole_0),esk1_2(u1_struct_0(esk6_0),esk7_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_58,plain,
    ( esk2_1(X1) = X1 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_50]),c_0_51])).

cnf(c_0_59,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_60,negated_conjecture,
    ( v1_subset_1(esk7_0,u1_struct_0(esk6_0))
    | ~ r2_hidden(k1_yellow_0(esk6_0,k1_xboole_0),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_40]),c_0_27])])).

cnf(c_0_61,negated_conjecture,
    ( u1_struct_0(esk6_0) = esk7_0 ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56]),c_0_57])).

cnf(c_0_62,plain,
    ( ~ v1_subset_1(X1,X1) ),
    inference(rw,[status(thm)],[c_0_51,c_0_58])).

cnf(c_0_63,plain,
    ( v1_xboole_0(u1_struct_0(X1))
    | r2_hidden(k1_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_59,c_0_33])).

cnf(c_0_64,negated_conjecture,
    ( ~ v1_xboole_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_65,negated_conjecture,
    ( ~ r2_hidden(k1_yellow_0(esk6_0,k1_xboole_0),esk7_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_61]),c_0_62])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(k1_yellow_0(esk6_0,X1),esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_61]),c_0_27])]),c_0_64])).

cnf(c_0_67,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_66])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:11:05 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.40  # AutoSched0-Mode selected heuristic G_E___008_C18_F1_PI_SE_CS_SP_CO_S4S
% 0.14/0.40  # and selection function SelectNewComplexAHPNS.
% 0.14/0.40  #
% 0.14/0.40  # Preprocessing time       : 0.029 s
% 0.14/0.40  
% 0.14/0.40  # Proof found!
% 0.14/0.40  # SZS status Theorem
% 0.14/0.40  # SZS output start CNFRefutation
% 0.14/0.40  fof(t8_waybel_7, conjecture, ![X1]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&v1_yellow_0(X1))&l1_orders_2(X1))=>![X2]:((((~(v1_xboole_0(X2))&v2_waybel_0(X2,X1))&v13_waybel_0(X2,X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v1_subset_1(X2,u1_struct_0(X1))<=>~(r2_hidden(k3_yellow_0(X1),X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_waybel_7)).
% 0.14/0.40  fof(d20_waybel_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v13_waybel_0(X2,X1)<=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((r2_hidden(X3,X2)&r1_orders_2(X1,X3,X4))=>r2_hidden(X4,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d20_waybel_0)).
% 0.14/0.40  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 0.14/0.40  fof(t49_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(![X3]:(m1_subset_1(X3,X1)=>r2_hidden(X3,X2))=>X1=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_subset_1)).
% 0.14/0.40  fof(d7_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(v1_subset_1(X2,X1)<=>X2!=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 0.14/0.40  fof(t30_yellow_0, axiom, ![X1]:((v5_orders_2(X1)&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(((X2=k1_yellow_0(X1,X3)&r1_yellow_0(X1,X3))=>(r2_lattice3(X1,X3,X2)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_lattice3(X1,X3,X4)=>r1_orders_2(X1,X2,X4)))))&((r2_lattice3(X1,X3,X2)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_lattice3(X1,X3,X4)=>r1_orders_2(X1,X2,X4))))=>(X2=k1_yellow_0(X1,X3)&r1_yellow_0(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_yellow_0)).
% 0.14/0.40  fof(dt_k1_yellow_0, axiom, ![X1, X2]:(l1_orders_2(X1)=>m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_yellow_0)).
% 0.14/0.40  fof(d11_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>k3_yellow_0(X1)=k1_yellow_0(X1,k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_yellow_0)).
% 0.14/0.40  fof(t42_yellow_0, axiom, ![X1]:((((~(v2_struct_0(X1))&v5_orders_2(X1))&v1_yellow_0(X1))&l1_orders_2(X1))=>(r1_yellow_0(X1,k1_xboole_0)&r2_yellow_0(X1,u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_yellow_0)).
% 0.14/0.40  fof(t6_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(r2_lattice3(X1,k1_xboole_0,X2)&r1_lattice3(X1,k1_xboole_0,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_yellow_0)).
% 0.14/0.40  fof(rc3_subset_1, axiom, ![X1]:?[X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))&~(v1_subset_1(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc3_subset_1)).
% 0.14/0.40  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 0.14/0.40  fof(c_0_12, negated_conjecture, ~(![X1]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&v1_yellow_0(X1))&l1_orders_2(X1))=>![X2]:((((~(v1_xboole_0(X2))&v2_waybel_0(X2,X1))&v13_waybel_0(X2,X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v1_subset_1(X2,u1_struct_0(X1))<=>~(r2_hidden(k3_yellow_0(X1),X2)))))), inference(assume_negation,[status(cth)],[t8_waybel_7])).
% 0.14/0.40  fof(c_0_13, plain, ![X27, X28, X29, X30]:((~v13_waybel_0(X28,X27)|(~m1_subset_1(X29,u1_struct_0(X27))|(~m1_subset_1(X30,u1_struct_0(X27))|(~r2_hidden(X29,X28)|~r1_orders_2(X27,X29,X30)|r2_hidden(X30,X28))))|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))|~l1_orders_2(X27))&((m1_subset_1(esk4_2(X27,X28),u1_struct_0(X27))|v13_waybel_0(X28,X27)|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))|~l1_orders_2(X27))&((m1_subset_1(esk5_2(X27,X28),u1_struct_0(X27))|v13_waybel_0(X28,X27)|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))|~l1_orders_2(X27))&(((r2_hidden(esk4_2(X27,X28),X28)|v13_waybel_0(X28,X27)|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))|~l1_orders_2(X27))&(r1_orders_2(X27,esk4_2(X27,X28),esk5_2(X27,X28))|v13_waybel_0(X28,X27)|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))|~l1_orders_2(X27)))&(~r2_hidden(esk5_2(X27,X28),X28)|v13_waybel_0(X28,X27)|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))|~l1_orders_2(X27)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d20_waybel_0])])])])])).
% 0.14/0.40  fof(c_0_14, plain, ![X12, X13, X14]:(~r2_hidden(X12,X13)|~m1_subset_1(X13,k1_zfmisc_1(X14))|m1_subset_1(X12,X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.14/0.40  fof(c_0_15, plain, ![X5, X6]:((m1_subset_1(esk1_2(X5,X6),X5)|X5=X6|~m1_subset_1(X6,k1_zfmisc_1(X5)))&(~r2_hidden(esk1_2(X5,X6),X6)|X5=X6|~m1_subset_1(X6,k1_zfmisc_1(X5)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t49_subset_1])])])])).
% 0.14/0.40  fof(c_0_16, negated_conjecture, ((((((~v2_struct_0(esk6_0)&v3_orders_2(esk6_0))&v4_orders_2(esk6_0))&v5_orders_2(esk6_0))&v1_yellow_0(esk6_0))&l1_orders_2(esk6_0))&((((~v1_xboole_0(esk7_0)&v2_waybel_0(esk7_0,esk6_0))&v13_waybel_0(esk7_0,esk6_0))&m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk6_0))))&((~v1_subset_1(esk7_0,u1_struct_0(esk6_0))|r2_hidden(k3_yellow_0(esk6_0),esk7_0))&(v1_subset_1(esk7_0,u1_struct_0(esk6_0))|~r2_hidden(k3_yellow_0(esk6_0),esk7_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])).
% 0.14/0.40  fof(c_0_17, plain, ![X33, X34]:((~v1_subset_1(X34,X33)|X34!=X33|~m1_subset_1(X34,k1_zfmisc_1(X33)))&(X34=X33|v1_subset_1(X34,X33)|~m1_subset_1(X34,k1_zfmisc_1(X33)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).
% 0.14/0.40  cnf(c_0_18, plain, (r2_hidden(X4,X1)|~v13_waybel_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X2))|~m1_subset_1(X4,u1_struct_0(X2))|~r2_hidden(X3,X1)|~r1_orders_2(X2,X3,X4)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.40  cnf(c_0_19, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.40  cnf(c_0_20, plain, (m1_subset_1(esk1_2(X1,X2),X1)|X1=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.40  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.40  cnf(c_0_22, plain, (X1=X2|v1_subset_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.40  fof(c_0_23, plain, ![X18, X19, X20, X21, X22]:(((r2_lattice3(X18,X20,X19)|(X19!=k1_yellow_0(X18,X20)|~r1_yellow_0(X18,X20))|~m1_subset_1(X19,u1_struct_0(X18))|(~v5_orders_2(X18)|~l1_orders_2(X18)))&(~m1_subset_1(X21,u1_struct_0(X18))|(~r2_lattice3(X18,X20,X21)|r1_orders_2(X18,X19,X21))|(X19!=k1_yellow_0(X18,X20)|~r1_yellow_0(X18,X20))|~m1_subset_1(X19,u1_struct_0(X18))|(~v5_orders_2(X18)|~l1_orders_2(X18))))&(((X19=k1_yellow_0(X18,X22)|(m1_subset_1(esk3_3(X18,X19,X22),u1_struct_0(X18))|~r2_lattice3(X18,X22,X19))|~m1_subset_1(X19,u1_struct_0(X18))|(~v5_orders_2(X18)|~l1_orders_2(X18)))&(r1_yellow_0(X18,X22)|(m1_subset_1(esk3_3(X18,X19,X22),u1_struct_0(X18))|~r2_lattice3(X18,X22,X19))|~m1_subset_1(X19,u1_struct_0(X18))|(~v5_orders_2(X18)|~l1_orders_2(X18))))&(((X19=k1_yellow_0(X18,X22)|(r2_lattice3(X18,X22,esk3_3(X18,X19,X22))|~r2_lattice3(X18,X22,X19))|~m1_subset_1(X19,u1_struct_0(X18))|(~v5_orders_2(X18)|~l1_orders_2(X18)))&(r1_yellow_0(X18,X22)|(r2_lattice3(X18,X22,esk3_3(X18,X19,X22))|~r2_lattice3(X18,X22,X19))|~m1_subset_1(X19,u1_struct_0(X18))|(~v5_orders_2(X18)|~l1_orders_2(X18))))&((X19=k1_yellow_0(X18,X22)|(~r1_orders_2(X18,X19,esk3_3(X18,X19,X22))|~r2_lattice3(X18,X22,X19))|~m1_subset_1(X19,u1_struct_0(X18))|(~v5_orders_2(X18)|~l1_orders_2(X18)))&(r1_yellow_0(X18,X22)|(~r1_orders_2(X18,X19,esk3_3(X18,X19,X22))|~r2_lattice3(X18,X22,X19))|~m1_subset_1(X19,u1_struct_0(X18))|(~v5_orders_2(X18)|~l1_orders_2(X18))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_yellow_0])])])])])])).
% 0.14/0.40  fof(c_0_24, plain, ![X16, X17]:(~l1_orders_2(X16)|m1_subset_1(k1_yellow_0(X16,X17),u1_struct_0(X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_yellow_0])])).
% 0.14/0.40  cnf(c_0_25, plain, (r2_hidden(X1,X2)|~v13_waybel_0(X2,X3)|~r1_orders_2(X3,X4,X1)|~l1_orders_2(X3)|~r2_hidden(X4,X2)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~m1_subset_1(X1,u1_struct_0(X3))), inference(csr,[status(thm)],[c_0_18, c_0_19])).
% 0.14/0.40  cnf(c_0_26, negated_conjecture, (u1_struct_0(esk6_0)=esk7_0|m1_subset_1(esk1_2(u1_struct_0(esk6_0),esk7_0),u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.14/0.40  cnf(c_0_27, negated_conjecture, (l1_orders_2(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.40  cnf(c_0_28, plain, (X1=X2|~r2_hidden(esk1_2(X1,X2),X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.40  cnf(c_0_29, negated_conjecture, (r2_hidden(k3_yellow_0(esk6_0),esk7_0)|~v1_subset_1(esk7_0,u1_struct_0(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.40  cnf(c_0_30, negated_conjecture, (u1_struct_0(esk6_0)=esk7_0|v1_subset_1(esk7_0,u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_22, c_0_21])).
% 0.14/0.40  fof(c_0_31, plain, ![X15]:(~l1_orders_2(X15)|k3_yellow_0(X15)=k1_yellow_0(X15,k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_yellow_0])])).
% 0.14/0.40  cnf(c_0_32, plain, (r1_orders_2(X2,X4,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~r2_lattice3(X2,X3,X1)|X4!=k1_yellow_0(X2,X3)|~r1_yellow_0(X2,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.14/0.40  cnf(c_0_33, plain, (m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.14/0.40  fof(c_0_34, plain, ![X24]:((r1_yellow_0(X24,k1_xboole_0)|(v2_struct_0(X24)|~v5_orders_2(X24)|~v1_yellow_0(X24)|~l1_orders_2(X24)))&(r2_yellow_0(X24,u1_struct_0(X24))|(v2_struct_0(X24)|~v5_orders_2(X24)|~v1_yellow_0(X24)|~l1_orders_2(X24)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t42_yellow_0])])])])).
% 0.14/0.40  fof(c_0_35, plain, ![X25, X26]:((r2_lattice3(X25,k1_xboole_0,X26)|~m1_subset_1(X26,u1_struct_0(X25))|~l1_orders_2(X25))&(r1_lattice3(X25,k1_xboole_0,X26)|~m1_subset_1(X26,u1_struct_0(X25))|~l1_orders_2(X25))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_yellow_0])])])])).
% 0.14/0.40  cnf(c_0_36, negated_conjecture, (u1_struct_0(esk6_0)=esk7_0|r2_hidden(esk1_2(u1_struct_0(esk6_0),esk7_0),X1)|~v13_waybel_0(X1,esk6_0)|~r1_orders_2(esk6_0,X2,esk1_2(u1_struct_0(esk6_0),esk7_0))|~r2_hidden(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27])])).
% 0.14/0.40  cnf(c_0_37, negated_conjecture, (v13_waybel_0(esk7_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.40  cnf(c_0_38, negated_conjecture, (u1_struct_0(esk6_0)=esk7_0|~r2_hidden(esk1_2(u1_struct_0(esk6_0),esk7_0),esk7_0)), inference(spm,[status(thm)],[c_0_28, c_0_21])).
% 0.14/0.40  cnf(c_0_39, negated_conjecture, (u1_struct_0(esk6_0)=esk7_0|r2_hidden(k3_yellow_0(esk6_0),esk7_0)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.14/0.40  cnf(c_0_40, plain, (k3_yellow_0(X1)=k1_yellow_0(X1,k1_xboole_0)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.14/0.40  fof(c_0_41, plain, ![X8]:(m1_subset_1(esk2_1(X8),k1_zfmisc_1(X8))&~v1_subset_1(esk2_1(X8),X8)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[rc3_subset_1])])])).
% 0.14/0.40  cnf(c_0_42, plain, (r1_orders_2(X1,k1_yellow_0(X1,X2),X3)|~r2_lattice3(X1,X2,X3)|~r1_yellow_0(X1,X2)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X3,u1_struct_0(X1))), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_32]), c_0_33])).
% 0.14/0.40  cnf(c_0_43, negated_conjecture, (v5_orders_2(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.40  cnf(c_0_44, negated_conjecture, (~v2_struct_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.40  cnf(c_0_45, plain, (r1_yellow_0(X1,k1_xboole_0)|v2_struct_0(X1)|~v5_orders_2(X1)|~v1_yellow_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.14/0.40  cnf(c_0_46, negated_conjecture, (v1_yellow_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.40  cnf(c_0_47, plain, (r2_lattice3(X1,k1_xboole_0,X2)|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.14/0.40  cnf(c_0_48, negated_conjecture, (u1_struct_0(esk6_0)=esk7_0|~r1_orders_2(esk6_0,X1,esk1_2(u1_struct_0(esk6_0),esk7_0))|~r2_hidden(X1,esk7_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_21])]), c_0_38])).
% 0.14/0.40  cnf(c_0_49, negated_conjecture, (u1_struct_0(esk6_0)=esk7_0|r2_hidden(k1_yellow_0(esk6_0,k1_xboole_0),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_27])])).
% 0.14/0.40  cnf(c_0_50, plain, (m1_subset_1(esk2_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.14/0.40  cnf(c_0_51, plain, (~v1_subset_1(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.14/0.40  fof(c_0_52, plain, ![X10, X11]:(~m1_subset_1(X10,X11)|(v1_xboole_0(X11)|r2_hidden(X10,X11))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.14/0.40  cnf(c_0_53, negated_conjecture, (v1_subset_1(esk7_0,u1_struct_0(esk6_0))|~r2_hidden(k3_yellow_0(esk6_0),esk7_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.40  cnf(c_0_54, negated_conjecture, (u1_struct_0(esk6_0)=esk7_0|r1_orders_2(esk6_0,k1_yellow_0(esk6_0,X1),esk1_2(u1_struct_0(esk6_0),esk7_0))|~r2_lattice3(esk6_0,X1,esk1_2(u1_struct_0(esk6_0),esk7_0))|~r1_yellow_0(esk6_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_26]), c_0_43]), c_0_27])])).
% 0.14/0.40  cnf(c_0_55, negated_conjecture, (r1_yellow_0(esk6_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46]), c_0_43]), c_0_27])])).
% 0.14/0.40  cnf(c_0_56, negated_conjecture, (u1_struct_0(esk6_0)=esk7_0|r2_lattice3(esk6_0,k1_xboole_0,esk1_2(u1_struct_0(esk6_0),esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_26]), c_0_27])])).
% 0.14/0.40  cnf(c_0_57, negated_conjecture, (u1_struct_0(esk6_0)=esk7_0|~r1_orders_2(esk6_0,k1_yellow_0(esk6_0,k1_xboole_0),esk1_2(u1_struct_0(esk6_0),esk7_0))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.14/0.40  cnf(c_0_58, plain, (esk2_1(X1)=X1), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_50]), c_0_51])).
% 0.14/0.40  cnf(c_0_59, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.14/0.40  cnf(c_0_60, negated_conjecture, (v1_subset_1(esk7_0,u1_struct_0(esk6_0))|~r2_hidden(k1_yellow_0(esk6_0,k1_xboole_0),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_40]), c_0_27])])).
% 0.14/0.40  cnf(c_0_61, negated_conjecture, (u1_struct_0(esk6_0)=esk7_0), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56]), c_0_57])).
% 0.14/0.40  cnf(c_0_62, plain, (~v1_subset_1(X1,X1)), inference(rw,[status(thm)],[c_0_51, c_0_58])).
% 0.14/0.40  cnf(c_0_63, plain, (v1_xboole_0(u1_struct_0(X1))|r2_hidden(k1_yellow_0(X1,X2),u1_struct_0(X1))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_59, c_0_33])).
% 0.14/0.40  cnf(c_0_64, negated_conjecture, (~v1_xboole_0(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.40  cnf(c_0_65, negated_conjecture, (~r2_hidden(k1_yellow_0(esk6_0,k1_xboole_0),esk7_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_61]), c_0_62])).
% 0.14/0.40  cnf(c_0_66, negated_conjecture, (r2_hidden(k1_yellow_0(esk6_0,X1),esk7_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_61]), c_0_27])]), c_0_64])).
% 0.14/0.40  cnf(c_0_67, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_65, c_0_66])]), ['proof']).
% 0.14/0.40  # SZS output end CNFRefutation
% 0.14/0.40  # Proof object total steps             : 68
% 0.14/0.40  # Proof object clause steps            : 43
% 0.14/0.40  # Proof object formula steps           : 25
% 0.14/0.40  # Proof object conjectures             : 28
% 0.14/0.40  # Proof object clause conjectures      : 25
% 0.14/0.40  # Proof object formula conjectures     : 3
% 0.14/0.40  # Proof object initial clauses used    : 22
% 0.14/0.40  # Proof object initial formulas used   : 12
% 0.14/0.40  # Proof object generating inferences   : 16
% 0.14/0.40  # Proof object simplifying inferences  : 32
% 0.14/0.40  # Training examples: 0 positive, 0 negative
% 0.14/0.40  # Parsed axioms                        : 12
% 0.14/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.40  # Initial clauses                      : 40
% 0.14/0.40  # Removed in clause preprocessing      : 0
% 0.14/0.40  # Initial clauses in saturation        : 40
% 0.14/0.40  # Processed clauses                    : 206
% 0.14/0.40  # ...of these trivial                  : 0
% 0.14/0.40  # ...subsumed                          : 41
% 0.14/0.40  # ...remaining for further processing  : 165
% 0.14/0.40  # Other redundant clauses eliminated   : 3
% 0.14/0.40  # Clauses deleted for lack of memory   : 0
% 0.14/0.40  # Backward-subsumed                    : 2
% 0.14/0.40  # Backward-rewritten                   : 90
% 0.14/0.40  # Generated clauses                    : 269
% 0.14/0.40  # ...of the previous two non-trivial   : 239
% 0.14/0.40  # Contextual simplify-reflections      : 7
% 0.14/0.40  # Paramodulations                      : 266
% 0.14/0.40  # Factorizations                       : 0
% 0.14/0.40  # Equation resolutions                 : 3
% 0.14/0.40  # Propositional unsat checks           : 0
% 0.14/0.40  #    Propositional check models        : 0
% 0.14/0.40  #    Propositional check unsatisfiable : 0
% 0.14/0.40  #    Propositional clauses             : 0
% 0.14/0.40  #    Propositional clauses after purity: 0
% 0.14/0.40  #    Propositional unsat core size     : 0
% 0.14/0.40  #    Propositional preprocessing time  : 0.000
% 0.14/0.40  #    Propositional encoding time       : 0.000
% 0.14/0.40  #    Propositional solver time         : 0.000
% 0.14/0.40  #    Success case prop preproc time    : 0.000
% 0.14/0.40  #    Success case prop encoding time   : 0.000
% 0.14/0.40  #    Success case prop solver time     : 0.000
% 0.14/0.40  # Current number of processed clauses  : 70
% 0.14/0.40  #    Positive orientable unit clauses  : 15
% 0.14/0.40  #    Positive unorientable unit clauses: 0
% 0.14/0.40  #    Negative unit clauses             : 4
% 0.14/0.40  #    Non-unit-clauses                  : 51
% 0.14/0.40  # Current number of unprocessed clauses: 64
% 0.14/0.40  # ...number of literals in the above   : 322
% 0.14/0.40  # Current number of archived formulas  : 0
% 0.14/0.40  # Current number of archived clauses   : 92
% 0.14/0.40  # Clause-clause subsumption calls (NU) : 2842
% 0.14/0.40  # Rec. Clause-clause subsumption calls : 543
% 0.14/0.40  # Non-unit clause-clause subsumptions  : 46
% 0.14/0.40  # Unit Clause-clause subsumption calls : 106
% 0.14/0.40  # Rewrite failures with RHS unbound    : 0
% 0.14/0.40  # BW rewrite match attempts            : 15
% 0.14/0.40  # BW rewrite match successes           : 6
% 0.14/0.40  # Condensation attempts                : 207
% 0.14/0.40  # Condensation successes               : 0
% 0.14/0.40  # Termbank termtop insertions          : 10738
% 0.14/0.40  
% 0.14/0.40  # -------------------------------------------------
% 0.14/0.40  # User time                : 0.045 s
% 0.14/0.40  # System time              : 0.006 s
% 0.14/0.40  # Total time               : 0.051 s
% 0.14/0.40  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
