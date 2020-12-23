%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:26 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 421 expanded)
%              Number of clauses        :   47 ( 164 expanded)
%              Number of leaves         :   13 ( 102 expanded)
%              Depth                    :   14
%              Number of atoms          :  345 (3171 expanded)
%              Number of equality atoms :   34 ( 145 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   50 (   3 average)
%              Maximal term depth       :    4 (   1 average)

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

fof(d9_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2,X3] :
          ( m1_subset_1(X3,u1_struct_0(X1))
         => ( r2_lattice3(X1,X2,X3)
          <=> ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_hidden(X4,X2)
                 => r1_orders_2(X1,X4,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattice3)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(c_0_13,negated_conjecture,(
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

fof(c_0_14,plain,(
    ! [X32,X33,X34,X35] :
      ( ( ~ v13_waybel_0(X33,X32)
        | ~ m1_subset_1(X34,u1_struct_0(X32))
        | ~ m1_subset_1(X35,u1_struct_0(X32))
        | ~ r2_hidden(X34,X33)
        | ~ r1_orders_2(X32,X34,X35)
        | r2_hidden(X35,X33)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))
        | ~ l1_orders_2(X32) )
      & ( m1_subset_1(esk5_2(X32,X33),u1_struct_0(X32))
        | v13_waybel_0(X33,X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))
        | ~ l1_orders_2(X32) )
      & ( m1_subset_1(esk6_2(X32,X33),u1_struct_0(X32))
        | v13_waybel_0(X33,X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))
        | ~ l1_orders_2(X32) )
      & ( r2_hidden(esk5_2(X32,X33),X33)
        | v13_waybel_0(X33,X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))
        | ~ l1_orders_2(X32) )
      & ( r1_orders_2(X32,esk5_2(X32,X33),esk6_2(X32,X33))
        | v13_waybel_0(X33,X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))
        | ~ l1_orders_2(X32) )
      & ( ~ r2_hidden(esk6_2(X32,X33),X33)
        | v13_waybel_0(X33,X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))
        | ~ l1_orders_2(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d20_waybel_0])])])])])).

fof(c_0_15,plain,(
    ! [X14,X15,X16] :
      ( ~ r2_hidden(X14,X15)
      | ~ m1_subset_1(X15,k1_zfmisc_1(X16))
      | m1_subset_1(X14,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_16,plain,(
    ! [X9,X10] :
      ( ( m1_subset_1(esk2_2(X9,X10),X9)
        | X9 = X10
        | ~ m1_subset_1(X10,k1_zfmisc_1(X9)) )
      & ( ~ r2_hidden(esk2_2(X9,X10),X10)
        | X9 = X10
        | ~ m1_subset_1(X10,k1_zfmisc_1(X9)) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t49_subset_1])])])])).

fof(c_0_17,negated_conjecture,
    ( ~ v2_struct_0(esk7_0)
    & v3_orders_2(esk7_0)
    & v4_orders_2(esk7_0)
    & v5_orders_2(esk7_0)
    & v1_yellow_0(esk7_0)
    & l1_orders_2(esk7_0)
    & ~ v1_xboole_0(esk8_0)
    & v2_waybel_0(esk8_0,esk7_0)
    & v13_waybel_0(esk8_0,esk7_0)
    & m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(esk7_0)))
    & ( ~ v1_subset_1(esk8_0,u1_struct_0(esk7_0))
      | r2_hidden(k3_yellow_0(esk7_0),esk8_0) )
    & ( v1_subset_1(esk8_0,u1_struct_0(esk7_0))
      | ~ r2_hidden(k3_yellow_0(esk7_0),esk8_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).

fof(c_0_18,plain,(
    ! [X38,X39] :
      ( ( ~ v1_subset_1(X39,X38)
        | X39 != X38
        | ~ m1_subset_1(X39,k1_zfmisc_1(X38)) )
      & ( X39 = X38
        | v1_subset_1(X39,X38)
        | ~ m1_subset_1(X39,k1_zfmisc_1(X38)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).

cnf(c_0_19,plain,
    ( r2_hidden(X4,X1)
    | ~ v13_waybel_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r2_hidden(X3,X1)
    | ~ r1_orders_2(X2,X3,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( m1_subset_1(esk2_2(X1,X2),X1)
    | X1 = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( X1 = X2
    | v1_subset_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_24,plain,(
    ! [X25,X26,X27,X28,X29] :
      ( ( r2_lattice3(X25,X27,X26)
        | X26 != k1_yellow_0(X25,X27)
        | ~ r1_yellow_0(X25,X27)
        | ~ m1_subset_1(X26,u1_struct_0(X25))
        | ~ v5_orders_2(X25)
        | ~ l1_orders_2(X25) )
      & ( ~ m1_subset_1(X28,u1_struct_0(X25))
        | ~ r2_lattice3(X25,X27,X28)
        | r1_orders_2(X25,X26,X28)
        | X26 != k1_yellow_0(X25,X27)
        | ~ r1_yellow_0(X25,X27)
        | ~ m1_subset_1(X26,u1_struct_0(X25))
        | ~ v5_orders_2(X25)
        | ~ l1_orders_2(X25) )
      & ( X26 = k1_yellow_0(X25,X29)
        | m1_subset_1(esk4_3(X25,X26,X29),u1_struct_0(X25))
        | ~ r2_lattice3(X25,X29,X26)
        | ~ m1_subset_1(X26,u1_struct_0(X25))
        | ~ v5_orders_2(X25)
        | ~ l1_orders_2(X25) )
      & ( r1_yellow_0(X25,X29)
        | m1_subset_1(esk4_3(X25,X26,X29),u1_struct_0(X25))
        | ~ r2_lattice3(X25,X29,X26)
        | ~ m1_subset_1(X26,u1_struct_0(X25))
        | ~ v5_orders_2(X25)
        | ~ l1_orders_2(X25) )
      & ( X26 = k1_yellow_0(X25,X29)
        | r2_lattice3(X25,X29,esk4_3(X25,X26,X29))
        | ~ r2_lattice3(X25,X29,X26)
        | ~ m1_subset_1(X26,u1_struct_0(X25))
        | ~ v5_orders_2(X25)
        | ~ l1_orders_2(X25) )
      & ( r1_yellow_0(X25,X29)
        | r2_lattice3(X25,X29,esk4_3(X25,X26,X29))
        | ~ r2_lattice3(X25,X29,X26)
        | ~ m1_subset_1(X26,u1_struct_0(X25))
        | ~ v5_orders_2(X25)
        | ~ l1_orders_2(X25) )
      & ( X26 = k1_yellow_0(X25,X29)
        | ~ r1_orders_2(X25,X26,esk4_3(X25,X26,X29))
        | ~ r2_lattice3(X25,X29,X26)
        | ~ m1_subset_1(X26,u1_struct_0(X25))
        | ~ v5_orders_2(X25)
        | ~ l1_orders_2(X25) )
      & ( r1_yellow_0(X25,X29)
        | ~ r1_orders_2(X25,X26,esk4_3(X25,X26,X29))
        | ~ r2_lattice3(X25,X29,X26)
        | ~ m1_subset_1(X26,u1_struct_0(X25))
        | ~ v5_orders_2(X25)
        | ~ l1_orders_2(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_yellow_0])])])])])])).

fof(c_0_25,plain,(
    ! [X23,X24] :
      ( ~ l1_orders_2(X23)
      | m1_subset_1(k1_yellow_0(X23,X24),u1_struct_0(X23)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_yellow_0])])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,X2)
    | ~ v13_waybel_0(X2,X3)
    | ~ r1_orders_2(X3,X4,X1)
    | ~ l1_orders_2(X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ r2_hidden(X4,X2) ),
    inference(csr,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( u1_struct_0(esk7_0) = esk8_0
    | m1_subset_1(esk2_2(u1_struct_0(esk7_0),esk8_0),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( l1_orders_2(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_29,plain,
    ( X1 = X2
    | ~ r2_hidden(esk2_2(X1,X2),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(k3_yellow_0(esk7_0),esk8_0)
    | ~ v1_subset_1(esk8_0,u1_struct_0(esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_31,negated_conjecture,
    ( u1_struct_0(esk7_0) = esk8_0
    | v1_subset_1(esk8_0,u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_22])).

fof(c_0_32,plain,(
    ! [X22] :
      ( ~ l1_orders_2(X22)
      | k3_yellow_0(X22) = k1_yellow_0(X22,k1_xboole_0) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_yellow_0])])).

cnf(c_0_33,plain,
    ( r1_orders_2(X2,X4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X1)
    | X4 != k1_yellow_0(X2,X3)
    | ~ r1_yellow_0(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,plain,
    ( m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_35,plain,(
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

cnf(c_0_36,negated_conjecture,
    ( u1_struct_0(esk7_0) = esk8_0
    | r2_hidden(esk2_2(u1_struct_0(esk7_0),esk8_0),X1)
    | ~ v13_waybel_0(X1,esk7_0)
    | ~ r1_orders_2(esk7_0,X2,esk2_2(u1_struct_0(esk7_0),esk8_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk7_0)))
    | ~ r2_hidden(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])])).

cnf(c_0_37,negated_conjecture,
    ( v13_waybel_0(esk8_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_38,negated_conjecture,
    ( u1_struct_0(esk7_0) = esk8_0
    | ~ r2_hidden(esk2_2(u1_struct_0(esk7_0),esk8_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_22])).

cnf(c_0_39,negated_conjecture,
    ( u1_struct_0(esk7_0) = esk8_0
    | r2_hidden(k3_yellow_0(esk7_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_40,plain,
    ( k3_yellow_0(X1) = k1_yellow_0(X1,k1_xboole_0)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_41,plain,(
    ! [X17,X18,X19,X20] :
      ( ( ~ r2_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ r2_hidden(X20,X18)
        | r1_orders_2(X17,X20,X19)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ l1_orders_2(X17) )
      & ( m1_subset_1(esk3_3(X17,X18,X19),u1_struct_0(X17))
        | r2_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ l1_orders_2(X17) )
      & ( r2_hidden(esk3_3(X17,X18,X19),X18)
        | r2_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ l1_orders_2(X17) )
      & ( ~ r1_orders_2(X17,esk3_3(X17,X18,X19),X19)
        | r2_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ l1_orders_2(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).

cnf(c_0_42,plain,
    ( r1_orders_2(X1,k1_yellow_0(X1,X2),X3)
    | ~ r1_yellow_0(X1,X2)
    | ~ v5_orders_2(X1)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_33]),c_0_34])).

cnf(c_0_43,negated_conjecture,
    ( v5_orders_2(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_44,negated_conjecture,
    ( ~ v2_struct_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_45,plain,
    ( r1_yellow_0(X1,k1_xboole_0)
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_yellow_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_46,negated_conjecture,
    ( v1_yellow_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_47,negated_conjecture,
    ( u1_struct_0(esk7_0) = esk8_0
    | ~ r1_orders_2(esk7_0,X1,esk2_2(u1_struct_0(esk7_0),esk8_0))
    | ~ r2_hidden(X1,esk8_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_22])]),c_0_38])).

cnf(c_0_48,negated_conjecture,
    ( u1_struct_0(esk7_0) = esk8_0
    | r2_hidden(k1_yellow_0(esk7_0,k1_xboole_0),esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_28])])).

fof(c_0_49,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_50,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),X2)
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_51,negated_conjecture,
    ( u1_struct_0(esk7_0) = esk8_0
    | r1_orders_2(esk7_0,k1_yellow_0(esk7_0,X1),esk2_2(u1_struct_0(esk7_0),esk8_0))
    | ~ r1_yellow_0(esk7_0,X1)
    | ~ r2_lattice3(esk7_0,X1,esk2_2(u1_struct_0(esk7_0),esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_27]),c_0_43]),c_0_28])])).

cnf(c_0_52,negated_conjecture,
    ( r1_yellow_0(esk7_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46]),c_0_43]),c_0_28])])).

cnf(c_0_53,negated_conjecture,
    ( u1_struct_0(esk7_0) = esk8_0
    | ~ r1_orders_2(esk7_0,k1_yellow_0(esk7_0,k1_xboole_0),esk2_2(u1_struct_0(esk7_0),esk8_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_54,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_55,negated_conjecture,
    ( u1_struct_0(esk7_0) = esk8_0
    | r2_lattice3(esk7_0,X1,esk2_2(u1_struct_0(esk7_0),esk8_0))
    | r2_hidden(esk3_3(esk7_0,X1,esk2_2(u1_struct_0(esk7_0),esk8_0)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_27]),c_0_28])])).

cnf(c_0_56,negated_conjecture,
    ( u1_struct_0(esk7_0) = esk8_0
    | ~ r2_lattice3(esk7_0,k1_xboole_0,esk2_2(u1_struct_0(esk7_0),esk8_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53])).

cnf(c_0_57,negated_conjecture,
    ( u1_struct_0(esk7_0) = esk8_0
    | r2_lattice3(esk7_0,X1,esk2_2(u1_struct_0(esk7_0),esk8_0))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_58,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_59,plain,
    ( ~ v1_subset_1(X1,X2)
    | X1 != X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_60,negated_conjecture,
    ( u1_struct_0(esk7_0) = esk8_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58])])).

cnf(c_0_61,plain,
    ( ~ v1_subset_1(X1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(er,[status(thm)],[c_0_59])).

cnf(c_0_62,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(esk8_0)) ),
    inference(rw,[status(thm)],[c_0_22,c_0_60])).

fof(c_0_63,plain,(
    ! [X12,X13] :
      ( ~ m1_subset_1(X12,X13)
      | v1_xboole_0(X13)
      | r2_hidden(X12,X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_64,negated_conjecture,
    ( v1_subset_1(esk8_0,u1_struct_0(esk7_0))
    | ~ r2_hidden(k3_yellow_0(esk7_0),esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_65,negated_conjecture,
    ( ~ v1_subset_1(esk8_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_66,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_67,negated_conjecture,
    ( ~ r2_hidden(k3_yellow_0(esk7_0),esk8_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_60]),c_0_65])).

cnf(c_0_68,plain,
    ( r2_hidden(k1_yellow_0(X1,X2),u1_struct_0(X1))
    | v1_xboole_0(u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_66,c_0_34])).

cnf(c_0_69,negated_conjecture,
    ( ~ v1_xboole_0(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_70,negated_conjecture,
    ( ~ r2_hidden(k1_yellow_0(esk7_0,k1_xboole_0),esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_40]),c_0_28])])).

cnf(c_0_71,negated_conjecture,
    ( r2_hidden(k1_yellow_0(esk7_0,X1),esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_60]),c_0_28])]),c_0_69])).

cnf(c_0_72,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_71])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:29:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.40  # AutoSched0-Mode selected heuristic G_E___008_C18_F1_PI_SE_CS_SP_CO_S4S
% 0.13/0.40  # and selection function SelectNewComplexAHPNS.
% 0.13/0.40  #
% 0.13/0.40  # Preprocessing time       : 0.029 s
% 0.13/0.40  
% 0.13/0.40  # Proof found!
% 0.13/0.40  # SZS status Theorem
% 0.13/0.40  # SZS output start CNFRefutation
% 0.13/0.40  fof(t8_waybel_7, conjecture, ![X1]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&v1_yellow_0(X1))&l1_orders_2(X1))=>![X2]:((((~(v1_xboole_0(X2))&v2_waybel_0(X2,X1))&v13_waybel_0(X2,X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v1_subset_1(X2,u1_struct_0(X1))<=>~(r2_hidden(k3_yellow_0(X1),X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_waybel_7)).
% 0.13/0.40  fof(d20_waybel_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v13_waybel_0(X2,X1)<=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((r2_hidden(X3,X2)&r1_orders_2(X1,X3,X4))=>r2_hidden(X4,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d20_waybel_0)).
% 0.13/0.40  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 0.13/0.40  fof(t49_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(![X3]:(m1_subset_1(X3,X1)=>r2_hidden(X3,X2))=>X1=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_subset_1)).
% 0.13/0.40  fof(d7_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(v1_subset_1(X2,X1)<=>X2!=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 0.13/0.40  fof(t30_yellow_0, axiom, ![X1]:((v5_orders_2(X1)&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(((X2=k1_yellow_0(X1,X3)&r1_yellow_0(X1,X3))=>(r2_lattice3(X1,X3,X2)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_lattice3(X1,X3,X4)=>r1_orders_2(X1,X2,X4)))))&((r2_lattice3(X1,X3,X2)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_lattice3(X1,X3,X4)=>r1_orders_2(X1,X2,X4))))=>(X2=k1_yellow_0(X1,X3)&r1_yellow_0(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_yellow_0)).
% 0.13/0.40  fof(dt_k1_yellow_0, axiom, ![X1, X2]:(l1_orders_2(X1)=>m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_yellow_0)).
% 0.13/0.40  fof(d11_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>k3_yellow_0(X1)=k1_yellow_0(X1,k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_yellow_0)).
% 0.13/0.40  fof(t42_yellow_0, axiom, ![X1]:((((~(v2_struct_0(X1))&v5_orders_2(X1))&v1_yellow_0(X1))&l1_orders_2(X1))=>(r1_yellow_0(X1,k1_xboole_0)&r2_yellow_0(X1,u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_yellow_0)).
% 0.13/0.40  fof(d9_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X2)=>r1_orders_2(X1,X4,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_lattice3)).
% 0.13/0.40  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.13/0.40  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.13/0.40  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 0.13/0.40  fof(c_0_13, negated_conjecture, ~(![X1]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&v1_yellow_0(X1))&l1_orders_2(X1))=>![X2]:((((~(v1_xboole_0(X2))&v2_waybel_0(X2,X1))&v13_waybel_0(X2,X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v1_subset_1(X2,u1_struct_0(X1))<=>~(r2_hidden(k3_yellow_0(X1),X2)))))), inference(assume_negation,[status(cth)],[t8_waybel_7])).
% 0.13/0.40  fof(c_0_14, plain, ![X32, X33, X34, X35]:((~v13_waybel_0(X33,X32)|(~m1_subset_1(X34,u1_struct_0(X32))|(~m1_subset_1(X35,u1_struct_0(X32))|(~r2_hidden(X34,X33)|~r1_orders_2(X32,X34,X35)|r2_hidden(X35,X33))))|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))|~l1_orders_2(X32))&((m1_subset_1(esk5_2(X32,X33),u1_struct_0(X32))|v13_waybel_0(X33,X32)|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))|~l1_orders_2(X32))&((m1_subset_1(esk6_2(X32,X33),u1_struct_0(X32))|v13_waybel_0(X33,X32)|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))|~l1_orders_2(X32))&(((r2_hidden(esk5_2(X32,X33),X33)|v13_waybel_0(X33,X32)|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))|~l1_orders_2(X32))&(r1_orders_2(X32,esk5_2(X32,X33),esk6_2(X32,X33))|v13_waybel_0(X33,X32)|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))|~l1_orders_2(X32)))&(~r2_hidden(esk6_2(X32,X33),X33)|v13_waybel_0(X33,X32)|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))|~l1_orders_2(X32)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d20_waybel_0])])])])])).
% 0.13/0.40  fof(c_0_15, plain, ![X14, X15, X16]:(~r2_hidden(X14,X15)|~m1_subset_1(X15,k1_zfmisc_1(X16))|m1_subset_1(X14,X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.13/0.40  fof(c_0_16, plain, ![X9, X10]:((m1_subset_1(esk2_2(X9,X10),X9)|X9=X10|~m1_subset_1(X10,k1_zfmisc_1(X9)))&(~r2_hidden(esk2_2(X9,X10),X10)|X9=X10|~m1_subset_1(X10,k1_zfmisc_1(X9)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t49_subset_1])])])])).
% 0.13/0.40  fof(c_0_17, negated_conjecture, ((((((~v2_struct_0(esk7_0)&v3_orders_2(esk7_0))&v4_orders_2(esk7_0))&v5_orders_2(esk7_0))&v1_yellow_0(esk7_0))&l1_orders_2(esk7_0))&((((~v1_xboole_0(esk8_0)&v2_waybel_0(esk8_0,esk7_0))&v13_waybel_0(esk8_0,esk7_0))&m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(esk7_0))))&((~v1_subset_1(esk8_0,u1_struct_0(esk7_0))|r2_hidden(k3_yellow_0(esk7_0),esk8_0))&(v1_subset_1(esk8_0,u1_struct_0(esk7_0))|~r2_hidden(k3_yellow_0(esk7_0),esk8_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).
% 0.13/0.40  fof(c_0_18, plain, ![X38, X39]:((~v1_subset_1(X39,X38)|X39!=X38|~m1_subset_1(X39,k1_zfmisc_1(X38)))&(X39=X38|v1_subset_1(X39,X38)|~m1_subset_1(X39,k1_zfmisc_1(X38)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).
% 0.13/0.40  cnf(c_0_19, plain, (r2_hidden(X4,X1)|~v13_waybel_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X2))|~m1_subset_1(X4,u1_struct_0(X2))|~r2_hidden(X3,X1)|~r1_orders_2(X2,X3,X4)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.40  cnf(c_0_20, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.40  cnf(c_0_21, plain, (m1_subset_1(esk2_2(X1,X2),X1)|X1=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.40  cnf(c_0_22, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(esk7_0)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.40  cnf(c_0_23, plain, (X1=X2|v1_subset_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.40  fof(c_0_24, plain, ![X25, X26, X27, X28, X29]:(((r2_lattice3(X25,X27,X26)|(X26!=k1_yellow_0(X25,X27)|~r1_yellow_0(X25,X27))|~m1_subset_1(X26,u1_struct_0(X25))|(~v5_orders_2(X25)|~l1_orders_2(X25)))&(~m1_subset_1(X28,u1_struct_0(X25))|(~r2_lattice3(X25,X27,X28)|r1_orders_2(X25,X26,X28))|(X26!=k1_yellow_0(X25,X27)|~r1_yellow_0(X25,X27))|~m1_subset_1(X26,u1_struct_0(X25))|(~v5_orders_2(X25)|~l1_orders_2(X25))))&(((X26=k1_yellow_0(X25,X29)|(m1_subset_1(esk4_3(X25,X26,X29),u1_struct_0(X25))|~r2_lattice3(X25,X29,X26))|~m1_subset_1(X26,u1_struct_0(X25))|(~v5_orders_2(X25)|~l1_orders_2(X25)))&(r1_yellow_0(X25,X29)|(m1_subset_1(esk4_3(X25,X26,X29),u1_struct_0(X25))|~r2_lattice3(X25,X29,X26))|~m1_subset_1(X26,u1_struct_0(X25))|(~v5_orders_2(X25)|~l1_orders_2(X25))))&(((X26=k1_yellow_0(X25,X29)|(r2_lattice3(X25,X29,esk4_3(X25,X26,X29))|~r2_lattice3(X25,X29,X26))|~m1_subset_1(X26,u1_struct_0(X25))|(~v5_orders_2(X25)|~l1_orders_2(X25)))&(r1_yellow_0(X25,X29)|(r2_lattice3(X25,X29,esk4_3(X25,X26,X29))|~r2_lattice3(X25,X29,X26))|~m1_subset_1(X26,u1_struct_0(X25))|(~v5_orders_2(X25)|~l1_orders_2(X25))))&((X26=k1_yellow_0(X25,X29)|(~r1_orders_2(X25,X26,esk4_3(X25,X26,X29))|~r2_lattice3(X25,X29,X26))|~m1_subset_1(X26,u1_struct_0(X25))|(~v5_orders_2(X25)|~l1_orders_2(X25)))&(r1_yellow_0(X25,X29)|(~r1_orders_2(X25,X26,esk4_3(X25,X26,X29))|~r2_lattice3(X25,X29,X26))|~m1_subset_1(X26,u1_struct_0(X25))|(~v5_orders_2(X25)|~l1_orders_2(X25))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_yellow_0])])])])])])).
% 0.13/0.40  fof(c_0_25, plain, ![X23, X24]:(~l1_orders_2(X23)|m1_subset_1(k1_yellow_0(X23,X24),u1_struct_0(X23))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_yellow_0])])).
% 0.13/0.40  cnf(c_0_26, plain, (r2_hidden(X1,X2)|~v13_waybel_0(X2,X3)|~r1_orders_2(X3,X4,X1)|~l1_orders_2(X3)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~m1_subset_1(X1,u1_struct_0(X3))|~r2_hidden(X4,X2)), inference(csr,[status(thm)],[c_0_19, c_0_20])).
% 0.13/0.40  cnf(c_0_27, negated_conjecture, (u1_struct_0(esk7_0)=esk8_0|m1_subset_1(esk2_2(u1_struct_0(esk7_0),esk8_0),u1_struct_0(esk7_0))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.13/0.40  cnf(c_0_28, negated_conjecture, (l1_orders_2(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.40  cnf(c_0_29, plain, (X1=X2|~r2_hidden(esk2_2(X1,X2),X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.40  cnf(c_0_30, negated_conjecture, (r2_hidden(k3_yellow_0(esk7_0),esk8_0)|~v1_subset_1(esk8_0,u1_struct_0(esk7_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.40  cnf(c_0_31, negated_conjecture, (u1_struct_0(esk7_0)=esk8_0|v1_subset_1(esk8_0,u1_struct_0(esk7_0))), inference(spm,[status(thm)],[c_0_23, c_0_22])).
% 0.13/0.40  fof(c_0_32, plain, ![X22]:(~l1_orders_2(X22)|k3_yellow_0(X22)=k1_yellow_0(X22,k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_yellow_0])])).
% 0.13/0.40  cnf(c_0_33, plain, (r1_orders_2(X2,X4,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~r2_lattice3(X2,X3,X1)|X4!=k1_yellow_0(X2,X3)|~r1_yellow_0(X2,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.40  cnf(c_0_34, plain, (m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.40  fof(c_0_35, plain, ![X31]:((r1_yellow_0(X31,k1_xboole_0)|(v2_struct_0(X31)|~v5_orders_2(X31)|~v1_yellow_0(X31)|~l1_orders_2(X31)))&(r2_yellow_0(X31,u1_struct_0(X31))|(v2_struct_0(X31)|~v5_orders_2(X31)|~v1_yellow_0(X31)|~l1_orders_2(X31)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t42_yellow_0])])])])).
% 0.13/0.40  cnf(c_0_36, negated_conjecture, (u1_struct_0(esk7_0)=esk8_0|r2_hidden(esk2_2(u1_struct_0(esk7_0),esk8_0),X1)|~v13_waybel_0(X1,esk7_0)|~r1_orders_2(esk7_0,X2,esk2_2(u1_struct_0(esk7_0),esk8_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk7_0)))|~r2_hidden(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28])])).
% 0.13/0.40  cnf(c_0_37, negated_conjecture, (v13_waybel_0(esk8_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.40  cnf(c_0_38, negated_conjecture, (u1_struct_0(esk7_0)=esk8_0|~r2_hidden(esk2_2(u1_struct_0(esk7_0),esk8_0),esk8_0)), inference(spm,[status(thm)],[c_0_29, c_0_22])).
% 0.13/0.40  cnf(c_0_39, negated_conjecture, (u1_struct_0(esk7_0)=esk8_0|r2_hidden(k3_yellow_0(esk7_0),esk8_0)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.13/0.40  cnf(c_0_40, plain, (k3_yellow_0(X1)=k1_yellow_0(X1,k1_xboole_0)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.13/0.40  fof(c_0_41, plain, ![X17, X18, X19, X20]:((~r2_lattice3(X17,X18,X19)|(~m1_subset_1(X20,u1_struct_0(X17))|(~r2_hidden(X20,X18)|r1_orders_2(X17,X20,X19)))|~m1_subset_1(X19,u1_struct_0(X17))|~l1_orders_2(X17))&((m1_subset_1(esk3_3(X17,X18,X19),u1_struct_0(X17))|r2_lattice3(X17,X18,X19)|~m1_subset_1(X19,u1_struct_0(X17))|~l1_orders_2(X17))&((r2_hidden(esk3_3(X17,X18,X19),X18)|r2_lattice3(X17,X18,X19)|~m1_subset_1(X19,u1_struct_0(X17))|~l1_orders_2(X17))&(~r1_orders_2(X17,esk3_3(X17,X18,X19),X19)|r2_lattice3(X17,X18,X19)|~m1_subset_1(X19,u1_struct_0(X17))|~l1_orders_2(X17))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).
% 0.13/0.40  cnf(c_0_42, plain, (r1_orders_2(X1,k1_yellow_0(X1,X2),X3)|~r1_yellow_0(X1,X2)|~v5_orders_2(X1)|~r2_lattice3(X1,X2,X3)|~l1_orders_2(X1)|~m1_subset_1(X3,u1_struct_0(X1))), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_33]), c_0_34])).
% 0.13/0.40  cnf(c_0_43, negated_conjecture, (v5_orders_2(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.40  cnf(c_0_44, negated_conjecture, (~v2_struct_0(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.40  cnf(c_0_45, plain, (r1_yellow_0(X1,k1_xboole_0)|v2_struct_0(X1)|~v5_orders_2(X1)|~v1_yellow_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.40  cnf(c_0_46, negated_conjecture, (v1_yellow_0(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.40  cnf(c_0_47, negated_conjecture, (u1_struct_0(esk7_0)=esk8_0|~r1_orders_2(esk7_0,X1,esk2_2(u1_struct_0(esk7_0),esk8_0))|~r2_hidden(X1,esk8_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_22])]), c_0_38])).
% 0.13/0.40  cnf(c_0_48, negated_conjecture, (u1_struct_0(esk7_0)=esk8_0|r2_hidden(k1_yellow_0(esk7_0,k1_xboole_0),esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_28])])).
% 0.13/0.40  fof(c_0_49, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.13/0.40  cnf(c_0_50, plain, (r2_hidden(esk3_3(X1,X2,X3),X2)|r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.13/0.40  cnf(c_0_51, negated_conjecture, (u1_struct_0(esk7_0)=esk8_0|r1_orders_2(esk7_0,k1_yellow_0(esk7_0,X1),esk2_2(u1_struct_0(esk7_0),esk8_0))|~r1_yellow_0(esk7_0,X1)|~r2_lattice3(esk7_0,X1,esk2_2(u1_struct_0(esk7_0),esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_27]), c_0_43]), c_0_28])])).
% 0.13/0.40  cnf(c_0_52, negated_conjecture, (r1_yellow_0(esk7_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46]), c_0_43]), c_0_28])])).
% 0.13/0.40  cnf(c_0_53, negated_conjecture, (u1_struct_0(esk7_0)=esk8_0|~r1_orders_2(esk7_0,k1_yellow_0(esk7_0,k1_xboole_0),esk2_2(u1_struct_0(esk7_0),esk8_0))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.13/0.40  cnf(c_0_54, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.13/0.40  cnf(c_0_55, negated_conjecture, (u1_struct_0(esk7_0)=esk8_0|r2_lattice3(esk7_0,X1,esk2_2(u1_struct_0(esk7_0),esk8_0))|r2_hidden(esk3_3(esk7_0,X1,esk2_2(u1_struct_0(esk7_0),esk8_0)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_27]), c_0_28])])).
% 0.13/0.40  cnf(c_0_56, negated_conjecture, (u1_struct_0(esk7_0)=esk8_0|~r2_lattice3(esk7_0,k1_xboole_0,esk2_2(u1_struct_0(esk7_0),esk8_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53])).
% 0.13/0.40  cnf(c_0_57, negated_conjecture, (u1_struct_0(esk7_0)=esk8_0|r2_lattice3(esk7_0,X1,esk2_2(u1_struct_0(esk7_0),esk8_0))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.13/0.40  cnf(c_0_58, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.13/0.40  cnf(c_0_59, plain, (~v1_subset_1(X1,X2)|X1!=X2|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.40  cnf(c_0_60, negated_conjecture, (u1_struct_0(esk7_0)=esk8_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_58])])).
% 0.13/0.40  cnf(c_0_61, plain, (~v1_subset_1(X1,X1)|~m1_subset_1(X1,k1_zfmisc_1(X1))), inference(er,[status(thm)],[c_0_59])).
% 0.13/0.40  cnf(c_0_62, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(esk8_0))), inference(rw,[status(thm)],[c_0_22, c_0_60])).
% 0.13/0.40  fof(c_0_63, plain, ![X12, X13]:(~m1_subset_1(X12,X13)|(v1_xboole_0(X13)|r2_hidden(X12,X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.13/0.40  cnf(c_0_64, negated_conjecture, (v1_subset_1(esk8_0,u1_struct_0(esk7_0))|~r2_hidden(k3_yellow_0(esk7_0),esk8_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.40  cnf(c_0_65, negated_conjecture, (~v1_subset_1(esk8_0,esk8_0)), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.13/0.40  cnf(c_0_66, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.13/0.40  cnf(c_0_67, negated_conjecture, (~r2_hidden(k3_yellow_0(esk7_0),esk8_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_64, c_0_60]), c_0_65])).
% 0.13/0.40  cnf(c_0_68, plain, (r2_hidden(k1_yellow_0(X1,X2),u1_struct_0(X1))|v1_xboole_0(u1_struct_0(X1))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_66, c_0_34])).
% 0.13/0.40  cnf(c_0_69, negated_conjecture, (~v1_xboole_0(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.40  cnf(c_0_70, negated_conjecture, (~r2_hidden(k1_yellow_0(esk7_0,k1_xboole_0),esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_40]), c_0_28])])).
% 0.13/0.40  cnf(c_0_71, negated_conjecture, (r2_hidden(k1_yellow_0(esk7_0,X1),esk8_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_60]), c_0_28])]), c_0_69])).
% 0.13/0.40  cnf(c_0_72, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_71])]), ['proof']).
% 0.13/0.40  # SZS output end CNFRefutation
% 0.13/0.40  # Proof object total steps             : 73
% 0.13/0.40  # Proof object clause steps            : 47
% 0.13/0.40  # Proof object formula steps           : 26
% 0.13/0.40  # Proof object conjectures             : 32
% 0.13/0.40  # Proof object clause conjectures      : 29
% 0.13/0.40  # Proof object formula conjectures     : 3
% 0.13/0.40  # Proof object initial clauses used    : 23
% 0.13/0.40  # Proof object initial formulas used   : 13
% 0.13/0.40  # Proof object generating inferences   : 18
% 0.13/0.40  # Proof object simplifying inferences  : 33
% 0.13/0.40  # Training examples: 0 positive, 0 negative
% 0.13/0.40  # Parsed axioms                        : 13
% 0.13/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.40  # Initial clauses                      : 43
% 0.13/0.40  # Removed in clause preprocessing      : 0
% 0.13/0.40  # Initial clauses in saturation        : 43
% 0.13/0.40  # Processed clauses                    : 244
% 0.13/0.40  # ...of these trivial                  : 0
% 0.13/0.40  # ...subsumed                          : 55
% 0.13/0.40  # ...remaining for further processing  : 189
% 0.13/0.40  # Other redundant clauses eliminated   : 3
% 0.13/0.40  # Clauses deleted for lack of memory   : 0
% 0.13/0.40  # Backward-subsumed                    : 6
% 0.13/0.40  # Backward-rewritten                   : 101
% 0.13/0.40  # Generated clauses                    : 452
% 0.13/0.40  # ...of the previous two non-trivial   : 441
% 0.13/0.40  # Contextual simplify-reflections      : 9
% 0.13/0.40  # Paramodulations                      : 449
% 0.13/0.40  # Factorizations                       : 0
% 0.13/0.40  # Equation resolutions                 : 3
% 0.13/0.40  # Propositional unsat checks           : 0
% 0.13/0.40  #    Propositional check models        : 0
% 0.13/0.40  #    Propositional check unsatisfiable : 0
% 0.13/0.40  #    Propositional clauses             : 0
% 0.13/0.40  #    Propositional clauses after purity: 0
% 0.13/0.40  #    Propositional unsat core size     : 0
% 0.13/0.40  #    Propositional preprocessing time  : 0.000
% 0.13/0.40  #    Propositional encoding time       : 0.000
% 0.13/0.40  #    Propositional solver time         : 0.000
% 0.13/0.40  #    Success case prop preproc time    : 0.000
% 0.13/0.40  #    Success case prop encoding time   : 0.000
% 0.13/0.40  #    Success case prop solver time     : 0.000
% 0.13/0.40  # Current number of processed clauses  : 79
% 0.13/0.40  #    Positive orientable unit clauses  : 18
% 0.13/0.40  #    Positive unorientable unit clauses: 0
% 0.13/0.40  #    Negative unit clauses             : 4
% 0.13/0.40  #    Non-unit-clauses                  : 57
% 0.13/0.40  # Current number of unprocessed clauses: 180
% 0.13/0.40  # ...number of literals in the above   : 861
% 0.13/0.40  # Current number of archived formulas  : 0
% 0.13/0.40  # Current number of archived clauses   : 107
% 0.13/0.40  # Clause-clause subsumption calls (NU) : 2390
% 0.13/0.40  # Rec. Clause-clause subsumption calls : 811
% 0.13/0.40  # Non-unit clause-clause subsumptions  : 63
% 0.13/0.40  # Unit Clause-clause subsumption calls : 119
% 0.13/0.40  # Rewrite failures with RHS unbound    : 0
% 0.13/0.40  # BW rewrite match attempts            : 11
% 0.13/0.40  # BW rewrite match successes           : 5
% 0.13/0.40  # Condensation attempts                : 246
% 0.13/0.40  # Condensation successes               : 0
% 0.13/0.40  # Termbank termtop insertions          : 15252
% 0.13/0.40  
% 0.13/0.40  # -------------------------------------------------
% 0.13/0.40  # User time                : 0.051 s
% 0.13/0.40  # System time              : 0.005 s
% 0.13/0.40  # Total time               : 0.056 s
% 0.13/0.40  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
