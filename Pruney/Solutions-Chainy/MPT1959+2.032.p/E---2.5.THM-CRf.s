%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:27 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 742 expanded)
%              Number of clauses        :   61 ( 311 expanded)
%              Number of leaves         :   17 ( 185 expanded)
%              Depth                    :   13
%              Number of atoms          :  373 (4095 expanded)
%              Number of equality atoms :   43 ( 276 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   30 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d7_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( v1_subset_1(X2,X1)
      <=> X2 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

fof(rc3_subset_1,axiom,(
    ! [X1] :
    ? [X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
      & ~ v1_subset_1(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_subset_1)).

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

fof(t8_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( ! [X4] :
                ( m1_subset_1(X4,X1)
               => ( r2_hidden(X4,X2)
                <=> r2_hidden(X4,X3) ) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_subset_1)).

fof(dt_k1_yellow_0,axiom,(
    ! [X1,X2] :
      ( l1_orders_2(X1)
     => m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_yellow_0)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(d9_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2,X3] :
          ( m1_subset_1(X3,u1_struct_0(X1))
         => ( r1_yellow_0(X1,X2)
           => ( X3 = k1_yellow_0(X1,X2)
            <=> ( r2_lattice3(X1,X2,X3)
                & ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( r2_lattice3(X1,X2,X4)
                     => r1_orders_2(X1,X3,X4) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_yellow_0)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

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

fof(t42_yellow_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v5_orders_2(X1)
        & v1_yellow_0(X1)
        & l1_orders_2(X1) )
     => ( r1_yellow_0(X1,k1_xboole_0)
        & r2_yellow_0(X1,u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_yellow_0)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(d11_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => k3_yellow_0(X1) = k1_yellow_0(X1,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_yellow_0)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(c_0_17,plain,(
    ! [X47,X48] :
      ( ( ~ v1_subset_1(X48,X47)
        | X48 != X47
        | ~ m1_subset_1(X48,k1_zfmisc_1(X47)) )
      & ( X48 = X47
        | v1_subset_1(X48,X47)
        | ~ m1_subset_1(X48,k1_zfmisc_1(X47)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).

fof(c_0_18,plain,(
    ! [X13] :
      ( m1_subset_1(esk2_1(X13),k1_zfmisc_1(X13))
      & ~ v1_subset_1(esk2_1(X13),X13) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[rc3_subset_1])])])).

cnf(c_0_19,plain,
    ( X1 = X2
    | v1_subset_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_20,plain,
    ( m1_subset_1(esk2_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_21,plain,
    ( ~ v1_subset_1(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_22,negated_conjecture,(
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

fof(c_0_23,plain,(
    ! [X9,X10,X11] :
      ( ( m1_subset_1(esk1_3(X9,X10,X11),X9)
        | X10 = X11
        | ~ m1_subset_1(X11,k1_zfmisc_1(X9))
        | ~ m1_subset_1(X10,k1_zfmisc_1(X9)) )
      & ( ~ r2_hidden(esk1_3(X9,X10,X11),X10)
        | ~ r2_hidden(esk1_3(X9,X10,X11),X11)
        | X10 = X11
        | ~ m1_subset_1(X11,k1_zfmisc_1(X9))
        | ~ m1_subset_1(X10,k1_zfmisc_1(X9)) )
      & ( r2_hidden(esk1_3(X9,X10,X11),X10)
        | r2_hidden(esk1_3(X9,X10,X11),X11)
        | X10 = X11
        | ~ m1_subset_1(X11,k1_zfmisc_1(X9))
        | ~ m1_subset_1(X10,k1_zfmisc_1(X9)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_subset_1])])])])])).

cnf(c_0_24,plain,
    ( esk2_1(X1) = X1 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])).

fof(c_0_25,plain,(
    ! [X37,X38] :
      ( ~ l1_orders_2(X37)
      | m1_subset_1(k1_yellow_0(X37,X38),u1_struct_0(X37)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_yellow_0])])).

fof(c_0_26,negated_conjecture,
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
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_22])])])])).

fof(c_0_27,plain,(
    ! [X19,X20] :
      ( ( ~ m1_subset_1(X19,k1_zfmisc_1(X20))
        | r1_tarski(X19,X20) )
      & ( ~ r1_tarski(X19,X20)
        | m1_subset_1(X19,k1_zfmisc_1(X20)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_28,plain,(
    ! [X8] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X8)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_29,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),X1)
    | X2 = X3
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_20,c_0_24])).

fof(c_0_31,plain,(
    ! [X5,X6,X7] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(X5))
      | ~ r2_hidden(X7,X6)
      | r2_hidden(X7,X5) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

fof(c_0_32,plain,(
    ! [X32,X33,X34,X35] :
      ( ( r2_lattice3(X32,X33,X34)
        | X34 != k1_yellow_0(X32,X33)
        | ~ r1_yellow_0(X32,X33)
        | ~ m1_subset_1(X34,u1_struct_0(X32))
        | ~ l1_orders_2(X32) )
      & ( ~ m1_subset_1(X35,u1_struct_0(X32))
        | ~ r2_lattice3(X32,X33,X35)
        | r1_orders_2(X32,X34,X35)
        | X34 != k1_yellow_0(X32,X33)
        | ~ r1_yellow_0(X32,X33)
        | ~ m1_subset_1(X34,u1_struct_0(X32))
        | ~ l1_orders_2(X32) )
      & ( m1_subset_1(esk4_3(X32,X33,X34),u1_struct_0(X32))
        | ~ r2_lattice3(X32,X33,X34)
        | X34 = k1_yellow_0(X32,X33)
        | ~ r1_yellow_0(X32,X33)
        | ~ m1_subset_1(X34,u1_struct_0(X32))
        | ~ l1_orders_2(X32) )
      & ( r2_lattice3(X32,X33,esk4_3(X32,X33,X34))
        | ~ r2_lattice3(X32,X33,X34)
        | X34 = k1_yellow_0(X32,X33)
        | ~ r1_yellow_0(X32,X33)
        | ~ m1_subset_1(X34,u1_struct_0(X32))
        | ~ l1_orders_2(X32) )
      & ( ~ r1_orders_2(X32,X34,esk4_3(X32,X33,X34))
        | ~ r2_lattice3(X32,X33,X34)
        | X34 = k1_yellow_0(X32,X33)
        | ~ r1_yellow_0(X32,X33)
        | ~ m1_subset_1(X34,u1_struct_0(X32))
        | ~ l1_orders_2(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_yellow_0])])])])])).

cnf(c_0_33,plain,
    ( m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,negated_conjecture,
    ( l1_orders_2(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_35,plain,(
    ! [X24,X25] :
      ( ~ r2_hidden(X24,X25)
      | ~ r1_tarski(X25,X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_38,plain,(
    ! [X26,X27,X28,X29] :
      ( ( ~ r2_lattice3(X26,X27,X28)
        | ~ m1_subset_1(X29,u1_struct_0(X26))
        | ~ r2_hidden(X29,X27)
        | r1_orders_2(X26,X29,X28)
        | ~ m1_subset_1(X28,u1_struct_0(X26))
        | ~ l1_orders_2(X26) )
      & ( m1_subset_1(esk3_3(X26,X27,X28),u1_struct_0(X26))
        | r2_lattice3(X26,X27,X28)
        | ~ m1_subset_1(X28,u1_struct_0(X26))
        | ~ l1_orders_2(X26) )
      & ( r2_hidden(esk3_3(X26,X27,X28),X27)
        | r2_lattice3(X26,X27,X28)
        | ~ m1_subset_1(X28,u1_struct_0(X26))
        | ~ l1_orders_2(X26) )
      & ( ~ r1_orders_2(X26,esk3_3(X26,X27,X28),X28)
        | r2_lattice3(X26,X27,X28)
        | ~ m1_subset_1(X28,u1_struct_0(X26))
        | ~ l1_orders_2(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).

cnf(c_0_39,plain,
    ( X1 = X2
    | m1_subset_1(esk1_3(X2,X1,X2),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_41,plain,(
    ! [X41,X42,X43,X44] :
      ( ( ~ v13_waybel_0(X42,X41)
        | ~ m1_subset_1(X43,u1_struct_0(X41))
        | ~ m1_subset_1(X44,u1_struct_0(X41))
        | ~ r2_hidden(X43,X42)
        | ~ r1_orders_2(X41,X43,X44)
        | r2_hidden(X44,X42)
        | ~ m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41)))
        | ~ l1_orders_2(X41) )
      & ( m1_subset_1(esk5_2(X41,X42),u1_struct_0(X41))
        | v13_waybel_0(X42,X41)
        | ~ m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41)))
        | ~ l1_orders_2(X41) )
      & ( m1_subset_1(esk6_2(X41,X42),u1_struct_0(X41))
        | v13_waybel_0(X42,X41)
        | ~ m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41)))
        | ~ l1_orders_2(X41) )
      & ( r2_hidden(esk5_2(X41,X42),X42)
        | v13_waybel_0(X42,X41)
        | ~ m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41)))
        | ~ l1_orders_2(X41) )
      & ( r1_orders_2(X41,esk5_2(X41,X42),esk6_2(X41,X42))
        | v13_waybel_0(X42,X41)
        | ~ m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41)))
        | ~ l1_orders_2(X41) )
      & ( ~ r2_hidden(esk6_2(X41,X42),X42)
        | v13_waybel_0(X42,X41)
        | ~ m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41)))
        | ~ l1_orders_2(X41) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d20_waybel_0])])])])])).

fof(c_0_42,plain,(
    ! [X21,X22,X23] :
      ( ~ r2_hidden(X21,X22)
      | ~ m1_subset_1(X22,k1_zfmisc_1(X23))
      | m1_subset_1(X21,X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_43,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X2 = X3
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_44,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_45,plain,
    ( r1_orders_2(X2,X4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X1)
    | X4 != k1_yellow_0(X2,X3)
    | ~ r1_yellow_0(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(k1_yellow_0(esk7_0,X1),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_47,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_48,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_49,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),X2)
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_50,negated_conjecture,
    ( u1_struct_0(esk7_0) = esk8_0
    | m1_subset_1(esk1_3(u1_struct_0(esk7_0),esk8_0,u1_struct_0(esk7_0)),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

fof(c_0_51,plain,(
    ! [X40] :
      ( ( r1_yellow_0(X40,k1_xboole_0)
        | v2_struct_0(X40)
        | ~ v5_orders_2(X40)
        | ~ v1_yellow_0(X40)
        | ~ l1_orders_2(X40) )
      & ( r2_yellow_0(X40,u1_struct_0(X40))
        | v2_struct_0(X40)
        | ~ v5_orders_2(X40)
        | ~ v1_yellow_0(X40)
        | ~ l1_orders_2(X40) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t42_yellow_0])])])])).

fof(c_0_52,plain,(
    ! [X15,X16] :
      ( ~ r2_hidden(X15,X16)
      | m1_subset_1(X15,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(k3_yellow_0(esk7_0),esk8_0)
    | ~ v1_subset_1(esk8_0,u1_struct_0(esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_54,negated_conjecture,
    ( u1_struct_0(esk7_0) = esk8_0
    | v1_subset_1(esk8_0,u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_40])).

fof(c_0_55,plain,(
    ! [X31] :
      ( ~ l1_orders_2(X31)
      | k3_yellow_0(X31) = k1_yellow_0(X31,k1_xboole_0) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_yellow_0])])).

cnf(c_0_56,plain,
    ( r2_hidden(X4,X1)
    | ~ v13_waybel_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r2_hidden(X3,X1)
    | ~ r1_orders_2(X2,X3,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_57,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_58,plain,
    ( X1 = X2
    | r2_hidden(esk1_3(X2,X1,X2),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_30]),c_0_44])).

cnf(c_0_59,negated_conjecture,
    ( r1_orders_2(esk7_0,k1_yellow_0(esk7_0,X1),X2)
    | k1_yellow_0(esk7_0,X1) != k1_yellow_0(esk7_0,X3)
    | ~ r1_yellow_0(esk7_0,X3)
    | ~ r2_lattice3(esk7_0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_34])])).

cnf(c_0_60,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_61,negated_conjecture,
    ( u1_struct_0(esk7_0) = esk8_0
    | r2_lattice3(esk7_0,X1,esk1_3(u1_struct_0(esk7_0),esk8_0,u1_struct_0(esk7_0)))
    | r2_hidden(esk3_3(esk7_0,X1,esk1_3(u1_struct_0(esk7_0),esk8_0,u1_struct_0(esk7_0))),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_34])])).

cnf(c_0_62,plain,
    ( r1_yellow_0(X1,k1_xboole_0)
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_yellow_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_63,negated_conjecture,
    ( v1_yellow_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_64,negated_conjecture,
    ( v5_orders_2(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_65,negated_conjecture,
    ( ~ v2_struct_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_66,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_67,negated_conjecture,
    ( u1_struct_0(esk7_0) = esk8_0
    | r2_hidden(k3_yellow_0(esk7_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_68,plain,
    ( k3_yellow_0(X1) = k1_yellow_0(X1,k1_xboole_0)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_69,plain,
    ( r2_hidden(X1,X2)
    | ~ v13_waybel_0(X2,X3)
    | ~ r1_orders_2(X3,X4,X1)
    | ~ l1_orders_2(X3)
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X1,u1_struct_0(X3)) ),
    inference(csr,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_70,negated_conjecture,
    ( v13_waybel_0(esk8_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_71,plain,
    ( X2 = X3
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_72,negated_conjecture,
    ( u1_struct_0(esk7_0) = esk8_0
    | r2_hidden(esk1_3(u1_struct_0(esk7_0),esk8_0,u1_struct_0(esk7_0)),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_40])).

cnf(c_0_73,negated_conjecture,
    ( u1_struct_0(esk7_0) = esk8_0
    | r1_orders_2(esk7_0,k1_yellow_0(esk7_0,X1),esk1_3(u1_struct_0(esk7_0),esk8_0,u1_struct_0(esk7_0)))
    | k1_yellow_0(esk7_0,X1) != k1_yellow_0(esk7_0,X2)
    | ~ r1_yellow_0(esk7_0,X2)
    | ~ r2_lattice3(esk7_0,X2,esk1_3(u1_struct_0(esk7_0),esk8_0,u1_struct_0(esk7_0))) ),
    inference(spm,[status(thm)],[c_0_59,c_0_50])).

cnf(c_0_74,negated_conjecture,
    ( u1_struct_0(esk7_0) = esk8_0
    | r2_lattice3(esk7_0,k1_xboole_0,esk1_3(u1_struct_0(esk7_0),esk8_0,u1_struct_0(esk7_0))) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_75,negated_conjecture,
    ( r1_yellow_0(esk7_0,k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64]),c_0_34])]),c_0_65])).

fof(c_0_76,plain,(
    ! [X17,X18] :
      ( ~ m1_subset_1(X17,X18)
      | v1_xboole_0(X18)
      | r2_hidden(X17,X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_77,negated_conjecture,
    ( u1_struct_0(esk7_0) = esk8_0
    | m1_subset_1(k3_yellow_0(esk7_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_78,negated_conjecture,
    ( k3_yellow_0(esk7_0) = k1_yellow_0(esk7_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_34])).

cnf(c_0_79,negated_conjecture,
    ( r2_hidden(X1,esk8_0)
    | ~ r1_orders_2(esk7_0,X2,X1)
    | ~ r2_hidden(X2,esk8_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_40]),c_0_70]),c_0_34])])).

cnf(c_0_80,negated_conjecture,
    ( u1_struct_0(esk7_0) = esk8_0
    | ~ r2_hidden(esk1_3(u1_struct_0(esk7_0),esk8_0,u1_struct_0(esk7_0)),esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_30]),c_0_40])])).

cnf(c_0_81,negated_conjecture,
    ( u1_struct_0(esk7_0) = esk8_0
    | r1_orders_2(esk7_0,k1_yellow_0(esk7_0,X1),esk1_3(u1_struct_0(esk7_0),esk8_0,u1_struct_0(esk7_0)))
    | k1_yellow_0(esk7_0,X1) != k1_yellow_0(esk7_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_75])])).

cnf(c_0_82,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_83,negated_conjecture,
    ( u1_struct_0(esk7_0) = esk8_0
    | m1_subset_1(k1_yellow_0(esk7_0,k1_xboole_0),esk8_0) ),
    inference(rw,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_84,negated_conjecture,
    ( ~ v1_xboole_0(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_85,negated_conjecture,
    ( v1_subset_1(esk8_0,u1_struct_0(esk7_0))
    | ~ r2_hidden(k3_yellow_0(esk7_0),esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_86,negated_conjecture,
    ( u1_struct_0(esk7_0) = esk8_0
    | ~ r1_orders_2(esk7_0,X1,esk1_3(u1_struct_0(esk7_0),esk8_0,u1_struct_0(esk7_0)))
    | ~ r2_hidden(X1,esk8_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_50]),c_0_80])).

cnf(c_0_87,negated_conjecture,
    ( u1_struct_0(esk7_0) = esk8_0
    | r1_orders_2(esk7_0,k1_yellow_0(esk7_0,k1_xboole_0),esk1_3(u1_struct_0(esk7_0),esk8_0,u1_struct_0(esk7_0))) ),
    inference(er,[status(thm)],[c_0_81])).

cnf(c_0_88,negated_conjecture,
    ( u1_struct_0(esk7_0) = esk8_0
    | r2_hidden(k1_yellow_0(esk7_0,k1_xboole_0),esk8_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_84])).

cnf(c_0_89,negated_conjecture,
    ( v1_subset_1(esk8_0,u1_struct_0(esk7_0))
    | ~ r2_hidden(k1_yellow_0(esk7_0,k1_xboole_0),esk8_0) ),
    inference(rw,[status(thm)],[c_0_85,c_0_78])).

cnf(c_0_90,negated_conjecture,
    ( u1_struct_0(esk7_0) = esk8_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_88])).

cnf(c_0_91,plain,
    ( ~ v1_subset_1(X1,X1) ),
    inference(rw,[status(thm)],[c_0_21,c_0_24])).

cnf(c_0_92,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk7_0))
    | r2_hidden(k1_yellow_0(esk7_0,X1),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_82,c_0_46])).

cnf(c_0_93,negated_conjecture,
    ( ~ r2_hidden(k1_yellow_0(esk7_0,k1_xboole_0),esk8_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_89,c_0_90]),c_0_91])).

cnf(c_0_94,negated_conjecture,
    ( r2_hidden(k1_yellow_0(esk7_0,X1),esk8_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_92,c_0_90]),c_0_90]),c_0_84])).

cnf(c_0_95,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_93,c_0_94])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:27:01 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.46  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_PS_S0S
% 0.20/0.46  # and selection function SelectComplexG.
% 0.20/0.46  #
% 0.20/0.46  # Preprocessing time       : 0.029 s
% 0.20/0.46  # Presaturation interreduction done
% 0.20/0.46  
% 0.20/0.46  # Proof found!
% 0.20/0.46  # SZS status Theorem
% 0.20/0.46  # SZS output start CNFRefutation
% 0.20/0.46  fof(d7_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(v1_subset_1(X2,X1)<=>X2!=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 0.20/0.46  fof(rc3_subset_1, axiom, ![X1]:?[X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))&~(v1_subset_1(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc3_subset_1)).
% 0.20/0.46  fof(t8_waybel_7, conjecture, ![X1]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&v1_yellow_0(X1))&l1_orders_2(X1))=>![X2]:((((~(v1_xboole_0(X2))&v2_waybel_0(X2,X1))&v13_waybel_0(X2,X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v1_subset_1(X2,u1_struct_0(X1))<=>~(r2_hidden(k3_yellow_0(X1),X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_waybel_7)).
% 0.20/0.46  fof(t8_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(![X4]:(m1_subset_1(X4,X1)=>(r2_hidden(X4,X2)<=>r2_hidden(X4,X3)))=>X2=X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_subset_1)).
% 0.20/0.46  fof(dt_k1_yellow_0, axiom, ![X1, X2]:(l1_orders_2(X1)=>m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_yellow_0)).
% 0.20/0.46  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.46  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 0.20/0.46  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 0.20/0.46  fof(d9_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_yellow_0(X1,X2)=>(X3=k1_yellow_0(X1,X2)<=>(r2_lattice3(X1,X2,X3)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X4)=>r1_orders_2(X1,X3,X4)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_yellow_0)).
% 0.20/0.46  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.20/0.46  fof(d9_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X2)=>r1_orders_2(X1,X4,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_lattice3)).
% 0.20/0.46  fof(d20_waybel_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v13_waybel_0(X2,X1)<=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((r2_hidden(X3,X2)&r1_orders_2(X1,X3,X4))=>r2_hidden(X4,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d20_waybel_0)).
% 0.20/0.46  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 0.20/0.46  fof(t42_yellow_0, axiom, ![X1]:((((~(v2_struct_0(X1))&v5_orders_2(X1))&v1_yellow_0(X1))&l1_orders_2(X1))=>(r1_yellow_0(X1,k1_xboole_0)&r2_yellow_0(X1,u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_yellow_0)).
% 0.20/0.46  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 0.20/0.46  fof(d11_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>k3_yellow_0(X1)=k1_yellow_0(X1,k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_yellow_0)).
% 0.20/0.46  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 0.20/0.46  fof(c_0_17, plain, ![X47, X48]:((~v1_subset_1(X48,X47)|X48!=X47|~m1_subset_1(X48,k1_zfmisc_1(X47)))&(X48=X47|v1_subset_1(X48,X47)|~m1_subset_1(X48,k1_zfmisc_1(X47)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).
% 0.20/0.46  fof(c_0_18, plain, ![X13]:(m1_subset_1(esk2_1(X13),k1_zfmisc_1(X13))&~v1_subset_1(esk2_1(X13),X13)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[rc3_subset_1])])])).
% 0.20/0.46  cnf(c_0_19, plain, (X1=X2|v1_subset_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.46  cnf(c_0_20, plain, (m1_subset_1(esk2_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.46  cnf(c_0_21, plain, (~v1_subset_1(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.46  fof(c_0_22, negated_conjecture, ~(![X1]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&v1_yellow_0(X1))&l1_orders_2(X1))=>![X2]:((((~(v1_xboole_0(X2))&v2_waybel_0(X2,X1))&v13_waybel_0(X2,X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v1_subset_1(X2,u1_struct_0(X1))<=>~(r2_hidden(k3_yellow_0(X1),X2)))))), inference(assume_negation,[status(cth)],[t8_waybel_7])).
% 0.20/0.46  fof(c_0_23, plain, ![X9, X10, X11]:((m1_subset_1(esk1_3(X9,X10,X11),X9)|X10=X11|~m1_subset_1(X11,k1_zfmisc_1(X9))|~m1_subset_1(X10,k1_zfmisc_1(X9)))&((~r2_hidden(esk1_3(X9,X10,X11),X10)|~r2_hidden(esk1_3(X9,X10,X11),X11)|X10=X11|~m1_subset_1(X11,k1_zfmisc_1(X9))|~m1_subset_1(X10,k1_zfmisc_1(X9)))&(r2_hidden(esk1_3(X9,X10,X11),X10)|r2_hidden(esk1_3(X9,X10,X11),X11)|X10=X11|~m1_subset_1(X11,k1_zfmisc_1(X9))|~m1_subset_1(X10,k1_zfmisc_1(X9))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_subset_1])])])])])).
% 0.20/0.46  cnf(c_0_24, plain, (esk2_1(X1)=X1), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21])).
% 0.20/0.46  fof(c_0_25, plain, ![X37, X38]:(~l1_orders_2(X37)|m1_subset_1(k1_yellow_0(X37,X38),u1_struct_0(X37))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_yellow_0])])).
% 0.20/0.46  fof(c_0_26, negated_conjecture, ((((((~v2_struct_0(esk7_0)&v3_orders_2(esk7_0))&v4_orders_2(esk7_0))&v5_orders_2(esk7_0))&v1_yellow_0(esk7_0))&l1_orders_2(esk7_0))&((((~v1_xboole_0(esk8_0)&v2_waybel_0(esk8_0,esk7_0))&v13_waybel_0(esk8_0,esk7_0))&m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(esk7_0))))&((~v1_subset_1(esk8_0,u1_struct_0(esk7_0))|r2_hidden(k3_yellow_0(esk7_0),esk8_0))&(v1_subset_1(esk8_0,u1_struct_0(esk7_0))|~r2_hidden(k3_yellow_0(esk7_0),esk8_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_22])])])])).
% 0.20/0.46  fof(c_0_27, plain, ![X19, X20]:((~m1_subset_1(X19,k1_zfmisc_1(X20))|r1_tarski(X19,X20))&(~r1_tarski(X19,X20)|m1_subset_1(X19,k1_zfmisc_1(X20)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.46  fof(c_0_28, plain, ![X8]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X8)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.20/0.46  cnf(c_0_29, plain, (m1_subset_1(esk1_3(X1,X2,X3),X1)|X2=X3|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.46  cnf(c_0_30, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_20, c_0_24])).
% 0.20/0.46  fof(c_0_31, plain, ![X5, X6, X7]:(~m1_subset_1(X6,k1_zfmisc_1(X5))|(~r2_hidden(X7,X6)|r2_hidden(X7,X5))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.20/0.46  fof(c_0_32, plain, ![X32, X33, X34, X35]:(((r2_lattice3(X32,X33,X34)|X34!=k1_yellow_0(X32,X33)|~r1_yellow_0(X32,X33)|~m1_subset_1(X34,u1_struct_0(X32))|~l1_orders_2(X32))&(~m1_subset_1(X35,u1_struct_0(X32))|(~r2_lattice3(X32,X33,X35)|r1_orders_2(X32,X34,X35))|X34!=k1_yellow_0(X32,X33)|~r1_yellow_0(X32,X33)|~m1_subset_1(X34,u1_struct_0(X32))|~l1_orders_2(X32)))&((m1_subset_1(esk4_3(X32,X33,X34),u1_struct_0(X32))|~r2_lattice3(X32,X33,X34)|X34=k1_yellow_0(X32,X33)|~r1_yellow_0(X32,X33)|~m1_subset_1(X34,u1_struct_0(X32))|~l1_orders_2(X32))&((r2_lattice3(X32,X33,esk4_3(X32,X33,X34))|~r2_lattice3(X32,X33,X34)|X34=k1_yellow_0(X32,X33)|~r1_yellow_0(X32,X33)|~m1_subset_1(X34,u1_struct_0(X32))|~l1_orders_2(X32))&(~r1_orders_2(X32,X34,esk4_3(X32,X33,X34))|~r2_lattice3(X32,X33,X34)|X34=k1_yellow_0(X32,X33)|~r1_yellow_0(X32,X33)|~m1_subset_1(X34,u1_struct_0(X32))|~l1_orders_2(X32))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_yellow_0])])])])])).
% 0.20/0.46  cnf(c_0_33, plain, (m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.46  cnf(c_0_34, negated_conjecture, (l1_orders_2(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.46  fof(c_0_35, plain, ![X24, X25]:(~r2_hidden(X24,X25)|~r1_tarski(X25,X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.20/0.46  cnf(c_0_36, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.46  cnf(c_0_37, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.46  fof(c_0_38, plain, ![X26, X27, X28, X29]:((~r2_lattice3(X26,X27,X28)|(~m1_subset_1(X29,u1_struct_0(X26))|(~r2_hidden(X29,X27)|r1_orders_2(X26,X29,X28)))|~m1_subset_1(X28,u1_struct_0(X26))|~l1_orders_2(X26))&((m1_subset_1(esk3_3(X26,X27,X28),u1_struct_0(X26))|r2_lattice3(X26,X27,X28)|~m1_subset_1(X28,u1_struct_0(X26))|~l1_orders_2(X26))&((r2_hidden(esk3_3(X26,X27,X28),X27)|r2_lattice3(X26,X27,X28)|~m1_subset_1(X28,u1_struct_0(X26))|~l1_orders_2(X26))&(~r1_orders_2(X26,esk3_3(X26,X27,X28),X28)|r2_lattice3(X26,X27,X28)|~m1_subset_1(X28,u1_struct_0(X26))|~l1_orders_2(X26))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).
% 0.20/0.46  cnf(c_0_39, plain, (X1=X2|m1_subset_1(esk1_3(X2,X1,X2),X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.20/0.46  cnf(c_0_40, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(esk7_0)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.46  fof(c_0_41, plain, ![X41, X42, X43, X44]:((~v13_waybel_0(X42,X41)|(~m1_subset_1(X43,u1_struct_0(X41))|(~m1_subset_1(X44,u1_struct_0(X41))|(~r2_hidden(X43,X42)|~r1_orders_2(X41,X43,X44)|r2_hidden(X44,X42))))|~m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41)))|~l1_orders_2(X41))&((m1_subset_1(esk5_2(X41,X42),u1_struct_0(X41))|v13_waybel_0(X42,X41)|~m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41)))|~l1_orders_2(X41))&((m1_subset_1(esk6_2(X41,X42),u1_struct_0(X41))|v13_waybel_0(X42,X41)|~m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41)))|~l1_orders_2(X41))&(((r2_hidden(esk5_2(X41,X42),X42)|v13_waybel_0(X42,X41)|~m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41)))|~l1_orders_2(X41))&(r1_orders_2(X41,esk5_2(X41,X42),esk6_2(X41,X42))|v13_waybel_0(X42,X41)|~m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41)))|~l1_orders_2(X41)))&(~r2_hidden(esk6_2(X41,X42),X42)|v13_waybel_0(X42,X41)|~m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41)))|~l1_orders_2(X41)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d20_waybel_0])])])])])).
% 0.20/0.46  fof(c_0_42, plain, ![X21, X22, X23]:(~r2_hidden(X21,X22)|~m1_subset_1(X22,k1_zfmisc_1(X23))|m1_subset_1(X21,X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.20/0.46  cnf(c_0_43, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r2_hidden(esk1_3(X1,X2,X3),X3)|X2=X3|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.46  cnf(c_0_44, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.46  cnf(c_0_45, plain, (r1_orders_2(X2,X4,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~r2_lattice3(X2,X3,X1)|X4!=k1_yellow_0(X2,X3)|~r1_yellow_0(X2,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.46  cnf(c_0_46, negated_conjecture, (m1_subset_1(k1_yellow_0(esk7_0,X1),u1_struct_0(esk7_0))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.20/0.46  cnf(c_0_47, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.46  cnf(c_0_48, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.20/0.46  cnf(c_0_49, plain, (r2_hidden(esk3_3(X1,X2,X3),X2)|r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.46  cnf(c_0_50, negated_conjecture, (u1_struct_0(esk7_0)=esk8_0|m1_subset_1(esk1_3(u1_struct_0(esk7_0),esk8_0,u1_struct_0(esk7_0)),u1_struct_0(esk7_0))), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.20/0.46  fof(c_0_51, plain, ![X40]:((r1_yellow_0(X40,k1_xboole_0)|(v2_struct_0(X40)|~v5_orders_2(X40)|~v1_yellow_0(X40)|~l1_orders_2(X40)))&(r2_yellow_0(X40,u1_struct_0(X40))|(v2_struct_0(X40)|~v5_orders_2(X40)|~v1_yellow_0(X40)|~l1_orders_2(X40)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t42_yellow_0])])])])).
% 0.20/0.46  fof(c_0_52, plain, ![X15, X16]:(~r2_hidden(X15,X16)|m1_subset_1(X15,X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.20/0.46  cnf(c_0_53, negated_conjecture, (r2_hidden(k3_yellow_0(esk7_0),esk8_0)|~v1_subset_1(esk8_0,u1_struct_0(esk7_0))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.46  cnf(c_0_54, negated_conjecture, (u1_struct_0(esk7_0)=esk8_0|v1_subset_1(esk8_0,u1_struct_0(esk7_0))), inference(spm,[status(thm)],[c_0_19, c_0_40])).
% 0.20/0.46  fof(c_0_55, plain, ![X31]:(~l1_orders_2(X31)|k3_yellow_0(X31)=k1_yellow_0(X31,k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_yellow_0])])).
% 0.20/0.46  cnf(c_0_56, plain, (r2_hidden(X4,X1)|~v13_waybel_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X2))|~m1_subset_1(X4,u1_struct_0(X2))|~r2_hidden(X3,X1)|~r1_orders_2(X2,X3,X4)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.20/0.46  cnf(c_0_57, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.46  cnf(c_0_58, plain, (X1=X2|r2_hidden(esk1_3(X2,X1,X2),X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_30]), c_0_44])).
% 0.20/0.46  cnf(c_0_59, negated_conjecture, (r1_orders_2(esk7_0,k1_yellow_0(esk7_0,X1),X2)|k1_yellow_0(esk7_0,X1)!=k1_yellow_0(esk7_0,X3)|~r1_yellow_0(esk7_0,X3)|~r2_lattice3(esk7_0,X3,X2)|~m1_subset_1(X2,u1_struct_0(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_34])])).
% 0.20/0.46  cnf(c_0_60, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.20/0.46  cnf(c_0_61, negated_conjecture, (u1_struct_0(esk7_0)=esk8_0|r2_lattice3(esk7_0,X1,esk1_3(u1_struct_0(esk7_0),esk8_0,u1_struct_0(esk7_0)))|r2_hidden(esk3_3(esk7_0,X1,esk1_3(u1_struct_0(esk7_0),esk8_0,u1_struct_0(esk7_0))),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_34])])).
% 0.20/0.46  cnf(c_0_62, plain, (r1_yellow_0(X1,k1_xboole_0)|v2_struct_0(X1)|~v5_orders_2(X1)|~v1_yellow_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.20/0.46  cnf(c_0_63, negated_conjecture, (v1_yellow_0(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.46  cnf(c_0_64, negated_conjecture, (v5_orders_2(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.46  cnf(c_0_65, negated_conjecture, (~v2_struct_0(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.46  cnf(c_0_66, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.20/0.46  cnf(c_0_67, negated_conjecture, (u1_struct_0(esk7_0)=esk8_0|r2_hidden(k3_yellow_0(esk7_0),esk8_0)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.20/0.46  cnf(c_0_68, plain, (k3_yellow_0(X1)=k1_yellow_0(X1,k1_xboole_0)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.20/0.46  cnf(c_0_69, plain, (r2_hidden(X1,X2)|~v13_waybel_0(X2,X3)|~r1_orders_2(X3,X4,X1)|~l1_orders_2(X3)|~r2_hidden(X4,X2)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~m1_subset_1(X1,u1_struct_0(X3))), inference(csr,[status(thm)],[c_0_56, c_0_57])).
% 0.20/0.46  cnf(c_0_70, negated_conjecture, (v13_waybel_0(esk8_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.46  cnf(c_0_71, plain, (X2=X3|~r2_hidden(esk1_3(X1,X2,X3),X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.46  cnf(c_0_72, negated_conjecture, (u1_struct_0(esk7_0)=esk8_0|r2_hidden(esk1_3(u1_struct_0(esk7_0),esk8_0,u1_struct_0(esk7_0)),u1_struct_0(esk7_0))), inference(spm,[status(thm)],[c_0_58, c_0_40])).
% 0.20/0.46  cnf(c_0_73, negated_conjecture, (u1_struct_0(esk7_0)=esk8_0|r1_orders_2(esk7_0,k1_yellow_0(esk7_0,X1),esk1_3(u1_struct_0(esk7_0),esk8_0,u1_struct_0(esk7_0)))|k1_yellow_0(esk7_0,X1)!=k1_yellow_0(esk7_0,X2)|~r1_yellow_0(esk7_0,X2)|~r2_lattice3(esk7_0,X2,esk1_3(u1_struct_0(esk7_0),esk8_0,u1_struct_0(esk7_0)))), inference(spm,[status(thm)],[c_0_59, c_0_50])).
% 0.20/0.46  cnf(c_0_74, negated_conjecture, (u1_struct_0(esk7_0)=esk8_0|r2_lattice3(esk7_0,k1_xboole_0,esk1_3(u1_struct_0(esk7_0),esk8_0,u1_struct_0(esk7_0)))), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.20/0.46  cnf(c_0_75, negated_conjecture, (r1_yellow_0(esk7_0,k1_xboole_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_64]), c_0_34])]), c_0_65])).
% 0.20/0.46  fof(c_0_76, plain, ![X17, X18]:(~m1_subset_1(X17,X18)|(v1_xboole_0(X18)|r2_hidden(X17,X18))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.20/0.46  cnf(c_0_77, negated_conjecture, (u1_struct_0(esk7_0)=esk8_0|m1_subset_1(k3_yellow_0(esk7_0),esk8_0)), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.20/0.46  cnf(c_0_78, negated_conjecture, (k3_yellow_0(esk7_0)=k1_yellow_0(esk7_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_68, c_0_34])).
% 0.20/0.46  cnf(c_0_79, negated_conjecture, (r2_hidden(X1,esk8_0)|~r1_orders_2(esk7_0,X2,X1)|~r2_hidden(X2,esk8_0)|~m1_subset_1(X1,u1_struct_0(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_40]), c_0_70]), c_0_34])])).
% 0.20/0.46  cnf(c_0_80, negated_conjecture, (u1_struct_0(esk7_0)=esk8_0|~r2_hidden(esk1_3(u1_struct_0(esk7_0),esk8_0,u1_struct_0(esk7_0)),esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_30]), c_0_40])])).
% 0.20/0.46  cnf(c_0_81, negated_conjecture, (u1_struct_0(esk7_0)=esk8_0|r1_orders_2(esk7_0,k1_yellow_0(esk7_0,X1),esk1_3(u1_struct_0(esk7_0),esk8_0,u1_struct_0(esk7_0)))|k1_yellow_0(esk7_0,X1)!=k1_yellow_0(esk7_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_75])])).
% 0.20/0.46  cnf(c_0_82, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_76])).
% 0.20/0.46  cnf(c_0_83, negated_conjecture, (u1_struct_0(esk7_0)=esk8_0|m1_subset_1(k1_yellow_0(esk7_0,k1_xboole_0),esk8_0)), inference(rw,[status(thm)],[c_0_77, c_0_78])).
% 0.20/0.46  cnf(c_0_84, negated_conjecture, (~v1_xboole_0(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.46  cnf(c_0_85, negated_conjecture, (v1_subset_1(esk8_0,u1_struct_0(esk7_0))|~r2_hidden(k3_yellow_0(esk7_0),esk8_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.46  cnf(c_0_86, negated_conjecture, (u1_struct_0(esk7_0)=esk8_0|~r1_orders_2(esk7_0,X1,esk1_3(u1_struct_0(esk7_0),esk8_0,u1_struct_0(esk7_0)))|~r2_hidden(X1,esk8_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_50]), c_0_80])).
% 0.20/0.46  cnf(c_0_87, negated_conjecture, (u1_struct_0(esk7_0)=esk8_0|r1_orders_2(esk7_0,k1_yellow_0(esk7_0,k1_xboole_0),esk1_3(u1_struct_0(esk7_0),esk8_0,u1_struct_0(esk7_0)))), inference(er,[status(thm)],[c_0_81])).
% 0.20/0.46  cnf(c_0_88, negated_conjecture, (u1_struct_0(esk7_0)=esk8_0|r2_hidden(k1_yellow_0(esk7_0,k1_xboole_0),esk8_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_84])).
% 0.20/0.46  cnf(c_0_89, negated_conjecture, (v1_subset_1(esk8_0,u1_struct_0(esk7_0))|~r2_hidden(k1_yellow_0(esk7_0,k1_xboole_0),esk8_0)), inference(rw,[status(thm)],[c_0_85, c_0_78])).
% 0.20/0.46  cnf(c_0_90, negated_conjecture, (u1_struct_0(esk7_0)=esk8_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_88])).
% 0.20/0.46  cnf(c_0_91, plain, (~v1_subset_1(X1,X1)), inference(rw,[status(thm)],[c_0_21, c_0_24])).
% 0.20/0.46  cnf(c_0_92, negated_conjecture, (v1_xboole_0(u1_struct_0(esk7_0))|r2_hidden(k1_yellow_0(esk7_0,X1),u1_struct_0(esk7_0))), inference(spm,[status(thm)],[c_0_82, c_0_46])).
% 0.20/0.46  cnf(c_0_93, negated_conjecture, (~r2_hidden(k1_yellow_0(esk7_0,k1_xboole_0),esk8_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_89, c_0_90]), c_0_91])).
% 0.20/0.46  cnf(c_0_94, negated_conjecture, (r2_hidden(k1_yellow_0(esk7_0,X1),esk8_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_92, c_0_90]), c_0_90]), c_0_84])).
% 0.20/0.46  cnf(c_0_95, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_93, c_0_94])]), ['proof']).
% 0.20/0.46  # SZS output end CNFRefutation
% 0.20/0.46  # Proof object total steps             : 96
% 0.20/0.46  # Proof object clause steps            : 61
% 0.20/0.46  # Proof object formula steps           : 35
% 0.20/0.46  # Proof object conjectures             : 37
% 0.20/0.46  # Proof object clause conjectures      : 34
% 0.20/0.46  # Proof object formula conjectures     : 3
% 0.20/0.46  # Proof object initial clauses used    : 28
% 0.20/0.46  # Proof object initial formulas used   : 17
% 0.20/0.46  # Proof object generating inferences   : 25
% 0.20/0.46  # Proof object simplifying inferences  : 33
% 0.20/0.46  # Training examples: 0 positive, 0 negative
% 0.20/0.46  # Parsed axioms                        : 18
% 0.20/0.46  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.46  # Initial clauses                      : 47
% 0.20/0.46  # Removed in clause preprocessing      : 0
% 0.20/0.46  # Initial clauses in saturation        : 47
% 0.20/0.46  # Processed clauses                    : 546
% 0.20/0.46  # ...of these trivial                  : 0
% 0.20/0.46  # ...subsumed                          : 104
% 0.20/0.46  # ...remaining for further processing  : 442
% 0.20/0.46  # Other redundant clauses eliminated   : 1
% 0.20/0.46  # Clauses deleted for lack of memory   : 0
% 0.20/0.46  # Backward-subsumed                    : 21
% 0.20/0.46  # Backward-rewritten                   : 225
% 0.20/0.46  # Generated clauses                    : 1472
% 0.20/0.46  # ...of the previous two non-trivial   : 1555
% 0.20/0.46  # Contextual simplify-reflections      : 9
% 0.20/0.46  # Paramodulations                      : 1465
% 0.20/0.46  # Factorizations                       : 0
% 0.20/0.46  # Equation resolutions                 : 7
% 0.20/0.46  # Propositional unsat checks           : 0
% 0.20/0.46  #    Propositional check models        : 0
% 0.20/0.46  #    Propositional check unsatisfiable : 0
% 0.20/0.46  #    Propositional clauses             : 0
% 0.20/0.46  #    Propositional clauses after purity: 0
% 0.20/0.46  #    Propositional unsat core size     : 0
% 0.20/0.46  #    Propositional preprocessing time  : 0.000
% 0.20/0.46  #    Propositional encoding time       : 0.000
% 0.20/0.46  #    Propositional solver time         : 0.000
% 0.20/0.46  #    Success case prop preproc time    : 0.000
% 0.20/0.46  #    Success case prop encoding time   : 0.000
% 0.20/0.46  #    Success case prop solver time     : 0.000
% 0.20/0.46  # Current number of processed clauses  : 148
% 0.20/0.46  #    Positive orientable unit clauses  : 19
% 0.20/0.46  #    Positive unorientable unit clauses: 0
% 0.20/0.46  #    Negative unit clauses             : 6
% 0.20/0.46  #    Non-unit-clauses                  : 123
% 0.20/0.46  # Current number of unprocessed clauses: 1054
% 0.20/0.46  # ...number of literals in the above   : 5334
% 0.20/0.46  # Current number of archived formulas  : 0
% 0.20/0.46  # Current number of archived clauses   : 293
% 0.20/0.46  # Clause-clause subsumption calls (NU) : 13942
% 0.20/0.46  # Rec. Clause-clause subsumption calls : 3684
% 0.20/0.46  # Non-unit clause-clause subsumptions  : 124
% 0.20/0.46  # Unit Clause-clause subsumption calls : 311
% 0.20/0.46  # Rewrite failures with RHS unbound    : 0
% 0.20/0.46  # BW rewrite match attempts            : 22
% 0.20/0.46  # BW rewrite match successes           : 10
% 0.20/0.46  # Condensation attempts                : 0
% 0.20/0.46  # Condensation successes               : 0
% 0.20/0.46  # Termbank termtop insertions          : 51842
% 0.20/0.46  
% 0.20/0.46  # -------------------------------------------------
% 0.20/0.46  # User time                : 0.103 s
% 0.20/0.46  # System time              : 0.006 s
% 0.20/0.46  # Total time               : 0.109 s
% 0.20/0.46  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
