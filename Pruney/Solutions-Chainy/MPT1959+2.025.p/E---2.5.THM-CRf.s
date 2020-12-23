%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:26 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 396 expanded)
%              Number of clauses        :   54 ( 144 expanded)
%              Number of leaves         :   16 ( 101 expanded)
%              Depth                    :   13
%              Number of atoms          :  340 (2913 expanded)
%              Number of equality atoms :   20 (  64 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   28 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(t34_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2,X3] :
          ( ( r1_tarski(X2,X3)
            & r1_yellow_0(X1,X2)
            & r1_yellow_0(X1,X3) )
         => r1_orders_2(X1,k1_yellow_0(X1,X2),k1_yellow_0(X1,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_yellow_0)).

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

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

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

fof(rc2_subset_1,axiom,(
    ! [X1] :
    ? [X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
      & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_subset_1)).

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

fof(c_0_16,plain,(
    ! [X24,X25,X26] :
      ( ~ r2_hidden(X24,X25)
      | ~ m1_subset_1(X25,k1_zfmisc_1(X26))
      | ~ v1_xboole_0(X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_17,plain,(
    ! [X16] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X16)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

fof(c_0_18,plain,(
    ! [X30,X31,X32] :
      ( ~ l1_orders_2(X30)
      | ~ r1_tarski(X31,X32)
      | ~ r1_yellow_0(X30,X31)
      | ~ r1_yellow_0(X30,X32)
      | r1_orders_2(X30,k1_yellow_0(X30,X31),k1_yellow_0(X30,X32)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_yellow_0])])])).

fof(c_0_19,plain,(
    ! [X40,X41] :
      ( ( r1_yellow_0(X40,k5_waybel_0(X40,X41))
        | ~ m1_subset_1(X41,u1_struct_0(X40))
        | v2_struct_0(X40)
        | ~ v3_orders_2(X40)
        | ~ v4_orders_2(X40)
        | ~ v5_orders_2(X40)
        | ~ l1_orders_2(X40) )
      & ( k1_yellow_0(X40,k5_waybel_0(X40,X41)) = X41
        | ~ m1_subset_1(X41,u1_struct_0(X40))
        | v2_struct_0(X40)
        | ~ v3_orders_2(X40)
        | ~ v4_orders_2(X40)
        | ~ v5_orders_2(X40)
        | ~ l1_orders_2(X40) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_waybel_0])])])])])).

fof(c_0_20,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_21,plain,(
    ! [X34,X35,X36,X37] :
      ( ( ~ v13_waybel_0(X35,X34)
        | ~ m1_subset_1(X36,u1_struct_0(X34))
        | ~ m1_subset_1(X37,u1_struct_0(X34))
        | ~ r2_hidden(X36,X35)
        | ~ r1_orders_2(X34,X36,X37)
        | r2_hidden(X37,X35)
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))
        | ~ l1_orders_2(X34) )
      & ( m1_subset_1(esk5_2(X34,X35),u1_struct_0(X34))
        | v13_waybel_0(X35,X34)
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))
        | ~ l1_orders_2(X34) )
      & ( m1_subset_1(esk6_2(X34,X35),u1_struct_0(X34))
        | v13_waybel_0(X35,X34)
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))
        | ~ l1_orders_2(X34) )
      & ( r2_hidden(esk5_2(X34,X35),X35)
        | v13_waybel_0(X35,X34)
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))
        | ~ l1_orders_2(X34) )
      & ( r1_orders_2(X34,esk5_2(X34,X35),esk6_2(X34,X35))
        | v13_waybel_0(X35,X34)
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))
        | ~ l1_orders_2(X34) )
      & ( ~ r2_hidden(esk6_2(X34,X35),X35)
        | v13_waybel_0(X35,X34)
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))
        | ~ l1_orders_2(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d20_waybel_0])])])])])).

fof(c_0_22,plain,(
    ! [X21,X22,X23] :
      ( ~ r2_hidden(X21,X22)
      | ~ m1_subset_1(X22,k1_zfmisc_1(X23))
      | m1_subset_1(X21,X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_23,negated_conjecture,(
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

cnf(c_0_24,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( r1_orders_2(X1,k1_yellow_0(X1,X2),k1_yellow_0(X1,X3))
    | ~ l1_orders_2(X1)
    | ~ r1_tarski(X2,X3)
    | ~ r1_yellow_0(X1,X2)
    | ~ r1_yellow_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( k1_yellow_0(X1,k5_waybel_0(X1,X2)) = X2
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( r1_yellow_0(X1,k5_waybel_0(X1,X2))
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,plain,
    ( r2_hidden(X4,X1)
    | ~ v13_waybel_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r2_hidden(X3,X1)
    | ~ r1_orders_2(X2,X3,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_33,plain,(
    ! [X28,X29] :
      ( ~ l1_orders_2(X28)
      | m1_subset_1(k1_yellow_0(X28,X29),u1_struct_0(X28)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_yellow_0])])).

fof(c_0_34,negated_conjecture,
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
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_23])])])])).

fof(c_0_35,plain,(
    ! [X27] :
      ( ~ l1_orders_2(X27)
      | k3_yellow_0(X27) = k1_yellow_0(X27,k1_xboole_0) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_yellow_0])])).

fof(c_0_36,plain,(
    ! [X33] :
      ( ( r1_yellow_0(X33,k1_xboole_0)
        | v2_struct_0(X33)
        | ~ v5_orders_2(X33)
        | ~ v1_yellow_0(X33)
        | ~ l1_orders_2(X33) )
      & ( r2_yellow_0(X33,u1_struct_0(X33))
        | v2_struct_0(X33)
        | ~ v5_orders_2(X33)
        | ~ v1_yellow_0(X33)
        | ~ l1_orders_2(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t42_yellow_0])])])])).

cnf(c_0_37,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

fof(c_0_38,plain,(
    ! [X11] :
      ( m1_subset_1(esk2_1(X11),k1_zfmisc_1(X11))
      & v1_xboole_0(esk2_1(X11)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc2_subset_1])])).

cnf(c_0_39,plain,
    ( v2_struct_0(X1)
    | r1_orders_2(X1,k1_yellow_0(X1,X2),X3)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ r1_yellow_0(X1,X2)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_tarski(X2,k5_waybel_0(X1,X3)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,X2)
    | ~ v13_waybel_0(X2,X3)
    | ~ r1_orders_2(X3,X4,X1)
    | ~ l1_orders_2(X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ r2_hidden(X4,X2) ),
    inference(csr,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_42,plain,
    ( m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(k3_yellow_0(esk7_0),esk8_0)
    | ~ v1_subset_1(esk8_0,u1_struct_0(esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_44,plain,
    ( k3_yellow_0(X1) = k1_yellow_0(X1,k1_xboole_0)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_45,negated_conjecture,
    ( l1_orders_2(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_46,plain,
    ( r1_yellow_0(X1,k1_xboole_0)
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_yellow_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_47,negated_conjecture,
    ( v1_yellow_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_48,negated_conjecture,
    ( v5_orders_2(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_49,negated_conjecture,
    ( ~ v2_struct_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_50,plain,
    ( r1_tarski(k1_xboole_0,X1)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_37,c_0_30])).

cnf(c_0_51,plain,
    ( v1_xboole_0(esk2_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_52,plain,
    ( v2_struct_0(X1)
    | r1_orders_2(X1,k1_yellow_0(X1,k5_waybel_0(X1,X2)),X2)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_28])).

cnf(c_0_53,plain,
    ( r2_hidden(k1_yellow_0(X1,X2),X3)
    | ~ v13_waybel_0(X3,X1)
    | ~ r1_yellow_0(X1,X2)
    | ~ r1_yellow_0(X1,X4)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(k1_yellow_0(X1,X4),X3)
    | ~ r1_tarski(X4,X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_26]),c_0_42])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(k1_yellow_0(esk7_0,k1_xboole_0),esk8_0)
    | ~ v1_subset_1(esk8_0,u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45])])).

cnf(c_0_55,negated_conjecture,
    ( v13_waybel_0(esk8_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_56,negated_conjecture,
    ( r1_yellow_0(esk7_0,k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48]),c_0_45])]),c_0_49])).

cnf(c_0_57,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_58,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_59,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,X3)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ v13_waybel_0(X3,X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(k1_yellow_0(X1,k5_waybel_0(X1,X2)),X3) ),
    inference(spm,[status(thm)],[c_0_41,c_0_52])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(k1_yellow_0(esk7_0,X1),esk8_0)
    | ~ r1_yellow_0(esk7_0,X1)
    | ~ v1_subset_1(esk8_0,u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55]),c_0_56]),c_0_45]),c_0_57])]),c_0_58])])).

cnf(c_0_61,negated_conjecture,
    ( v4_orders_2(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_62,negated_conjecture,
    ( v3_orders_2(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(X1,esk8_0)
    | ~ r1_yellow_0(esk7_0,k5_waybel_0(esk7_0,X1))
    | ~ v1_subset_1(esk8_0,u1_struct_0(esk7_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61]),c_0_62]),c_0_55]),c_0_48]),c_0_45]),c_0_57])]),c_0_49])).

fof(c_0_64,plain,(
    ! [X42,X43] :
      ( ( ~ v1_subset_1(X43,X42)
        | X43 != X42
        | ~ m1_subset_1(X43,k1_zfmisc_1(X42)) )
      & ( X43 = X42
        | v1_subset_1(X43,X42)
        | ~ m1_subset_1(X43,k1_zfmisc_1(X42)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).

fof(c_0_65,plain,(
    ! [X13,X14] :
      ( ( m1_subset_1(esk3_2(X13,X14),X13)
        | X13 = X14
        | ~ m1_subset_1(X14,k1_zfmisc_1(X13)) )
      & ( ~ r2_hidden(esk3_2(X13,X14),X14)
        | X13 = X14
        | ~ m1_subset_1(X14,k1_zfmisc_1(X13)) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t49_subset_1])])])])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(X1,esk8_0)
    | ~ v1_subset_1(esk8_0,u1_struct_0(esk7_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_28]),c_0_61]),c_0_62]),c_0_48]),c_0_45])]),c_0_49])).

cnf(c_0_67,plain,
    ( X1 = X2
    | v1_subset_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

fof(c_0_68,plain,(
    ! [X17] :
      ( m1_subset_1(esk4_1(X17),k1_zfmisc_1(X17))
      & ~ v1_subset_1(esk4_1(X17),X17) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[rc3_subset_1])])])).

cnf(c_0_69,plain,
    ( X1 = X2
    | ~ r2_hidden(esk3_2(X1,X2),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_70,negated_conjecture,
    ( u1_struct_0(esk7_0) = esk8_0
    | r2_hidden(X1,esk8_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_57])])).

cnf(c_0_71,plain,
    ( ~ v1_subset_1(esk4_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_72,plain,
    ( m1_subset_1(esk4_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

fof(c_0_73,plain,(
    ! [X19,X20] :
      ( ~ m1_subset_1(X19,X20)
      | v1_xboole_0(X20)
      | r2_hidden(X19,X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_74,negated_conjecture,
    ( v1_subset_1(esk8_0,u1_struct_0(esk7_0))
    | ~ r2_hidden(k3_yellow_0(esk7_0),esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_75,negated_conjecture,
    ( u1_struct_0(esk7_0) = esk8_0
    | X1 = esk8_0
    | ~ m1_subset_1(esk3_2(X1,esk8_0),u1_struct_0(esk7_0))
    | ~ m1_subset_1(esk8_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_76,plain,
    ( m1_subset_1(esk3_2(X1,X2),X1)
    | X1 = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_77,plain,
    ( esk4_1(X1) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_67]),c_0_72])])).

cnf(c_0_78,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_79,negated_conjecture,
    ( v1_subset_1(esk8_0,u1_struct_0(esk7_0))
    | ~ r2_hidden(k1_yellow_0(esk7_0,k1_xboole_0),esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_44]),c_0_45])])).

cnf(c_0_80,negated_conjecture,
    ( u1_struct_0(esk7_0) = esk8_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_57])])).

cnf(c_0_81,plain,
    ( ~ v1_subset_1(X1,X1) ),
    inference(rw,[status(thm)],[c_0_71,c_0_77])).

cnf(c_0_82,plain,
    ( v1_xboole_0(u1_struct_0(X1))
    | r2_hidden(k1_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_78,c_0_42])).

cnf(c_0_83,negated_conjecture,
    ( ~ v1_xboole_0(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_84,negated_conjecture,
    ( ~ r2_hidden(k1_yellow_0(esk7_0,k1_xboole_0),esk8_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_80]),c_0_81])).

cnf(c_0_85,negated_conjecture,
    ( r2_hidden(k1_yellow_0(esk7_0,X1),esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_80]),c_0_45])]),c_0_83])).

cnf(c_0_86,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_84,c_0_85])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:16:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.46  # AutoSched0-Mode selected heuristic G_E___301_C18_F1_URBAN_S5PRR_RG_S0Y
% 0.20/0.46  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.46  #
% 0.20/0.46  # Preprocessing time       : 0.029 s
% 0.20/0.46  
% 0.20/0.46  # Proof found!
% 0.20/0.46  # SZS status Theorem
% 0.20/0.46  # SZS output start CNFRefutation
% 0.20/0.46  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 0.20/0.46  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 0.20/0.46  fof(t34_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(((r1_tarski(X2,X3)&r1_yellow_0(X1,X2))&r1_yellow_0(X1,X3))=>r1_orders_2(X1,k1_yellow_0(X1,X2),k1_yellow_0(X1,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_yellow_0)).
% 0.20/0.46  fof(t34_waybel_0, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(r1_yellow_0(X1,k5_waybel_0(X1,X2))&k1_yellow_0(X1,k5_waybel_0(X1,X2))=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_waybel_0)).
% 0.20/0.46  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.46  fof(d20_waybel_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v13_waybel_0(X2,X1)<=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((r2_hidden(X3,X2)&r1_orders_2(X1,X3,X4))=>r2_hidden(X4,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d20_waybel_0)).
% 0.20/0.46  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 0.20/0.46  fof(t8_waybel_7, conjecture, ![X1]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&v1_yellow_0(X1))&l1_orders_2(X1))=>![X2]:((((~(v1_xboole_0(X2))&v2_waybel_0(X2,X1))&v13_waybel_0(X2,X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v1_subset_1(X2,u1_struct_0(X1))<=>~(r2_hidden(k3_yellow_0(X1),X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_waybel_7)).
% 0.20/0.46  fof(dt_k1_yellow_0, axiom, ![X1, X2]:(l1_orders_2(X1)=>m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_yellow_0)).
% 0.20/0.46  fof(d11_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>k3_yellow_0(X1)=k1_yellow_0(X1,k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_yellow_0)).
% 0.20/0.46  fof(t42_yellow_0, axiom, ![X1]:((((~(v2_struct_0(X1))&v5_orders_2(X1))&v1_yellow_0(X1))&l1_orders_2(X1))=>(r1_yellow_0(X1,k1_xboole_0)&r2_yellow_0(X1,u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_yellow_0)).
% 0.20/0.46  fof(rc2_subset_1, axiom, ![X1]:?[X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))&v1_xboole_0(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc2_subset_1)).
% 0.20/0.46  fof(d7_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(v1_subset_1(X2,X1)<=>X2!=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 0.20/0.46  fof(t49_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(![X3]:(m1_subset_1(X3,X1)=>r2_hidden(X3,X2))=>X1=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_subset_1)).
% 0.20/0.46  fof(rc3_subset_1, axiom, ![X1]:?[X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))&~(v1_subset_1(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc3_subset_1)).
% 0.20/0.46  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 0.20/0.46  fof(c_0_16, plain, ![X24, X25, X26]:(~r2_hidden(X24,X25)|~m1_subset_1(X25,k1_zfmisc_1(X26))|~v1_xboole_0(X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.20/0.46  fof(c_0_17, plain, ![X16]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X16)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.20/0.46  fof(c_0_18, plain, ![X30, X31, X32]:(~l1_orders_2(X30)|(~r1_tarski(X31,X32)|~r1_yellow_0(X30,X31)|~r1_yellow_0(X30,X32)|r1_orders_2(X30,k1_yellow_0(X30,X31),k1_yellow_0(X30,X32)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_yellow_0])])])).
% 0.20/0.46  fof(c_0_19, plain, ![X40, X41]:((r1_yellow_0(X40,k5_waybel_0(X40,X41))|~m1_subset_1(X41,u1_struct_0(X40))|(v2_struct_0(X40)|~v3_orders_2(X40)|~v4_orders_2(X40)|~v5_orders_2(X40)|~l1_orders_2(X40)))&(k1_yellow_0(X40,k5_waybel_0(X40,X41))=X41|~m1_subset_1(X41,u1_struct_0(X40))|(v2_struct_0(X40)|~v3_orders_2(X40)|~v4_orders_2(X40)|~v5_orders_2(X40)|~l1_orders_2(X40)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_waybel_0])])])])])).
% 0.20/0.46  fof(c_0_20, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.46  fof(c_0_21, plain, ![X34, X35, X36, X37]:((~v13_waybel_0(X35,X34)|(~m1_subset_1(X36,u1_struct_0(X34))|(~m1_subset_1(X37,u1_struct_0(X34))|(~r2_hidden(X36,X35)|~r1_orders_2(X34,X36,X37)|r2_hidden(X37,X35))))|~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))|~l1_orders_2(X34))&((m1_subset_1(esk5_2(X34,X35),u1_struct_0(X34))|v13_waybel_0(X35,X34)|~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))|~l1_orders_2(X34))&((m1_subset_1(esk6_2(X34,X35),u1_struct_0(X34))|v13_waybel_0(X35,X34)|~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))|~l1_orders_2(X34))&(((r2_hidden(esk5_2(X34,X35),X35)|v13_waybel_0(X35,X34)|~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))|~l1_orders_2(X34))&(r1_orders_2(X34,esk5_2(X34,X35),esk6_2(X34,X35))|v13_waybel_0(X35,X34)|~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))|~l1_orders_2(X34)))&(~r2_hidden(esk6_2(X34,X35),X35)|v13_waybel_0(X35,X34)|~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))|~l1_orders_2(X34)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d20_waybel_0])])])])])).
% 0.20/0.46  fof(c_0_22, plain, ![X21, X22, X23]:(~r2_hidden(X21,X22)|~m1_subset_1(X22,k1_zfmisc_1(X23))|m1_subset_1(X21,X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.20/0.46  fof(c_0_23, negated_conjecture, ~(![X1]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&v1_yellow_0(X1))&l1_orders_2(X1))=>![X2]:((((~(v1_xboole_0(X2))&v2_waybel_0(X2,X1))&v13_waybel_0(X2,X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v1_subset_1(X2,u1_struct_0(X1))<=>~(r2_hidden(k3_yellow_0(X1),X2)))))), inference(assume_negation,[status(cth)],[t8_waybel_7])).
% 0.20/0.46  cnf(c_0_24, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.46  cnf(c_0_25, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.46  cnf(c_0_26, plain, (r1_orders_2(X1,k1_yellow_0(X1,X2),k1_yellow_0(X1,X3))|~l1_orders_2(X1)|~r1_tarski(X2,X3)|~r1_yellow_0(X1,X2)|~r1_yellow_0(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.46  cnf(c_0_27, plain, (k1_yellow_0(X1,k5_waybel_0(X1,X2))=X2|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.46  cnf(c_0_28, plain, (r1_yellow_0(X1,k5_waybel_0(X1,X2))|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.46  cnf(c_0_29, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.46  cnf(c_0_30, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.46  cnf(c_0_31, plain, (r2_hidden(X4,X1)|~v13_waybel_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X2))|~m1_subset_1(X4,u1_struct_0(X2))|~r2_hidden(X3,X1)|~r1_orders_2(X2,X3,X4)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.46  cnf(c_0_32, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.46  fof(c_0_33, plain, ![X28, X29]:(~l1_orders_2(X28)|m1_subset_1(k1_yellow_0(X28,X29),u1_struct_0(X28))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_yellow_0])])).
% 0.20/0.46  fof(c_0_34, negated_conjecture, ((((((~v2_struct_0(esk7_0)&v3_orders_2(esk7_0))&v4_orders_2(esk7_0))&v5_orders_2(esk7_0))&v1_yellow_0(esk7_0))&l1_orders_2(esk7_0))&((((~v1_xboole_0(esk8_0)&v2_waybel_0(esk8_0,esk7_0))&v13_waybel_0(esk8_0,esk7_0))&m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(esk7_0))))&((~v1_subset_1(esk8_0,u1_struct_0(esk7_0))|r2_hidden(k3_yellow_0(esk7_0),esk8_0))&(v1_subset_1(esk8_0,u1_struct_0(esk7_0))|~r2_hidden(k3_yellow_0(esk7_0),esk8_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_23])])])])).
% 0.20/0.46  fof(c_0_35, plain, ![X27]:(~l1_orders_2(X27)|k3_yellow_0(X27)=k1_yellow_0(X27,k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_yellow_0])])).
% 0.20/0.46  fof(c_0_36, plain, ![X33]:((r1_yellow_0(X33,k1_xboole_0)|(v2_struct_0(X33)|~v5_orders_2(X33)|~v1_yellow_0(X33)|~l1_orders_2(X33)))&(r2_yellow_0(X33,u1_struct_0(X33))|(v2_struct_0(X33)|~v5_orders_2(X33)|~v1_yellow_0(X33)|~l1_orders_2(X33)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t42_yellow_0])])])])).
% 0.20/0.46  cnf(c_0_37, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.20/0.46  fof(c_0_38, plain, ![X11]:(m1_subset_1(esk2_1(X11),k1_zfmisc_1(X11))&v1_xboole_0(esk2_1(X11))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc2_subset_1])])).
% 0.20/0.46  cnf(c_0_39, plain, (v2_struct_0(X1)|r1_orders_2(X1,k1_yellow_0(X1,X2),X3)|~v4_orders_2(X1)|~v3_orders_2(X1)|~v5_orders_2(X1)|~r1_yellow_0(X1,X2)|~l1_orders_2(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~r1_tarski(X2,k5_waybel_0(X1,X3))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28])).
% 0.20/0.46  cnf(c_0_40, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.20/0.46  cnf(c_0_41, plain, (r2_hidden(X1,X2)|~v13_waybel_0(X2,X3)|~r1_orders_2(X3,X4,X1)|~l1_orders_2(X3)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~m1_subset_1(X1,u1_struct_0(X3))|~r2_hidden(X4,X2)), inference(csr,[status(thm)],[c_0_31, c_0_32])).
% 0.20/0.46  cnf(c_0_42, plain, (m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.46  cnf(c_0_43, negated_conjecture, (r2_hidden(k3_yellow_0(esk7_0),esk8_0)|~v1_subset_1(esk8_0,u1_struct_0(esk7_0))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.46  cnf(c_0_44, plain, (k3_yellow_0(X1)=k1_yellow_0(X1,k1_xboole_0)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.46  cnf(c_0_45, negated_conjecture, (l1_orders_2(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.46  cnf(c_0_46, plain, (r1_yellow_0(X1,k1_xboole_0)|v2_struct_0(X1)|~v5_orders_2(X1)|~v1_yellow_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.46  cnf(c_0_47, negated_conjecture, (v1_yellow_0(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.46  cnf(c_0_48, negated_conjecture, (v5_orders_2(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.46  cnf(c_0_49, negated_conjecture, (~v2_struct_0(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.46  cnf(c_0_50, plain, (r1_tarski(k1_xboole_0,X1)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_37, c_0_30])).
% 0.20/0.46  cnf(c_0_51, plain, (v1_xboole_0(esk2_1(X1))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.46  cnf(c_0_52, plain, (v2_struct_0(X1)|r1_orders_2(X1,k1_yellow_0(X1,k5_waybel_0(X1,X2)),X2)|~v4_orders_2(X1)|~v3_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_28])).
% 0.20/0.46  cnf(c_0_53, plain, (r2_hidden(k1_yellow_0(X1,X2),X3)|~v13_waybel_0(X3,X1)|~r1_yellow_0(X1,X2)|~r1_yellow_0(X1,X4)|~l1_orders_2(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(k1_yellow_0(X1,X4),X3)|~r1_tarski(X4,X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_26]), c_0_42])).
% 0.20/0.46  cnf(c_0_54, negated_conjecture, (r2_hidden(k1_yellow_0(esk7_0,k1_xboole_0),esk8_0)|~v1_subset_1(esk8_0,u1_struct_0(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45])])).
% 0.20/0.46  cnf(c_0_55, negated_conjecture, (v13_waybel_0(esk8_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.46  cnf(c_0_56, negated_conjecture, (r1_yellow_0(esk7_0,k1_xboole_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48]), c_0_45])]), c_0_49])).
% 0.20/0.46  cnf(c_0_57, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(esk7_0)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.46  cnf(c_0_58, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.20/0.46  cnf(c_0_59, plain, (v2_struct_0(X1)|r2_hidden(X2,X3)|~v4_orders_2(X1)|~v3_orders_2(X1)|~v13_waybel_0(X3,X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,u1_struct_0(X1))|~r2_hidden(k1_yellow_0(X1,k5_waybel_0(X1,X2)),X3)), inference(spm,[status(thm)],[c_0_41, c_0_52])).
% 0.20/0.46  cnf(c_0_60, negated_conjecture, (r2_hidden(k1_yellow_0(esk7_0,X1),esk8_0)|~r1_yellow_0(esk7_0,X1)|~v1_subset_1(esk8_0,u1_struct_0(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55]), c_0_56]), c_0_45]), c_0_57])]), c_0_58])])).
% 0.20/0.46  cnf(c_0_61, negated_conjecture, (v4_orders_2(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.46  cnf(c_0_62, negated_conjecture, (v3_orders_2(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.46  cnf(c_0_63, negated_conjecture, (r2_hidden(X1,esk8_0)|~r1_yellow_0(esk7_0,k5_waybel_0(esk7_0,X1))|~v1_subset_1(esk8_0,u1_struct_0(esk7_0))|~m1_subset_1(X1,u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_61]), c_0_62]), c_0_55]), c_0_48]), c_0_45]), c_0_57])]), c_0_49])).
% 0.20/0.46  fof(c_0_64, plain, ![X42, X43]:((~v1_subset_1(X43,X42)|X43!=X42|~m1_subset_1(X43,k1_zfmisc_1(X42)))&(X43=X42|v1_subset_1(X43,X42)|~m1_subset_1(X43,k1_zfmisc_1(X42)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).
% 0.20/0.46  fof(c_0_65, plain, ![X13, X14]:((m1_subset_1(esk3_2(X13,X14),X13)|X13=X14|~m1_subset_1(X14,k1_zfmisc_1(X13)))&(~r2_hidden(esk3_2(X13,X14),X14)|X13=X14|~m1_subset_1(X14,k1_zfmisc_1(X13)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t49_subset_1])])])])).
% 0.20/0.46  cnf(c_0_66, negated_conjecture, (r2_hidden(X1,esk8_0)|~v1_subset_1(esk8_0,u1_struct_0(esk7_0))|~m1_subset_1(X1,u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_28]), c_0_61]), c_0_62]), c_0_48]), c_0_45])]), c_0_49])).
% 0.20/0.46  cnf(c_0_67, plain, (X1=X2|v1_subset_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.20/0.46  fof(c_0_68, plain, ![X17]:(m1_subset_1(esk4_1(X17),k1_zfmisc_1(X17))&~v1_subset_1(esk4_1(X17),X17)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[rc3_subset_1])])])).
% 0.20/0.46  cnf(c_0_69, plain, (X1=X2|~r2_hidden(esk3_2(X1,X2),X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.20/0.46  cnf(c_0_70, negated_conjecture, (u1_struct_0(esk7_0)=esk8_0|r2_hidden(X1,esk8_0)|~m1_subset_1(X1,u1_struct_0(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_57])])).
% 0.20/0.46  cnf(c_0_71, plain, (~v1_subset_1(esk4_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.20/0.46  cnf(c_0_72, plain, (m1_subset_1(esk4_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.20/0.46  fof(c_0_73, plain, ![X19, X20]:(~m1_subset_1(X19,X20)|(v1_xboole_0(X20)|r2_hidden(X19,X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.20/0.46  cnf(c_0_74, negated_conjecture, (v1_subset_1(esk8_0,u1_struct_0(esk7_0))|~r2_hidden(k3_yellow_0(esk7_0),esk8_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.46  cnf(c_0_75, negated_conjecture, (u1_struct_0(esk7_0)=esk8_0|X1=esk8_0|~m1_subset_1(esk3_2(X1,esk8_0),u1_struct_0(esk7_0))|~m1_subset_1(esk8_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.20/0.46  cnf(c_0_76, plain, (m1_subset_1(esk3_2(X1,X2),X1)|X1=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.20/0.46  cnf(c_0_77, plain, (esk4_1(X1)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_67]), c_0_72])])).
% 0.20/0.46  cnf(c_0_78, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.20/0.46  cnf(c_0_79, negated_conjecture, (v1_subset_1(esk8_0,u1_struct_0(esk7_0))|~r2_hidden(k1_yellow_0(esk7_0,k1_xboole_0),esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_44]), c_0_45])])).
% 0.20/0.46  cnf(c_0_80, negated_conjecture, (u1_struct_0(esk7_0)=esk8_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_57])])).
% 0.20/0.46  cnf(c_0_81, plain, (~v1_subset_1(X1,X1)), inference(rw,[status(thm)],[c_0_71, c_0_77])).
% 0.20/0.46  cnf(c_0_82, plain, (v1_xboole_0(u1_struct_0(X1))|r2_hidden(k1_yellow_0(X1,X2),u1_struct_0(X1))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_78, c_0_42])).
% 0.20/0.46  cnf(c_0_83, negated_conjecture, (~v1_xboole_0(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.46  cnf(c_0_84, negated_conjecture, (~r2_hidden(k1_yellow_0(esk7_0,k1_xboole_0),esk8_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_79, c_0_80]), c_0_81])).
% 0.20/0.46  cnf(c_0_85, negated_conjecture, (r2_hidden(k1_yellow_0(esk7_0,X1),esk8_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_80]), c_0_45])]), c_0_83])).
% 0.20/0.46  cnf(c_0_86, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_84, c_0_85])]), ['proof']).
% 0.20/0.46  # SZS output end CNFRefutation
% 0.20/0.46  # Proof object total steps             : 87
% 0.20/0.46  # Proof object clause steps            : 54
% 0.20/0.46  # Proof object formula steps           : 33
% 0.20/0.46  # Proof object conjectures             : 26
% 0.20/0.46  # Proof object clause conjectures      : 23
% 0.20/0.46  # Proof object formula conjectures     : 3
% 0.20/0.46  # Proof object initial clauses used    : 30
% 0.20/0.46  # Proof object initial formulas used   : 16
% 0.20/0.46  # Proof object generating inferences   : 20
% 0.20/0.46  # Proof object simplifying inferences  : 47
% 0.20/0.46  # Training examples: 0 positive, 0 negative
% 0.20/0.46  # Parsed axioms                        : 16
% 0.20/0.46  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.46  # Initial clauses                      : 40
% 0.20/0.46  # Removed in clause preprocessing      : 0
% 0.20/0.46  # Initial clauses in saturation        : 40
% 0.20/0.46  # Processed clauses                    : 370
% 0.20/0.46  # ...of these trivial                  : 0
% 0.20/0.46  # ...subsumed                          : 96
% 0.20/0.46  # ...remaining for further processing  : 274
% 0.20/0.46  # Other redundant clauses eliminated   : 1
% 0.20/0.46  # Clauses deleted for lack of memory   : 0
% 0.20/0.46  # Backward-subsumed                    : 33
% 0.20/0.46  # Backward-rewritten                   : 81
% 0.20/0.46  # Generated clauses                    : 1111
% 0.20/0.46  # ...of the previous two non-trivial   : 1026
% 0.20/0.46  # Contextual simplify-reflections      : 36
% 0.20/0.46  # Paramodulations                      : 1110
% 0.20/0.46  # Factorizations                       : 0
% 0.20/0.46  # Equation resolutions                 : 1
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
% 0.20/0.46  # Current number of processed clauses  : 159
% 0.20/0.46  #    Positive orientable unit clauses  : 24
% 0.20/0.46  #    Positive unorientable unit clauses: 0
% 0.20/0.46  #    Negative unit clauses             : 4
% 0.20/0.46  #    Non-unit-clauses                  : 131
% 0.20/0.46  # Current number of unprocessed clauses: 603
% 0.20/0.46  # ...number of literals in the above   : 5095
% 0.20/0.46  # Current number of archived formulas  : 0
% 0.20/0.46  # Current number of archived clauses   : 114
% 0.20/0.46  # Clause-clause subsumption calls (NU) : 19105
% 0.20/0.46  # Rec. Clause-clause subsumption calls : 2362
% 0.20/0.46  # Non-unit clause-clause subsumptions  : 142
% 0.20/0.46  # Unit Clause-clause subsumption calls : 210
% 0.20/0.46  # Rewrite failures with RHS unbound    : 0
% 0.20/0.46  # BW rewrite match attempts            : 30
% 0.20/0.46  # BW rewrite match successes           : 12
% 0.20/0.46  # Condensation attempts                : 0
% 0.20/0.46  # Condensation successes               : 0
% 0.20/0.46  # Termbank termtop insertions          : 40301
% 0.20/0.46  
% 0.20/0.46  # -------------------------------------------------
% 0.20/0.46  # User time                : 0.104 s
% 0.20/0.46  # System time              : 0.009 s
% 0.20/0.46  # Total time               : 0.113 s
% 0.20/0.46  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
