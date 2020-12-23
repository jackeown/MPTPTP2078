%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:24 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 377 expanded)
%              Number of clauses        :   54 ( 161 expanded)
%              Number of leaves         :   16 (  90 expanded)
%              Depth                    :   12
%              Number of atoms          :  369 (2433 expanded)
%              Number of equality atoms :   41 ( 158 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   30 (   3 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_7)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_subset_1)).

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

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(d7_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( v1_subset_1(X2,X1)
      <=> X2 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_yellow_0)).

fof(dt_k1_yellow_0,axiom,(
    ! [X1,X2] :
      ( l1_orders_2(X1)
     => m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_0)).

fof(d11_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => k3_yellow_0(X1) = k1_yellow_0(X1,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_yellow_0)).

fof(t42_yellow_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v5_orders_2(X1)
        & v1_yellow_0(X1)
        & l1_orders_2(X1) )
     => ( r1_yellow_0(X1,k1_xboole_0)
        & r2_yellow_0(X1,u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_yellow_0)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattice3)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

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
    ! [X9,X10] :
      ( ( r1_tarski(X9,X10)
        | X9 != X10 )
      & ( r1_tarski(X10,X9)
        | X9 != X10 )
      & ( ~ r1_tarski(X9,X10)
        | ~ r1_tarski(X10,X9)
        | X9 = X10 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_18,plain,(
    ! [X14,X15,X16] :
      ( ( m1_subset_1(esk2_3(X14,X15,X16),X14)
        | X15 = X16
        | ~ m1_subset_1(X16,k1_zfmisc_1(X14))
        | ~ m1_subset_1(X15,k1_zfmisc_1(X14)) )
      & ( ~ r2_hidden(esk2_3(X14,X15,X16),X15)
        | ~ r2_hidden(esk2_3(X14,X15,X16),X16)
        | X15 = X16
        | ~ m1_subset_1(X16,k1_zfmisc_1(X14))
        | ~ m1_subset_1(X15,k1_zfmisc_1(X14)) )
      & ( r2_hidden(esk2_3(X14,X15,X16),X15)
        | r2_hidden(esk2_3(X14,X15,X16),X16)
        | X15 = X16
        | ~ m1_subset_1(X16,k1_zfmisc_1(X14))
        | ~ m1_subset_1(X15,k1_zfmisc_1(X14)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_subset_1])])])])])).

fof(c_0_19,negated_conjecture,
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
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])).

fof(c_0_20,plain,(
    ! [X20,X21] :
      ( ( ~ m1_subset_1(X20,k1_zfmisc_1(X21))
        | r1_tarski(X20,X21) )
      & ( ~ r1_tarski(X20,X21)
        | m1_subset_1(X20,k1_zfmisc_1(X21)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_21,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_22,plain,(
    ! [X39,X40,X41,X42] :
      ( ( ~ v13_waybel_0(X40,X39)
        | ~ m1_subset_1(X41,u1_struct_0(X39))
        | ~ m1_subset_1(X42,u1_struct_0(X39))
        | ~ r2_hidden(X41,X40)
        | ~ r1_orders_2(X39,X41,X42)
        | r2_hidden(X42,X40)
        | ~ m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))
        | ~ l1_orders_2(X39) )
      & ( m1_subset_1(esk5_2(X39,X40),u1_struct_0(X39))
        | v13_waybel_0(X40,X39)
        | ~ m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))
        | ~ l1_orders_2(X39) )
      & ( m1_subset_1(esk6_2(X39,X40),u1_struct_0(X39))
        | v13_waybel_0(X40,X39)
        | ~ m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))
        | ~ l1_orders_2(X39) )
      & ( r2_hidden(esk5_2(X39,X40),X40)
        | v13_waybel_0(X40,X39)
        | ~ m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))
        | ~ l1_orders_2(X39) )
      & ( r1_orders_2(X39,esk5_2(X39,X40),esk6_2(X39,X40))
        | v13_waybel_0(X40,X39)
        | ~ m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))
        | ~ l1_orders_2(X39) )
      & ( ~ r2_hidden(esk6_2(X39,X40),X40)
        | v13_waybel_0(X40,X39)
        | ~ m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))
        | ~ l1_orders_2(X39) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d20_waybel_0])])])])])).

fof(c_0_23,plain,(
    ! [X22,X23,X24] :
      ( ~ r2_hidden(X22,X23)
      | ~ m1_subset_1(X23,k1_zfmisc_1(X24))
      | m1_subset_1(X22,X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_24,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),X1)
    | X2 = X3
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_21])).

fof(c_0_28,plain,(
    ! [X11,X12,X13] :
      ( ~ m1_subset_1(X12,k1_zfmisc_1(X11))
      | ~ r2_hidden(X13,X12)
      | r2_hidden(X13,X11) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

fof(c_0_29,plain,(
    ! [X45,X46] :
      ( ( ~ v1_subset_1(X46,X45)
        | X46 != X45
        | ~ m1_subset_1(X46,k1_zfmisc_1(X45)) )
      & ( X46 = X45
        | v1_subset_1(X46,X45)
        | ~ m1_subset_1(X46,k1_zfmisc_1(X45)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).

cnf(c_0_30,plain,
    ( r2_hidden(X4,X1)
    | ~ v13_waybel_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r2_hidden(X3,X1)
    | ~ r1_orders_2(X2,X3,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,negated_conjecture,
    ( X1 = esk8_0
    | m1_subset_1(esk2_3(u1_struct_0(esk7_0),X1,esk8_0),u1_struct_0(esk7_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_33,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_34,plain,
    ( X2 = X3
    | ~ r2_hidden(esk2_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_35,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,plain,
    ( X1 = X2
    | v1_subset_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_37,plain,(
    ! [X31,X32,X33,X34] :
      ( ( r2_lattice3(X31,X32,X33)
        | X33 != k1_yellow_0(X31,X32)
        | ~ r1_yellow_0(X31,X32)
        | ~ m1_subset_1(X33,u1_struct_0(X31))
        | ~ l1_orders_2(X31) )
      & ( ~ m1_subset_1(X34,u1_struct_0(X31))
        | ~ r2_lattice3(X31,X32,X34)
        | r1_orders_2(X31,X33,X34)
        | X33 != k1_yellow_0(X31,X32)
        | ~ r1_yellow_0(X31,X32)
        | ~ m1_subset_1(X33,u1_struct_0(X31))
        | ~ l1_orders_2(X31) )
      & ( m1_subset_1(esk4_3(X31,X32,X33),u1_struct_0(X31))
        | ~ r2_lattice3(X31,X32,X33)
        | X33 = k1_yellow_0(X31,X32)
        | ~ r1_yellow_0(X31,X32)
        | ~ m1_subset_1(X33,u1_struct_0(X31))
        | ~ l1_orders_2(X31) )
      & ( r2_lattice3(X31,X32,esk4_3(X31,X32,X33))
        | ~ r2_lattice3(X31,X32,X33)
        | X33 = k1_yellow_0(X31,X32)
        | ~ r1_yellow_0(X31,X32)
        | ~ m1_subset_1(X33,u1_struct_0(X31))
        | ~ l1_orders_2(X31) )
      & ( ~ r1_orders_2(X31,X33,esk4_3(X31,X32,X33))
        | ~ r2_lattice3(X31,X32,X33)
        | X33 = k1_yellow_0(X31,X32)
        | ~ r1_yellow_0(X31,X32)
        | ~ m1_subset_1(X33,u1_struct_0(X31))
        | ~ l1_orders_2(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_yellow_0])])])])])).

fof(c_0_38,plain,(
    ! [X36,X37] :
      ( ~ l1_orders_2(X36)
      | m1_subset_1(k1_yellow_0(X36,X37),u1_struct_0(X36)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_yellow_0])])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,X2)
    | ~ v13_waybel_0(X2,X3)
    | ~ r1_orders_2(X3,X4,X1)
    | ~ l1_orders_2(X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ r2_hidden(X4,X2) ),
    inference(csr,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_40,negated_conjecture,
    ( u1_struct_0(esk7_0) = esk8_0
    | m1_subset_1(esk2_3(u1_struct_0(esk7_0),u1_struct_0(esk7_0),esk8_0),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_41,negated_conjecture,
    ( l1_orders_2(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_42,negated_conjecture,
    ( X1 = esk8_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk7_0)))
    | ~ r2_hidden(esk2_3(u1_struct_0(esk7_0),X1,esk8_0),esk8_0)
    | ~ r2_hidden(esk2_3(u1_struct_0(esk7_0),X1,esk8_0),X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_25])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(X1,u1_struct_0(esk7_0))
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_25])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(k3_yellow_0(esk7_0),esk8_0)
    | ~ v1_subset_1(esk8_0,u1_struct_0(esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_45,negated_conjecture,
    ( u1_struct_0(esk7_0) = esk8_0
    | v1_subset_1(esk8_0,u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_25])).

fof(c_0_46,plain,(
    ! [X30] :
      ( ~ l1_orders_2(X30)
      | k3_yellow_0(X30) = k1_yellow_0(X30,k1_xboole_0) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_yellow_0])])).

cnf(c_0_47,plain,
    ( r1_orders_2(X2,X4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X1)
    | X4 != k1_yellow_0(X2,X3)
    | ~ r1_yellow_0(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_48,plain,
    ( m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_49,plain,(
    ! [X38] :
      ( ( r1_yellow_0(X38,k1_xboole_0)
        | v2_struct_0(X38)
        | ~ v5_orders_2(X38)
        | ~ v1_yellow_0(X38)
        | ~ l1_orders_2(X38) )
      & ( r2_yellow_0(X38,u1_struct_0(X38))
        | v2_struct_0(X38)
        | ~ v5_orders_2(X38)
        | ~ v1_yellow_0(X38)
        | ~ l1_orders_2(X38) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t42_yellow_0])])])])).

cnf(c_0_50,negated_conjecture,
    ( u1_struct_0(esk7_0) = esk8_0
    | r2_hidden(esk2_3(u1_struct_0(esk7_0),u1_struct_0(esk7_0),esk8_0),X1)
    | ~ v13_waybel_0(X1,esk7_0)
    | ~ r1_orders_2(esk7_0,X2,esk2_3(u1_struct_0(esk7_0),u1_struct_0(esk7_0),esk8_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk7_0)))
    | ~ r2_hidden(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41])])).

cnf(c_0_51,negated_conjecture,
    ( v13_waybel_0(esk8_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_52,negated_conjecture,
    ( u1_struct_0(esk7_0) = esk8_0
    | ~ r2_hidden(esk2_3(u1_struct_0(esk7_0),u1_struct_0(esk7_0),esk8_0),esk8_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_33]),c_0_43])).

cnf(c_0_53,negated_conjecture,
    ( u1_struct_0(esk7_0) = esk8_0
    | r2_hidden(k3_yellow_0(esk7_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_54,plain,
    ( k3_yellow_0(X1) = k1_yellow_0(X1,k1_xboole_0)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

fof(c_0_55,plain,(
    ! [X25,X26,X27,X28] :
      ( ( ~ r2_lattice3(X25,X26,X27)
        | ~ m1_subset_1(X28,u1_struct_0(X25))
        | ~ r2_hidden(X28,X26)
        | r1_orders_2(X25,X28,X27)
        | ~ m1_subset_1(X27,u1_struct_0(X25))
        | ~ l1_orders_2(X25) )
      & ( m1_subset_1(esk3_3(X25,X26,X27),u1_struct_0(X25))
        | r2_lattice3(X25,X26,X27)
        | ~ m1_subset_1(X27,u1_struct_0(X25))
        | ~ l1_orders_2(X25) )
      & ( r2_hidden(esk3_3(X25,X26,X27),X26)
        | r2_lattice3(X25,X26,X27)
        | ~ m1_subset_1(X27,u1_struct_0(X25))
        | ~ l1_orders_2(X25) )
      & ( ~ r1_orders_2(X25,esk3_3(X25,X26,X27),X27)
        | r2_lattice3(X25,X26,X27)
        | ~ m1_subset_1(X27,u1_struct_0(X25))
        | ~ l1_orders_2(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).

cnf(c_0_56,plain,
    ( r1_orders_2(X1,k1_yellow_0(X1,X2),X3)
    | ~ r1_yellow_0(X1,X2)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_47]),c_0_48])).

cnf(c_0_57,negated_conjecture,
    ( ~ v2_struct_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_58,plain,
    ( r1_yellow_0(X1,k1_xboole_0)
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_yellow_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_59,negated_conjecture,
    ( v1_yellow_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_60,negated_conjecture,
    ( v5_orders_2(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_61,negated_conjecture,
    ( u1_struct_0(esk7_0) = esk8_0
    | ~ r1_orders_2(esk7_0,X1,esk2_3(u1_struct_0(esk7_0),u1_struct_0(esk7_0),esk8_0))
    | ~ r2_hidden(X1,esk8_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_25])]),c_0_52])).

cnf(c_0_62,negated_conjecture,
    ( u1_struct_0(esk7_0) = esk8_0
    | r2_hidden(k1_yellow_0(esk7_0,k1_xboole_0),esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_41])])).

fof(c_0_63,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_64,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),X2)
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_65,negated_conjecture,
    ( u1_struct_0(esk7_0) = esk8_0
    | r1_orders_2(esk7_0,k1_yellow_0(esk7_0,X1),esk2_3(u1_struct_0(esk7_0),u1_struct_0(esk7_0),esk8_0))
    | ~ r1_yellow_0(esk7_0,X1)
    | ~ r2_lattice3(esk7_0,X1,esk2_3(u1_struct_0(esk7_0),u1_struct_0(esk7_0),esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_40]),c_0_41])])).

cnf(c_0_66,negated_conjecture,
    ( r1_yellow_0(esk7_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59]),c_0_60]),c_0_41])])).

cnf(c_0_67,negated_conjecture,
    ( u1_struct_0(esk7_0) = esk8_0
    | ~ r1_orders_2(esk7_0,k1_yellow_0(esk7_0,k1_xboole_0),esk2_3(u1_struct_0(esk7_0),u1_struct_0(esk7_0),esk8_0)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_68,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_69,negated_conjecture,
    ( u1_struct_0(esk7_0) = esk8_0
    | r2_lattice3(esk7_0,X1,esk2_3(u1_struct_0(esk7_0),u1_struct_0(esk7_0),esk8_0))
    | r2_hidden(esk3_3(esk7_0,X1,esk2_3(u1_struct_0(esk7_0),u1_struct_0(esk7_0),esk8_0)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_40]),c_0_41])])).

cnf(c_0_70,plain,
    ( ~ v1_subset_1(X1,X2)
    | X1 != X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_71,plain,(
    ! [X18,X19] :
      ( ~ m1_subset_1(X18,X19)
      | v1_xboole_0(X19)
      | r2_hidden(X18,X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_72,negated_conjecture,
    ( v1_subset_1(esk8_0,u1_struct_0(esk7_0))
    | ~ r2_hidden(k3_yellow_0(esk7_0),esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_73,negated_conjecture,
    ( u1_struct_0(esk7_0) = esk8_0
    | ~ r2_lattice3(esk7_0,k1_xboole_0,esk2_3(u1_struct_0(esk7_0),u1_struct_0(esk7_0),esk8_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67])).

cnf(c_0_74,negated_conjecture,
    ( u1_struct_0(esk7_0) = esk8_0
    | r2_lattice3(esk7_0,X1,esk2_3(u1_struct_0(esk7_0),u1_struct_0(esk7_0),esk8_0))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_75,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_76,plain,
    ( ~ v1_subset_1(X1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(er,[status(thm)],[c_0_70])).

cnf(c_0_77,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_78,negated_conjecture,
    ( v1_subset_1(esk8_0,u1_struct_0(esk7_0))
    | ~ r2_hidden(k1_yellow_0(esk7_0,k1_xboole_0),esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_54]),c_0_41])])).

cnf(c_0_79,negated_conjecture,
    ( u1_struct_0(esk7_0) = esk8_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_75])])).

cnf(c_0_80,plain,
    ( ~ v1_subset_1(X1,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_33])])).

cnf(c_0_81,plain,
    ( r2_hidden(k1_yellow_0(X1,X2),u1_struct_0(X1))
    | v1_xboole_0(u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_77,c_0_48])).

cnf(c_0_82,negated_conjecture,
    ( ~ v1_xboole_0(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_83,negated_conjecture,
    ( ~ r2_hidden(k1_yellow_0(esk7_0,k1_xboole_0),esk8_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_79]),c_0_80])).

cnf(c_0_84,negated_conjecture,
    ( r2_hidden(k1_yellow_0(esk7_0,X1),esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_79]),c_0_41])]),c_0_82])).

cnf(c_0_85,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_83,c_0_84])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:37:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.41  # AutoSched0-Mode selected heuristic G_E___008_C18_F1_PI_SE_CS_SP_CO_S4S
% 0.19/0.41  # and selection function SelectNewComplexAHPNS.
% 0.19/0.41  #
% 0.19/0.41  # Preprocessing time       : 0.030 s
% 0.19/0.41  
% 0.19/0.41  # Proof found!
% 0.19/0.41  # SZS status Theorem
% 0.19/0.41  # SZS output start CNFRefutation
% 0.19/0.41  fof(t8_waybel_7, conjecture, ![X1]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&v1_yellow_0(X1))&l1_orders_2(X1))=>![X2]:((((~(v1_xboole_0(X2))&v2_waybel_0(X2,X1))&v13_waybel_0(X2,X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v1_subset_1(X2,u1_struct_0(X1))<=>~(r2_hidden(k3_yellow_0(X1),X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_waybel_7)).
% 0.19/0.41  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.41  fof(t8_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(![X4]:(m1_subset_1(X4,X1)=>(r2_hidden(X4,X2)<=>r2_hidden(X4,X3)))=>X2=X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_subset_1)).
% 0.19/0.41  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.41  fof(d20_waybel_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v13_waybel_0(X2,X1)<=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((r2_hidden(X3,X2)&r1_orders_2(X1,X3,X4))=>r2_hidden(X4,X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d20_waybel_0)).
% 0.19/0.41  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.19/0.41  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 0.19/0.41  fof(d7_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(v1_subset_1(X2,X1)<=>X2!=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 0.19/0.41  fof(d9_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_yellow_0(X1,X2)=>(X3=k1_yellow_0(X1,X2)<=>(r2_lattice3(X1,X2,X3)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X4)=>r1_orders_2(X1,X3,X4)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_yellow_0)).
% 0.19/0.41  fof(dt_k1_yellow_0, axiom, ![X1, X2]:(l1_orders_2(X1)=>m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_yellow_0)).
% 0.19/0.41  fof(d11_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>k3_yellow_0(X1)=k1_yellow_0(X1,k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_yellow_0)).
% 0.19/0.41  fof(t42_yellow_0, axiom, ![X1]:((((~(v2_struct_0(X1))&v5_orders_2(X1))&v1_yellow_0(X1))&l1_orders_2(X1))=>(r1_yellow_0(X1,k1_xboole_0)&r2_yellow_0(X1,u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_yellow_0)).
% 0.19/0.41  fof(d9_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X2)=>r1_orders_2(X1,X4,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_lattice3)).
% 0.19/0.41  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.19/0.41  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 0.19/0.41  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.19/0.41  fof(c_0_16, negated_conjecture, ~(![X1]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&v1_yellow_0(X1))&l1_orders_2(X1))=>![X2]:((((~(v1_xboole_0(X2))&v2_waybel_0(X2,X1))&v13_waybel_0(X2,X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v1_subset_1(X2,u1_struct_0(X1))<=>~(r2_hidden(k3_yellow_0(X1),X2)))))), inference(assume_negation,[status(cth)],[t8_waybel_7])).
% 0.19/0.41  fof(c_0_17, plain, ![X9, X10]:(((r1_tarski(X9,X10)|X9!=X10)&(r1_tarski(X10,X9)|X9!=X10))&(~r1_tarski(X9,X10)|~r1_tarski(X10,X9)|X9=X10)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.41  fof(c_0_18, plain, ![X14, X15, X16]:((m1_subset_1(esk2_3(X14,X15,X16),X14)|X15=X16|~m1_subset_1(X16,k1_zfmisc_1(X14))|~m1_subset_1(X15,k1_zfmisc_1(X14)))&((~r2_hidden(esk2_3(X14,X15,X16),X15)|~r2_hidden(esk2_3(X14,X15,X16),X16)|X15=X16|~m1_subset_1(X16,k1_zfmisc_1(X14))|~m1_subset_1(X15,k1_zfmisc_1(X14)))&(r2_hidden(esk2_3(X14,X15,X16),X15)|r2_hidden(esk2_3(X14,X15,X16),X16)|X15=X16|~m1_subset_1(X16,k1_zfmisc_1(X14))|~m1_subset_1(X15,k1_zfmisc_1(X14))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_subset_1])])])])])).
% 0.19/0.41  fof(c_0_19, negated_conjecture, ((((((~v2_struct_0(esk7_0)&v3_orders_2(esk7_0))&v4_orders_2(esk7_0))&v5_orders_2(esk7_0))&v1_yellow_0(esk7_0))&l1_orders_2(esk7_0))&((((~v1_xboole_0(esk8_0)&v2_waybel_0(esk8_0,esk7_0))&v13_waybel_0(esk8_0,esk7_0))&m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(esk7_0))))&((~v1_subset_1(esk8_0,u1_struct_0(esk7_0))|r2_hidden(k3_yellow_0(esk7_0),esk8_0))&(v1_subset_1(esk8_0,u1_struct_0(esk7_0))|~r2_hidden(k3_yellow_0(esk7_0),esk8_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])).
% 0.19/0.41  fof(c_0_20, plain, ![X20, X21]:((~m1_subset_1(X20,k1_zfmisc_1(X21))|r1_tarski(X20,X21))&(~r1_tarski(X20,X21)|m1_subset_1(X20,k1_zfmisc_1(X21)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.41  cnf(c_0_21, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.41  fof(c_0_22, plain, ![X39, X40, X41, X42]:((~v13_waybel_0(X40,X39)|(~m1_subset_1(X41,u1_struct_0(X39))|(~m1_subset_1(X42,u1_struct_0(X39))|(~r2_hidden(X41,X40)|~r1_orders_2(X39,X41,X42)|r2_hidden(X42,X40))))|~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))|~l1_orders_2(X39))&((m1_subset_1(esk5_2(X39,X40),u1_struct_0(X39))|v13_waybel_0(X40,X39)|~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))|~l1_orders_2(X39))&((m1_subset_1(esk6_2(X39,X40),u1_struct_0(X39))|v13_waybel_0(X40,X39)|~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))|~l1_orders_2(X39))&(((r2_hidden(esk5_2(X39,X40),X40)|v13_waybel_0(X40,X39)|~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))|~l1_orders_2(X39))&(r1_orders_2(X39,esk5_2(X39,X40),esk6_2(X39,X40))|v13_waybel_0(X40,X39)|~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))|~l1_orders_2(X39)))&(~r2_hidden(esk6_2(X39,X40),X40)|v13_waybel_0(X40,X39)|~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))|~l1_orders_2(X39)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d20_waybel_0])])])])])).
% 0.19/0.41  fof(c_0_23, plain, ![X22, X23, X24]:(~r2_hidden(X22,X23)|~m1_subset_1(X23,k1_zfmisc_1(X24))|m1_subset_1(X22,X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.19/0.41  cnf(c_0_24, plain, (m1_subset_1(esk2_3(X1,X2,X3),X1)|X2=X3|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.41  cnf(c_0_25, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(esk7_0)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.41  cnf(c_0_26, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.41  cnf(c_0_27, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_21])).
% 0.19/0.41  fof(c_0_28, plain, ![X11, X12, X13]:(~m1_subset_1(X12,k1_zfmisc_1(X11))|(~r2_hidden(X13,X12)|r2_hidden(X13,X11))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.19/0.41  fof(c_0_29, plain, ![X45, X46]:((~v1_subset_1(X46,X45)|X46!=X45|~m1_subset_1(X46,k1_zfmisc_1(X45)))&(X46=X45|v1_subset_1(X46,X45)|~m1_subset_1(X46,k1_zfmisc_1(X45)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).
% 0.19/0.41  cnf(c_0_30, plain, (r2_hidden(X4,X1)|~v13_waybel_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X2))|~m1_subset_1(X4,u1_struct_0(X2))|~r2_hidden(X3,X1)|~r1_orders_2(X2,X3,X4)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.41  cnf(c_0_31, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.41  cnf(c_0_32, negated_conjecture, (X1=esk8_0|m1_subset_1(esk2_3(u1_struct_0(esk7_0),X1,esk8_0),u1_struct_0(esk7_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk7_0)))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.19/0.41  cnf(c_0_33, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.19/0.41  cnf(c_0_34, plain, (X2=X3|~r2_hidden(esk2_3(X1,X2,X3),X2)|~r2_hidden(esk2_3(X1,X2,X3),X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.41  cnf(c_0_35, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.41  cnf(c_0_36, plain, (X1=X2|v1_subset_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.41  fof(c_0_37, plain, ![X31, X32, X33, X34]:(((r2_lattice3(X31,X32,X33)|X33!=k1_yellow_0(X31,X32)|~r1_yellow_0(X31,X32)|~m1_subset_1(X33,u1_struct_0(X31))|~l1_orders_2(X31))&(~m1_subset_1(X34,u1_struct_0(X31))|(~r2_lattice3(X31,X32,X34)|r1_orders_2(X31,X33,X34))|X33!=k1_yellow_0(X31,X32)|~r1_yellow_0(X31,X32)|~m1_subset_1(X33,u1_struct_0(X31))|~l1_orders_2(X31)))&((m1_subset_1(esk4_3(X31,X32,X33),u1_struct_0(X31))|~r2_lattice3(X31,X32,X33)|X33=k1_yellow_0(X31,X32)|~r1_yellow_0(X31,X32)|~m1_subset_1(X33,u1_struct_0(X31))|~l1_orders_2(X31))&((r2_lattice3(X31,X32,esk4_3(X31,X32,X33))|~r2_lattice3(X31,X32,X33)|X33=k1_yellow_0(X31,X32)|~r1_yellow_0(X31,X32)|~m1_subset_1(X33,u1_struct_0(X31))|~l1_orders_2(X31))&(~r1_orders_2(X31,X33,esk4_3(X31,X32,X33))|~r2_lattice3(X31,X32,X33)|X33=k1_yellow_0(X31,X32)|~r1_yellow_0(X31,X32)|~m1_subset_1(X33,u1_struct_0(X31))|~l1_orders_2(X31))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_yellow_0])])])])])).
% 0.19/0.41  fof(c_0_38, plain, ![X36, X37]:(~l1_orders_2(X36)|m1_subset_1(k1_yellow_0(X36,X37),u1_struct_0(X36))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_yellow_0])])).
% 0.19/0.41  cnf(c_0_39, plain, (r2_hidden(X1,X2)|~v13_waybel_0(X2,X3)|~r1_orders_2(X3,X4,X1)|~l1_orders_2(X3)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~m1_subset_1(X1,u1_struct_0(X3))|~r2_hidden(X4,X2)), inference(csr,[status(thm)],[c_0_30, c_0_31])).
% 0.19/0.41  cnf(c_0_40, negated_conjecture, (u1_struct_0(esk7_0)=esk8_0|m1_subset_1(esk2_3(u1_struct_0(esk7_0),u1_struct_0(esk7_0),esk8_0),u1_struct_0(esk7_0))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.19/0.41  cnf(c_0_41, negated_conjecture, (l1_orders_2(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.41  cnf(c_0_42, negated_conjecture, (X1=esk8_0|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk7_0)))|~r2_hidden(esk2_3(u1_struct_0(esk7_0),X1,esk8_0),esk8_0)|~r2_hidden(esk2_3(u1_struct_0(esk7_0),X1,esk8_0),X1)), inference(spm,[status(thm)],[c_0_34, c_0_25])).
% 0.19/0.41  cnf(c_0_43, negated_conjecture, (r2_hidden(X1,u1_struct_0(esk7_0))|~r2_hidden(X1,esk8_0)), inference(spm,[status(thm)],[c_0_35, c_0_25])).
% 0.19/0.41  cnf(c_0_44, negated_conjecture, (r2_hidden(k3_yellow_0(esk7_0),esk8_0)|~v1_subset_1(esk8_0,u1_struct_0(esk7_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.41  cnf(c_0_45, negated_conjecture, (u1_struct_0(esk7_0)=esk8_0|v1_subset_1(esk8_0,u1_struct_0(esk7_0))), inference(spm,[status(thm)],[c_0_36, c_0_25])).
% 0.19/0.41  fof(c_0_46, plain, ![X30]:(~l1_orders_2(X30)|k3_yellow_0(X30)=k1_yellow_0(X30,k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_yellow_0])])).
% 0.19/0.41  cnf(c_0_47, plain, (r1_orders_2(X2,X4,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~r2_lattice3(X2,X3,X1)|X4!=k1_yellow_0(X2,X3)|~r1_yellow_0(X2,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.41  cnf(c_0_48, plain, (m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.41  fof(c_0_49, plain, ![X38]:((r1_yellow_0(X38,k1_xboole_0)|(v2_struct_0(X38)|~v5_orders_2(X38)|~v1_yellow_0(X38)|~l1_orders_2(X38)))&(r2_yellow_0(X38,u1_struct_0(X38))|(v2_struct_0(X38)|~v5_orders_2(X38)|~v1_yellow_0(X38)|~l1_orders_2(X38)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t42_yellow_0])])])])).
% 0.19/0.41  cnf(c_0_50, negated_conjecture, (u1_struct_0(esk7_0)=esk8_0|r2_hidden(esk2_3(u1_struct_0(esk7_0),u1_struct_0(esk7_0),esk8_0),X1)|~v13_waybel_0(X1,esk7_0)|~r1_orders_2(esk7_0,X2,esk2_3(u1_struct_0(esk7_0),u1_struct_0(esk7_0),esk8_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk7_0)))|~r2_hidden(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41])])).
% 0.19/0.41  cnf(c_0_51, negated_conjecture, (v13_waybel_0(esk8_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.41  cnf(c_0_52, negated_conjecture, (u1_struct_0(esk7_0)=esk8_0|~r2_hidden(esk2_3(u1_struct_0(esk7_0),u1_struct_0(esk7_0),esk8_0),esk8_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_33]), c_0_43])).
% 0.19/0.41  cnf(c_0_53, negated_conjecture, (u1_struct_0(esk7_0)=esk8_0|r2_hidden(k3_yellow_0(esk7_0),esk8_0)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.19/0.41  cnf(c_0_54, plain, (k3_yellow_0(X1)=k1_yellow_0(X1,k1_xboole_0)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.19/0.41  fof(c_0_55, plain, ![X25, X26, X27, X28]:((~r2_lattice3(X25,X26,X27)|(~m1_subset_1(X28,u1_struct_0(X25))|(~r2_hidden(X28,X26)|r1_orders_2(X25,X28,X27)))|~m1_subset_1(X27,u1_struct_0(X25))|~l1_orders_2(X25))&((m1_subset_1(esk3_3(X25,X26,X27),u1_struct_0(X25))|r2_lattice3(X25,X26,X27)|~m1_subset_1(X27,u1_struct_0(X25))|~l1_orders_2(X25))&((r2_hidden(esk3_3(X25,X26,X27),X26)|r2_lattice3(X25,X26,X27)|~m1_subset_1(X27,u1_struct_0(X25))|~l1_orders_2(X25))&(~r1_orders_2(X25,esk3_3(X25,X26,X27),X27)|r2_lattice3(X25,X26,X27)|~m1_subset_1(X27,u1_struct_0(X25))|~l1_orders_2(X25))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).
% 0.19/0.41  cnf(c_0_56, plain, (r1_orders_2(X1,k1_yellow_0(X1,X2),X3)|~r1_yellow_0(X1,X2)|~r2_lattice3(X1,X2,X3)|~l1_orders_2(X1)|~m1_subset_1(X3,u1_struct_0(X1))), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_47]), c_0_48])).
% 0.19/0.41  cnf(c_0_57, negated_conjecture, (~v2_struct_0(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.41  cnf(c_0_58, plain, (r1_yellow_0(X1,k1_xboole_0)|v2_struct_0(X1)|~v5_orders_2(X1)|~v1_yellow_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.19/0.41  cnf(c_0_59, negated_conjecture, (v1_yellow_0(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.41  cnf(c_0_60, negated_conjecture, (v5_orders_2(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.41  cnf(c_0_61, negated_conjecture, (u1_struct_0(esk7_0)=esk8_0|~r1_orders_2(esk7_0,X1,esk2_3(u1_struct_0(esk7_0),u1_struct_0(esk7_0),esk8_0))|~r2_hidden(X1,esk8_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_25])]), c_0_52])).
% 0.19/0.41  cnf(c_0_62, negated_conjecture, (u1_struct_0(esk7_0)=esk8_0|r2_hidden(k1_yellow_0(esk7_0,k1_xboole_0),esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_41])])).
% 0.19/0.41  fof(c_0_63, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.19/0.41  cnf(c_0_64, plain, (r2_hidden(esk3_3(X1,X2,X3),X2)|r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.19/0.41  cnf(c_0_65, negated_conjecture, (u1_struct_0(esk7_0)=esk8_0|r1_orders_2(esk7_0,k1_yellow_0(esk7_0,X1),esk2_3(u1_struct_0(esk7_0),u1_struct_0(esk7_0),esk8_0))|~r1_yellow_0(esk7_0,X1)|~r2_lattice3(esk7_0,X1,esk2_3(u1_struct_0(esk7_0),u1_struct_0(esk7_0),esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_40]), c_0_41])])).
% 0.19/0.41  cnf(c_0_66, negated_conjecture, (r1_yellow_0(esk7_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_59]), c_0_60]), c_0_41])])).
% 0.19/0.41  cnf(c_0_67, negated_conjecture, (u1_struct_0(esk7_0)=esk8_0|~r1_orders_2(esk7_0,k1_yellow_0(esk7_0,k1_xboole_0),esk2_3(u1_struct_0(esk7_0),u1_struct_0(esk7_0),esk8_0))), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.19/0.41  cnf(c_0_68, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.19/0.41  cnf(c_0_69, negated_conjecture, (u1_struct_0(esk7_0)=esk8_0|r2_lattice3(esk7_0,X1,esk2_3(u1_struct_0(esk7_0),u1_struct_0(esk7_0),esk8_0))|r2_hidden(esk3_3(esk7_0,X1,esk2_3(u1_struct_0(esk7_0),u1_struct_0(esk7_0),esk8_0)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_40]), c_0_41])])).
% 0.19/0.41  cnf(c_0_70, plain, (~v1_subset_1(X1,X2)|X1!=X2|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.41  fof(c_0_71, plain, ![X18, X19]:(~m1_subset_1(X18,X19)|(v1_xboole_0(X19)|r2_hidden(X18,X19))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.19/0.41  cnf(c_0_72, negated_conjecture, (v1_subset_1(esk8_0,u1_struct_0(esk7_0))|~r2_hidden(k3_yellow_0(esk7_0),esk8_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.41  cnf(c_0_73, negated_conjecture, (u1_struct_0(esk7_0)=esk8_0|~r2_lattice3(esk7_0,k1_xboole_0,esk2_3(u1_struct_0(esk7_0),u1_struct_0(esk7_0),esk8_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_67])).
% 0.19/0.41  cnf(c_0_74, negated_conjecture, (u1_struct_0(esk7_0)=esk8_0|r2_lattice3(esk7_0,X1,esk2_3(u1_struct_0(esk7_0),u1_struct_0(esk7_0),esk8_0))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.19/0.41  cnf(c_0_75, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.19/0.41  cnf(c_0_76, plain, (~v1_subset_1(X1,X1)|~m1_subset_1(X1,k1_zfmisc_1(X1))), inference(er,[status(thm)],[c_0_70])).
% 0.19/0.41  cnf(c_0_77, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.19/0.41  cnf(c_0_78, negated_conjecture, (v1_subset_1(esk8_0,u1_struct_0(esk7_0))|~r2_hidden(k1_yellow_0(esk7_0,k1_xboole_0),esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_54]), c_0_41])])).
% 0.19/0.41  cnf(c_0_79, negated_conjecture, (u1_struct_0(esk7_0)=esk8_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_75])])).
% 0.19/0.41  cnf(c_0_80, plain, (~v1_subset_1(X1,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_76, c_0_33])])).
% 0.19/0.41  cnf(c_0_81, plain, (r2_hidden(k1_yellow_0(X1,X2),u1_struct_0(X1))|v1_xboole_0(u1_struct_0(X1))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_77, c_0_48])).
% 0.19/0.41  cnf(c_0_82, negated_conjecture, (~v1_xboole_0(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.41  cnf(c_0_83, negated_conjecture, (~r2_hidden(k1_yellow_0(esk7_0,k1_xboole_0),esk8_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_78, c_0_79]), c_0_80])).
% 0.19/0.41  cnf(c_0_84, negated_conjecture, (r2_hidden(k1_yellow_0(esk7_0,X1),esk8_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_79]), c_0_41])]), c_0_82])).
% 0.19/0.41  cnf(c_0_85, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_83, c_0_84])]), ['proof']).
% 0.19/0.41  # SZS output end CNFRefutation
% 0.19/0.41  # Proof object total steps             : 86
% 0.19/0.41  # Proof object clause steps            : 54
% 0.19/0.41  # Proof object formula steps           : 32
% 0.19/0.41  # Proof object conjectures             : 33
% 0.19/0.41  # Proof object clause conjectures      : 30
% 0.19/0.41  # Proof object formula conjectures     : 3
% 0.19/0.41  # Proof object initial clauses used    : 26
% 0.19/0.41  # Proof object initial formulas used   : 16
% 0.19/0.41  # Proof object generating inferences   : 21
% 0.19/0.41  # Proof object simplifying inferences  : 35
% 0.19/0.41  # Training examples: 0 positive, 0 negative
% 0.19/0.41  # Parsed axioms                        : 16
% 0.19/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.41  # Initial clauses                      : 47
% 0.19/0.41  # Removed in clause preprocessing      : 0
% 0.19/0.41  # Initial clauses in saturation        : 47
% 0.19/0.41  # Processed clauses                    : 370
% 0.19/0.41  # ...of these trivial                  : 2
% 0.19/0.41  # ...subsumed                          : 111
% 0.19/0.41  # ...remaining for further processing  : 257
% 0.19/0.41  # Other redundant clauses eliminated   : 5
% 0.19/0.41  # Clauses deleted for lack of memory   : 0
% 0.19/0.41  # Backward-subsumed                    : 16
% 0.19/0.41  # Backward-rewritten                   : 143
% 0.19/0.41  # Generated clauses                    : 737
% 0.19/0.41  # ...of the previous two non-trivial   : 746
% 0.19/0.41  # Contextual simplify-reflections      : 17
% 0.19/0.41  # Paramodulations                      : 732
% 0.19/0.41  # Factorizations                       : 0
% 0.19/0.41  # Equation resolutions                 : 5
% 0.19/0.41  # Propositional unsat checks           : 0
% 0.19/0.41  #    Propositional check models        : 0
% 0.19/0.41  #    Propositional check unsatisfiable : 0
% 0.19/0.41  #    Propositional clauses             : 0
% 0.19/0.41  #    Propositional clauses after purity: 0
% 0.19/0.41  #    Propositional unsat core size     : 0
% 0.19/0.41  #    Propositional preprocessing time  : 0.000
% 0.19/0.41  #    Propositional encoding time       : 0.000
% 0.19/0.41  #    Propositional solver time         : 0.000
% 0.19/0.41  #    Success case prop preproc time    : 0.000
% 0.19/0.41  #    Success case prop encoding time   : 0.000
% 0.19/0.41  #    Success case prop solver time     : 0.000
% 0.19/0.41  # Current number of processed clauses  : 93
% 0.19/0.41  #    Positive orientable unit clauses  : 19
% 0.19/0.41  #    Positive unorientable unit clauses: 0
% 0.19/0.41  #    Negative unit clauses             : 4
% 0.19/0.41  #    Non-unit-clauses                  : 70
% 0.19/0.41  # Current number of unprocessed clauses: 416
% 0.19/0.41  # ...number of literals in the above   : 1954
% 0.19/0.41  # Current number of archived formulas  : 0
% 0.19/0.41  # Current number of archived clauses   : 159
% 0.19/0.41  # Clause-clause subsumption calls (NU) : 6691
% 0.19/0.41  # Rec. Clause-clause subsumption calls : 2280
% 0.19/0.41  # Non-unit clause-clause subsumptions  : 122
% 0.19/0.41  # Unit Clause-clause subsumption calls : 287
% 0.19/0.41  # Rewrite failures with RHS unbound    : 0
% 0.19/0.41  # BW rewrite match attempts            : 22
% 0.19/0.41  # BW rewrite match successes           : 6
% 0.19/0.41  # Condensation attempts                : 371
% 0.19/0.41  # Condensation successes               : 0
% 0.19/0.41  # Termbank termtop insertions          : 22790
% 0.19/0.41  
% 0.19/0.41  # -------------------------------------------------
% 0.19/0.41  # User time                : 0.066 s
% 0.19/0.41  # System time              : 0.008 s
% 0.19/0.41  # Total time               : 0.074 s
% 0.19/0.41  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
