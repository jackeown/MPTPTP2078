%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:27 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 694 expanded)
%              Number of clauses        :   56 ( 290 expanded)
%              Number of leaves         :   15 ( 173 expanded)
%              Depth                    :   14
%              Number of atoms          :  356 (3900 expanded)
%              Number of equality atoms :   41 ( 270 expanded)
%              Maximal formula depth    :   15 (   5 average)
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

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t42_yellow_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v5_orders_2(X1)
        & v1_yellow_0(X1)
        & l1_orders_2(X1) )
     => ( r1_yellow_0(X1,k1_xboole_0)
        & r2_yellow_0(X1,u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_yellow_0)).

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

fof(c_0_15,plain,(
    ! [X45,X46] :
      ( ( ~ v1_subset_1(X46,X45)
        | X46 != X45
        | ~ m1_subset_1(X46,k1_zfmisc_1(X45)) )
      & ( X46 = X45
        | v1_subset_1(X46,X45)
        | ~ m1_subset_1(X46,k1_zfmisc_1(X45)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).

fof(c_0_16,plain,(
    ! [X13] :
      ( m1_subset_1(esk2_1(X13),k1_zfmisc_1(X13))
      & ~ v1_subset_1(esk2_1(X13),X13) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[rc3_subset_1])])])).

cnf(c_0_17,plain,
    ( X1 = X2
    | v1_subset_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_18,plain,
    ( m1_subset_1(esk2_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_19,plain,
    ( ~ v1_subset_1(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_20,plain,(
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

cnf(c_0_21,plain,
    ( esk2_1(X1) = X1 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])).

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

cnf(c_0_23,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),X1)
    | X2 = X3
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_18,c_0_21])).

fof(c_0_25,negated_conjecture,
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

fof(c_0_26,plain,(
    ! [X35,X36] :
      ( ~ l1_orders_2(X35)
      | m1_subset_1(k1_yellow_0(X35,X36),u1_struct_0(X35)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_yellow_0])])).

fof(c_0_27,plain,(
    ! [X24,X25,X26,X27] :
      ( ( ~ r2_lattice3(X24,X25,X26)
        | ~ m1_subset_1(X27,u1_struct_0(X24))
        | ~ r2_hidden(X27,X25)
        | r1_orders_2(X24,X27,X26)
        | ~ m1_subset_1(X26,u1_struct_0(X24))
        | ~ l1_orders_2(X24) )
      & ( m1_subset_1(esk3_3(X24,X25,X26),u1_struct_0(X24))
        | r2_lattice3(X24,X25,X26)
        | ~ m1_subset_1(X26,u1_struct_0(X24))
        | ~ l1_orders_2(X24) )
      & ( r2_hidden(esk3_3(X24,X25,X26),X25)
        | r2_lattice3(X24,X25,X26)
        | ~ m1_subset_1(X26,u1_struct_0(X24))
        | ~ l1_orders_2(X24) )
      & ( ~ r1_orders_2(X24,esk3_3(X24,X25,X26),X26)
        | r2_lattice3(X24,X25,X26)
        | ~ m1_subset_1(X26,u1_struct_0(X24))
        | ~ l1_orders_2(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).

cnf(c_0_28,plain,
    ( X1 = X2
    | m1_subset_1(esk1_3(X2,X1,X2),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_30,plain,(
    ! [X6,X7,X8] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(X6))
      | ~ r2_hidden(X8,X7)
      | r2_hidden(X8,X6) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

fof(c_0_31,plain,(
    ! [X30,X31,X32,X33] :
      ( ( r2_lattice3(X30,X31,X32)
        | X32 != k1_yellow_0(X30,X31)
        | ~ r1_yellow_0(X30,X31)
        | ~ m1_subset_1(X32,u1_struct_0(X30))
        | ~ l1_orders_2(X30) )
      & ( ~ m1_subset_1(X33,u1_struct_0(X30))
        | ~ r2_lattice3(X30,X31,X33)
        | r1_orders_2(X30,X32,X33)
        | X32 != k1_yellow_0(X30,X31)
        | ~ r1_yellow_0(X30,X31)
        | ~ m1_subset_1(X32,u1_struct_0(X30))
        | ~ l1_orders_2(X30) )
      & ( m1_subset_1(esk4_3(X30,X31,X32),u1_struct_0(X30))
        | ~ r2_lattice3(X30,X31,X32)
        | X32 = k1_yellow_0(X30,X31)
        | ~ r1_yellow_0(X30,X31)
        | ~ m1_subset_1(X32,u1_struct_0(X30))
        | ~ l1_orders_2(X30) )
      & ( r2_lattice3(X30,X31,esk4_3(X30,X31,X32))
        | ~ r2_lattice3(X30,X31,X32)
        | X32 = k1_yellow_0(X30,X31)
        | ~ r1_yellow_0(X30,X31)
        | ~ m1_subset_1(X32,u1_struct_0(X30))
        | ~ l1_orders_2(X30) )
      & ( ~ r1_orders_2(X30,X32,esk4_3(X30,X31,X32))
        | ~ r2_lattice3(X30,X31,X32)
        | X32 = k1_yellow_0(X30,X31)
        | ~ r1_yellow_0(X30,X31)
        | ~ m1_subset_1(X32,u1_struct_0(X30))
        | ~ l1_orders_2(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_yellow_0])])])])])).

cnf(c_0_32,plain,
    ( m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,negated_conjecture,
    ( l1_orders_2(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_34,plain,(
    ! [X22,X23] :
      ( ~ r2_hidden(X22,X23)
      | ~ r1_tarski(X23,X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_35,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),X2)
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,negated_conjecture,
    ( u1_struct_0(esk7_0) = esk8_0
    | m1_subset_1(esk1_3(u1_struct_0(esk7_0),esk8_0,u1_struct_0(esk7_0)),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

fof(c_0_37,plain,(
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

fof(c_0_38,plain,(
    ! [X19,X20,X21] :
      ( ~ r2_hidden(X19,X20)
      | ~ m1_subset_1(X20,k1_zfmisc_1(X21))
      | m1_subset_1(X19,X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_39,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X2 = X3
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_40,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_41,plain,
    ( r1_orders_2(X2,X4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X1)
    | X4 != k1_yellow_0(X2,X3)
    | ~ r1_yellow_0(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(k1_yellow_0(esk7_0,X1),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_43,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_44,negated_conjecture,
    ( u1_struct_0(esk7_0) = esk8_0
    | r2_lattice3(esk7_0,X1,esk1_3(u1_struct_0(esk7_0),esk8_0,u1_struct_0(esk7_0)))
    | r2_hidden(esk3_3(esk7_0,X1,esk1_3(u1_struct_0(esk7_0),esk8_0,u1_struct_0(esk7_0))),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_33])])).

fof(c_0_45,plain,(
    ! [X5] : r1_tarski(k1_xboole_0,X5) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_46,plain,(
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

fof(c_0_47,plain,(
    ! [X29] :
      ( ~ l1_orders_2(X29)
      | k3_yellow_0(X29) = k1_yellow_0(X29,k1_xboole_0) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_yellow_0])])).

cnf(c_0_48,plain,
    ( r2_hidden(X4,X1)
    | ~ v13_waybel_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r2_hidden(X3,X1)
    | ~ r1_orders_2(X2,X3,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_49,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_50,plain,
    ( X1 = X2
    | r2_hidden(esk1_3(X2,X1,X2),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_24]),c_0_40])).

cnf(c_0_51,negated_conjecture,
    ( r1_orders_2(esk7_0,k1_yellow_0(esk7_0,X1),X2)
    | k1_yellow_0(esk7_0,X1) != k1_yellow_0(esk7_0,X3)
    | ~ r1_yellow_0(esk7_0,X3)
    | ~ r2_lattice3(esk7_0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_33])])).

cnf(c_0_52,negated_conjecture,
    ( u1_struct_0(esk7_0) = esk8_0
    | r2_lattice3(esk7_0,X1,esk1_3(u1_struct_0(esk7_0),esk8_0,u1_struct_0(esk7_0)))
    | ~ r1_tarski(X1,esk3_3(esk7_0,X1,esk1_3(u1_struct_0(esk7_0),esk8_0,u1_struct_0(esk7_0)))) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_53,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_54,plain,
    ( r1_yellow_0(X1,k1_xboole_0)
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_yellow_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_55,negated_conjecture,
    ( v1_yellow_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_56,negated_conjecture,
    ( v5_orders_2(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_57,negated_conjecture,
    ( ~ v2_struct_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_58,plain,
    ( k3_yellow_0(X1) = k1_yellow_0(X1,k1_xboole_0)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_59,plain,
    ( r2_hidden(X1,X2)
    | ~ v13_waybel_0(X2,X3)
    | ~ r1_orders_2(X3,X4,X1)
    | ~ l1_orders_2(X3)
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X1,u1_struct_0(X3)) ),
    inference(csr,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_60,negated_conjecture,
    ( v13_waybel_0(esk8_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_61,plain,
    ( X2 = X3
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_62,negated_conjecture,
    ( u1_struct_0(esk7_0) = esk8_0
    | r2_hidden(esk1_3(u1_struct_0(esk7_0),esk8_0,u1_struct_0(esk7_0)),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_29])).

cnf(c_0_63,negated_conjecture,
    ( u1_struct_0(esk7_0) = esk8_0
    | r1_orders_2(esk7_0,k1_yellow_0(esk7_0,X1),esk1_3(u1_struct_0(esk7_0),esk8_0,u1_struct_0(esk7_0)))
    | k1_yellow_0(esk7_0,X1) != k1_yellow_0(esk7_0,X2)
    | ~ r1_yellow_0(esk7_0,X2)
    | ~ r2_lattice3(esk7_0,X2,esk1_3(u1_struct_0(esk7_0),esk8_0,u1_struct_0(esk7_0))) ),
    inference(spm,[status(thm)],[c_0_51,c_0_36])).

cnf(c_0_64,negated_conjecture,
    ( u1_struct_0(esk7_0) = esk8_0
    | r2_lattice3(esk7_0,k1_xboole_0,esk1_3(u1_struct_0(esk7_0),esk8_0,u1_struct_0(esk7_0))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_65,negated_conjecture,
    ( r1_yellow_0(esk7_0,k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56]),c_0_33])]),c_0_57])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(k3_yellow_0(esk7_0),esk8_0)
    | ~ v1_subset_1(esk8_0,u1_struct_0(esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_67,negated_conjecture,
    ( k3_yellow_0(esk7_0) = k1_yellow_0(esk7_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_33])).

cnf(c_0_68,negated_conjecture,
    ( r2_hidden(X1,esk8_0)
    | ~ r1_orders_2(esk7_0,X2,X1)
    | ~ r2_hidden(X2,esk8_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_29]),c_0_60]),c_0_33])])).

cnf(c_0_69,negated_conjecture,
    ( u1_struct_0(esk7_0) = esk8_0
    | ~ r2_hidden(esk1_3(u1_struct_0(esk7_0),esk8_0,u1_struct_0(esk7_0)),esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_24]),c_0_29])])).

cnf(c_0_70,negated_conjecture,
    ( u1_struct_0(esk7_0) = esk8_0
    | r1_orders_2(esk7_0,k1_yellow_0(esk7_0,X1),esk1_3(u1_struct_0(esk7_0),esk8_0,u1_struct_0(esk7_0)))
    | k1_yellow_0(esk7_0,X1) != k1_yellow_0(esk7_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65])])).

cnf(c_0_71,negated_conjecture,
    ( r2_hidden(k1_yellow_0(esk7_0,k1_xboole_0),esk8_0)
    | ~ v1_subset_1(esk8_0,u1_struct_0(esk7_0)) ),
    inference(rw,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_72,negated_conjecture,
    ( u1_struct_0(esk7_0) = esk8_0
    | v1_subset_1(esk8_0,u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_29])).

fof(c_0_73,plain,(
    ! [X17,X18] :
      ( ~ m1_subset_1(X17,X18)
      | v1_xboole_0(X18)
      | r2_hidden(X17,X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_74,negated_conjecture,
    ( v1_subset_1(esk8_0,u1_struct_0(esk7_0))
    | ~ r2_hidden(k3_yellow_0(esk7_0),esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_75,negated_conjecture,
    ( u1_struct_0(esk7_0) = esk8_0
    | ~ r1_orders_2(esk7_0,X1,esk1_3(u1_struct_0(esk7_0),esk8_0,u1_struct_0(esk7_0)))
    | ~ r2_hidden(X1,esk8_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_36]),c_0_69])).

cnf(c_0_76,negated_conjecture,
    ( u1_struct_0(esk7_0) = esk8_0
    | r1_orders_2(esk7_0,k1_yellow_0(esk7_0,k1_xboole_0),esk1_3(u1_struct_0(esk7_0),esk8_0,u1_struct_0(esk7_0))) ),
    inference(er,[status(thm)],[c_0_70])).

cnf(c_0_77,negated_conjecture,
    ( u1_struct_0(esk7_0) = esk8_0
    | r2_hidden(k1_yellow_0(esk7_0,k1_xboole_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_78,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_79,negated_conjecture,
    ( v1_subset_1(esk8_0,u1_struct_0(esk7_0))
    | ~ r2_hidden(k1_yellow_0(esk7_0,k1_xboole_0),esk8_0) ),
    inference(rw,[status(thm)],[c_0_74,c_0_67])).

cnf(c_0_80,negated_conjecture,
    ( u1_struct_0(esk7_0) = esk8_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_77])).

cnf(c_0_81,plain,
    ( ~ v1_subset_1(X1,X1) ),
    inference(rw,[status(thm)],[c_0_19,c_0_21])).

cnf(c_0_82,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk7_0))
    | r2_hidden(k1_yellow_0(esk7_0,X1),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_78,c_0_42])).

cnf(c_0_83,negated_conjecture,
    ( ~ v1_xboole_0(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_84,negated_conjecture,
    ( ~ r2_hidden(k1_yellow_0(esk7_0,k1_xboole_0),esk8_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_80]),c_0_81])).

cnf(c_0_85,negated_conjecture,
    ( r2_hidden(k1_yellow_0(esk7_0,X1),esk8_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82,c_0_80]),c_0_80]),c_0_83])).

cnf(c_0_86,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_84,c_0_85])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:18:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.41  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_PS_S0S
% 0.21/0.41  # and selection function SelectComplexG.
% 0.21/0.41  #
% 0.21/0.41  # Preprocessing time       : 0.029 s
% 0.21/0.41  # Presaturation interreduction done
% 0.21/0.41  
% 0.21/0.41  # Proof found!
% 0.21/0.41  # SZS status Theorem
% 0.21/0.41  # SZS output start CNFRefutation
% 0.21/0.41  fof(d7_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(v1_subset_1(X2,X1)<=>X2!=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 0.21/0.41  fof(rc3_subset_1, axiom, ![X1]:?[X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))&~(v1_subset_1(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc3_subset_1)).
% 0.21/0.41  fof(t8_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(![X4]:(m1_subset_1(X4,X1)=>(r2_hidden(X4,X2)<=>r2_hidden(X4,X3)))=>X2=X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_subset_1)).
% 0.21/0.41  fof(t8_waybel_7, conjecture, ![X1]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&v1_yellow_0(X1))&l1_orders_2(X1))=>![X2]:((((~(v1_xboole_0(X2))&v2_waybel_0(X2,X1))&v13_waybel_0(X2,X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v1_subset_1(X2,u1_struct_0(X1))<=>~(r2_hidden(k3_yellow_0(X1),X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_waybel_7)).
% 0.21/0.41  fof(dt_k1_yellow_0, axiom, ![X1, X2]:(l1_orders_2(X1)=>m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_yellow_0)).
% 0.21/0.41  fof(d9_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X2)=>r1_orders_2(X1,X4,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_lattice3)).
% 0.21/0.41  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 0.21/0.41  fof(d9_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_yellow_0(X1,X2)=>(X3=k1_yellow_0(X1,X2)<=>(r2_lattice3(X1,X2,X3)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X4)=>r1_orders_2(X1,X3,X4)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_yellow_0)).
% 0.21/0.41  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.21/0.41  fof(d20_waybel_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v13_waybel_0(X2,X1)<=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((r2_hidden(X3,X2)&r1_orders_2(X1,X3,X4))=>r2_hidden(X4,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d20_waybel_0)).
% 0.21/0.41  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 0.21/0.41  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.21/0.41  fof(t42_yellow_0, axiom, ![X1]:((((~(v2_struct_0(X1))&v5_orders_2(X1))&v1_yellow_0(X1))&l1_orders_2(X1))=>(r1_yellow_0(X1,k1_xboole_0)&r2_yellow_0(X1,u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_yellow_0)).
% 0.21/0.41  fof(d11_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>k3_yellow_0(X1)=k1_yellow_0(X1,k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_yellow_0)).
% 0.21/0.41  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 0.21/0.41  fof(c_0_15, plain, ![X45, X46]:((~v1_subset_1(X46,X45)|X46!=X45|~m1_subset_1(X46,k1_zfmisc_1(X45)))&(X46=X45|v1_subset_1(X46,X45)|~m1_subset_1(X46,k1_zfmisc_1(X45)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).
% 0.21/0.41  fof(c_0_16, plain, ![X13]:(m1_subset_1(esk2_1(X13),k1_zfmisc_1(X13))&~v1_subset_1(esk2_1(X13),X13)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[rc3_subset_1])])])).
% 0.21/0.41  cnf(c_0_17, plain, (X1=X2|v1_subset_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.41  cnf(c_0_18, plain, (m1_subset_1(esk2_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.41  cnf(c_0_19, plain, (~v1_subset_1(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.41  fof(c_0_20, plain, ![X9, X10, X11]:((m1_subset_1(esk1_3(X9,X10,X11),X9)|X10=X11|~m1_subset_1(X11,k1_zfmisc_1(X9))|~m1_subset_1(X10,k1_zfmisc_1(X9)))&((~r2_hidden(esk1_3(X9,X10,X11),X10)|~r2_hidden(esk1_3(X9,X10,X11),X11)|X10=X11|~m1_subset_1(X11,k1_zfmisc_1(X9))|~m1_subset_1(X10,k1_zfmisc_1(X9)))&(r2_hidden(esk1_3(X9,X10,X11),X10)|r2_hidden(esk1_3(X9,X10,X11),X11)|X10=X11|~m1_subset_1(X11,k1_zfmisc_1(X9))|~m1_subset_1(X10,k1_zfmisc_1(X9))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_subset_1])])])])])).
% 0.21/0.41  cnf(c_0_21, plain, (esk2_1(X1)=X1), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19])).
% 0.21/0.41  fof(c_0_22, negated_conjecture, ~(![X1]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&v1_yellow_0(X1))&l1_orders_2(X1))=>![X2]:((((~(v1_xboole_0(X2))&v2_waybel_0(X2,X1))&v13_waybel_0(X2,X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v1_subset_1(X2,u1_struct_0(X1))<=>~(r2_hidden(k3_yellow_0(X1),X2)))))), inference(assume_negation,[status(cth)],[t8_waybel_7])).
% 0.21/0.41  cnf(c_0_23, plain, (m1_subset_1(esk1_3(X1,X2,X3),X1)|X2=X3|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.41  cnf(c_0_24, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_18, c_0_21])).
% 0.21/0.41  fof(c_0_25, negated_conjecture, ((((((~v2_struct_0(esk7_0)&v3_orders_2(esk7_0))&v4_orders_2(esk7_0))&v5_orders_2(esk7_0))&v1_yellow_0(esk7_0))&l1_orders_2(esk7_0))&((((~v1_xboole_0(esk8_0)&v2_waybel_0(esk8_0,esk7_0))&v13_waybel_0(esk8_0,esk7_0))&m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(esk7_0))))&((~v1_subset_1(esk8_0,u1_struct_0(esk7_0))|r2_hidden(k3_yellow_0(esk7_0),esk8_0))&(v1_subset_1(esk8_0,u1_struct_0(esk7_0))|~r2_hidden(k3_yellow_0(esk7_0),esk8_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_22])])])])).
% 0.21/0.41  fof(c_0_26, plain, ![X35, X36]:(~l1_orders_2(X35)|m1_subset_1(k1_yellow_0(X35,X36),u1_struct_0(X35))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_yellow_0])])).
% 0.21/0.41  fof(c_0_27, plain, ![X24, X25, X26, X27]:((~r2_lattice3(X24,X25,X26)|(~m1_subset_1(X27,u1_struct_0(X24))|(~r2_hidden(X27,X25)|r1_orders_2(X24,X27,X26)))|~m1_subset_1(X26,u1_struct_0(X24))|~l1_orders_2(X24))&((m1_subset_1(esk3_3(X24,X25,X26),u1_struct_0(X24))|r2_lattice3(X24,X25,X26)|~m1_subset_1(X26,u1_struct_0(X24))|~l1_orders_2(X24))&((r2_hidden(esk3_3(X24,X25,X26),X25)|r2_lattice3(X24,X25,X26)|~m1_subset_1(X26,u1_struct_0(X24))|~l1_orders_2(X24))&(~r1_orders_2(X24,esk3_3(X24,X25,X26),X26)|r2_lattice3(X24,X25,X26)|~m1_subset_1(X26,u1_struct_0(X24))|~l1_orders_2(X24))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).
% 0.21/0.41  cnf(c_0_28, plain, (X1=X2|m1_subset_1(esk1_3(X2,X1,X2),X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.21/0.41  cnf(c_0_29, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(esk7_0)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.41  fof(c_0_30, plain, ![X6, X7, X8]:(~m1_subset_1(X7,k1_zfmisc_1(X6))|(~r2_hidden(X8,X7)|r2_hidden(X8,X6))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.21/0.41  fof(c_0_31, plain, ![X30, X31, X32, X33]:(((r2_lattice3(X30,X31,X32)|X32!=k1_yellow_0(X30,X31)|~r1_yellow_0(X30,X31)|~m1_subset_1(X32,u1_struct_0(X30))|~l1_orders_2(X30))&(~m1_subset_1(X33,u1_struct_0(X30))|(~r2_lattice3(X30,X31,X33)|r1_orders_2(X30,X32,X33))|X32!=k1_yellow_0(X30,X31)|~r1_yellow_0(X30,X31)|~m1_subset_1(X32,u1_struct_0(X30))|~l1_orders_2(X30)))&((m1_subset_1(esk4_3(X30,X31,X32),u1_struct_0(X30))|~r2_lattice3(X30,X31,X32)|X32=k1_yellow_0(X30,X31)|~r1_yellow_0(X30,X31)|~m1_subset_1(X32,u1_struct_0(X30))|~l1_orders_2(X30))&((r2_lattice3(X30,X31,esk4_3(X30,X31,X32))|~r2_lattice3(X30,X31,X32)|X32=k1_yellow_0(X30,X31)|~r1_yellow_0(X30,X31)|~m1_subset_1(X32,u1_struct_0(X30))|~l1_orders_2(X30))&(~r1_orders_2(X30,X32,esk4_3(X30,X31,X32))|~r2_lattice3(X30,X31,X32)|X32=k1_yellow_0(X30,X31)|~r1_yellow_0(X30,X31)|~m1_subset_1(X32,u1_struct_0(X30))|~l1_orders_2(X30))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_yellow_0])])])])])).
% 0.21/0.41  cnf(c_0_32, plain, (m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.21/0.41  cnf(c_0_33, negated_conjecture, (l1_orders_2(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.41  fof(c_0_34, plain, ![X22, X23]:(~r2_hidden(X22,X23)|~r1_tarski(X23,X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.21/0.41  cnf(c_0_35, plain, (r2_hidden(esk3_3(X1,X2,X3),X2)|r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.21/0.41  cnf(c_0_36, negated_conjecture, (u1_struct_0(esk7_0)=esk8_0|m1_subset_1(esk1_3(u1_struct_0(esk7_0),esk8_0,u1_struct_0(esk7_0)),u1_struct_0(esk7_0))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.21/0.41  fof(c_0_37, plain, ![X39, X40, X41, X42]:((~v13_waybel_0(X40,X39)|(~m1_subset_1(X41,u1_struct_0(X39))|(~m1_subset_1(X42,u1_struct_0(X39))|(~r2_hidden(X41,X40)|~r1_orders_2(X39,X41,X42)|r2_hidden(X42,X40))))|~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))|~l1_orders_2(X39))&((m1_subset_1(esk5_2(X39,X40),u1_struct_0(X39))|v13_waybel_0(X40,X39)|~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))|~l1_orders_2(X39))&((m1_subset_1(esk6_2(X39,X40),u1_struct_0(X39))|v13_waybel_0(X40,X39)|~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))|~l1_orders_2(X39))&(((r2_hidden(esk5_2(X39,X40),X40)|v13_waybel_0(X40,X39)|~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))|~l1_orders_2(X39))&(r1_orders_2(X39,esk5_2(X39,X40),esk6_2(X39,X40))|v13_waybel_0(X40,X39)|~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))|~l1_orders_2(X39)))&(~r2_hidden(esk6_2(X39,X40),X40)|v13_waybel_0(X40,X39)|~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))|~l1_orders_2(X39)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d20_waybel_0])])])])])).
% 0.21/0.41  fof(c_0_38, plain, ![X19, X20, X21]:(~r2_hidden(X19,X20)|~m1_subset_1(X20,k1_zfmisc_1(X21))|m1_subset_1(X19,X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.21/0.41  cnf(c_0_39, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r2_hidden(esk1_3(X1,X2,X3),X3)|X2=X3|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.41  cnf(c_0_40, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.21/0.41  cnf(c_0_41, plain, (r1_orders_2(X2,X4,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~r2_lattice3(X2,X3,X1)|X4!=k1_yellow_0(X2,X3)|~r1_yellow_0(X2,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.21/0.41  cnf(c_0_42, negated_conjecture, (m1_subset_1(k1_yellow_0(esk7_0,X1),u1_struct_0(esk7_0))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.21/0.41  cnf(c_0_43, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.21/0.41  cnf(c_0_44, negated_conjecture, (u1_struct_0(esk7_0)=esk8_0|r2_lattice3(esk7_0,X1,esk1_3(u1_struct_0(esk7_0),esk8_0,u1_struct_0(esk7_0)))|r2_hidden(esk3_3(esk7_0,X1,esk1_3(u1_struct_0(esk7_0),esk8_0,u1_struct_0(esk7_0))),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_33])])).
% 0.21/0.41  fof(c_0_45, plain, ![X5]:r1_tarski(k1_xboole_0,X5), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.21/0.41  fof(c_0_46, plain, ![X38]:((r1_yellow_0(X38,k1_xboole_0)|(v2_struct_0(X38)|~v5_orders_2(X38)|~v1_yellow_0(X38)|~l1_orders_2(X38)))&(r2_yellow_0(X38,u1_struct_0(X38))|(v2_struct_0(X38)|~v5_orders_2(X38)|~v1_yellow_0(X38)|~l1_orders_2(X38)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t42_yellow_0])])])])).
% 0.21/0.41  fof(c_0_47, plain, ![X29]:(~l1_orders_2(X29)|k3_yellow_0(X29)=k1_yellow_0(X29,k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_yellow_0])])).
% 0.21/0.41  cnf(c_0_48, plain, (r2_hidden(X4,X1)|~v13_waybel_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X2))|~m1_subset_1(X4,u1_struct_0(X2))|~r2_hidden(X3,X1)|~r1_orders_2(X2,X3,X4)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.21/0.41  cnf(c_0_49, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.21/0.41  cnf(c_0_50, plain, (X1=X2|r2_hidden(esk1_3(X2,X1,X2),X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_24]), c_0_40])).
% 0.21/0.41  cnf(c_0_51, negated_conjecture, (r1_orders_2(esk7_0,k1_yellow_0(esk7_0,X1),X2)|k1_yellow_0(esk7_0,X1)!=k1_yellow_0(esk7_0,X3)|~r1_yellow_0(esk7_0,X3)|~r2_lattice3(esk7_0,X3,X2)|~m1_subset_1(X2,u1_struct_0(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_33])])).
% 0.21/0.41  cnf(c_0_52, negated_conjecture, (u1_struct_0(esk7_0)=esk8_0|r2_lattice3(esk7_0,X1,esk1_3(u1_struct_0(esk7_0),esk8_0,u1_struct_0(esk7_0)))|~r1_tarski(X1,esk3_3(esk7_0,X1,esk1_3(u1_struct_0(esk7_0),esk8_0,u1_struct_0(esk7_0))))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.21/0.41  cnf(c_0_53, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.21/0.41  cnf(c_0_54, plain, (r1_yellow_0(X1,k1_xboole_0)|v2_struct_0(X1)|~v5_orders_2(X1)|~v1_yellow_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.21/0.41  cnf(c_0_55, negated_conjecture, (v1_yellow_0(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.41  cnf(c_0_56, negated_conjecture, (v5_orders_2(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.41  cnf(c_0_57, negated_conjecture, (~v2_struct_0(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.41  cnf(c_0_58, plain, (k3_yellow_0(X1)=k1_yellow_0(X1,k1_xboole_0)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.21/0.41  cnf(c_0_59, plain, (r2_hidden(X1,X2)|~v13_waybel_0(X2,X3)|~r1_orders_2(X3,X4,X1)|~l1_orders_2(X3)|~r2_hidden(X4,X2)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~m1_subset_1(X1,u1_struct_0(X3))), inference(csr,[status(thm)],[c_0_48, c_0_49])).
% 0.21/0.41  cnf(c_0_60, negated_conjecture, (v13_waybel_0(esk8_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.41  cnf(c_0_61, plain, (X2=X3|~r2_hidden(esk1_3(X1,X2,X3),X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.41  cnf(c_0_62, negated_conjecture, (u1_struct_0(esk7_0)=esk8_0|r2_hidden(esk1_3(u1_struct_0(esk7_0),esk8_0,u1_struct_0(esk7_0)),u1_struct_0(esk7_0))), inference(spm,[status(thm)],[c_0_50, c_0_29])).
% 0.21/0.41  cnf(c_0_63, negated_conjecture, (u1_struct_0(esk7_0)=esk8_0|r1_orders_2(esk7_0,k1_yellow_0(esk7_0,X1),esk1_3(u1_struct_0(esk7_0),esk8_0,u1_struct_0(esk7_0)))|k1_yellow_0(esk7_0,X1)!=k1_yellow_0(esk7_0,X2)|~r1_yellow_0(esk7_0,X2)|~r2_lattice3(esk7_0,X2,esk1_3(u1_struct_0(esk7_0),esk8_0,u1_struct_0(esk7_0)))), inference(spm,[status(thm)],[c_0_51, c_0_36])).
% 0.21/0.41  cnf(c_0_64, negated_conjecture, (u1_struct_0(esk7_0)=esk8_0|r2_lattice3(esk7_0,k1_xboole_0,esk1_3(u1_struct_0(esk7_0),esk8_0,u1_struct_0(esk7_0)))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.21/0.41  cnf(c_0_65, negated_conjecture, (r1_yellow_0(esk7_0,k1_xboole_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56]), c_0_33])]), c_0_57])).
% 0.21/0.41  cnf(c_0_66, negated_conjecture, (r2_hidden(k3_yellow_0(esk7_0),esk8_0)|~v1_subset_1(esk8_0,u1_struct_0(esk7_0))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.41  cnf(c_0_67, negated_conjecture, (k3_yellow_0(esk7_0)=k1_yellow_0(esk7_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_58, c_0_33])).
% 0.21/0.41  cnf(c_0_68, negated_conjecture, (r2_hidden(X1,esk8_0)|~r1_orders_2(esk7_0,X2,X1)|~r2_hidden(X2,esk8_0)|~m1_subset_1(X1,u1_struct_0(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_29]), c_0_60]), c_0_33])])).
% 0.21/0.41  cnf(c_0_69, negated_conjecture, (u1_struct_0(esk7_0)=esk8_0|~r2_hidden(esk1_3(u1_struct_0(esk7_0),esk8_0,u1_struct_0(esk7_0)),esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_24]), c_0_29])])).
% 0.21/0.41  cnf(c_0_70, negated_conjecture, (u1_struct_0(esk7_0)=esk8_0|r1_orders_2(esk7_0,k1_yellow_0(esk7_0,X1),esk1_3(u1_struct_0(esk7_0),esk8_0,u1_struct_0(esk7_0)))|k1_yellow_0(esk7_0,X1)!=k1_yellow_0(esk7_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_65])])).
% 0.21/0.41  cnf(c_0_71, negated_conjecture, (r2_hidden(k1_yellow_0(esk7_0,k1_xboole_0),esk8_0)|~v1_subset_1(esk8_0,u1_struct_0(esk7_0))), inference(rw,[status(thm)],[c_0_66, c_0_67])).
% 0.21/0.41  cnf(c_0_72, negated_conjecture, (u1_struct_0(esk7_0)=esk8_0|v1_subset_1(esk8_0,u1_struct_0(esk7_0))), inference(spm,[status(thm)],[c_0_17, c_0_29])).
% 0.21/0.41  fof(c_0_73, plain, ![X17, X18]:(~m1_subset_1(X17,X18)|(v1_xboole_0(X18)|r2_hidden(X17,X18))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.21/0.41  cnf(c_0_74, negated_conjecture, (v1_subset_1(esk8_0,u1_struct_0(esk7_0))|~r2_hidden(k3_yellow_0(esk7_0),esk8_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.41  cnf(c_0_75, negated_conjecture, (u1_struct_0(esk7_0)=esk8_0|~r1_orders_2(esk7_0,X1,esk1_3(u1_struct_0(esk7_0),esk8_0,u1_struct_0(esk7_0)))|~r2_hidden(X1,esk8_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_36]), c_0_69])).
% 0.21/0.41  cnf(c_0_76, negated_conjecture, (u1_struct_0(esk7_0)=esk8_0|r1_orders_2(esk7_0,k1_yellow_0(esk7_0,k1_xboole_0),esk1_3(u1_struct_0(esk7_0),esk8_0,u1_struct_0(esk7_0)))), inference(er,[status(thm)],[c_0_70])).
% 0.21/0.41  cnf(c_0_77, negated_conjecture, (u1_struct_0(esk7_0)=esk8_0|r2_hidden(k1_yellow_0(esk7_0,k1_xboole_0),esk8_0)), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.21/0.41  cnf(c_0_78, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.21/0.41  cnf(c_0_79, negated_conjecture, (v1_subset_1(esk8_0,u1_struct_0(esk7_0))|~r2_hidden(k1_yellow_0(esk7_0,k1_xboole_0),esk8_0)), inference(rw,[status(thm)],[c_0_74, c_0_67])).
% 0.21/0.41  cnf(c_0_80, negated_conjecture, (u1_struct_0(esk7_0)=esk8_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_77])).
% 0.21/0.41  cnf(c_0_81, plain, (~v1_subset_1(X1,X1)), inference(rw,[status(thm)],[c_0_19, c_0_21])).
% 0.21/0.41  cnf(c_0_82, negated_conjecture, (v1_xboole_0(u1_struct_0(esk7_0))|r2_hidden(k1_yellow_0(esk7_0,X1),u1_struct_0(esk7_0))), inference(spm,[status(thm)],[c_0_78, c_0_42])).
% 0.21/0.41  cnf(c_0_83, negated_conjecture, (~v1_xboole_0(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.41  cnf(c_0_84, negated_conjecture, (~r2_hidden(k1_yellow_0(esk7_0,k1_xboole_0),esk8_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_79, c_0_80]), c_0_81])).
% 0.21/0.41  cnf(c_0_85, negated_conjecture, (r2_hidden(k1_yellow_0(esk7_0,X1),esk8_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82, c_0_80]), c_0_80]), c_0_83])).
% 0.21/0.41  cnf(c_0_86, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_84, c_0_85])]), ['proof']).
% 0.21/0.41  # SZS output end CNFRefutation
% 0.21/0.41  # Proof object total steps             : 87
% 0.21/0.41  # Proof object clause steps            : 56
% 0.21/0.41  # Proof object formula steps           : 31
% 0.21/0.41  # Proof object conjectures             : 36
% 0.21/0.41  # Proof object clause conjectures      : 33
% 0.21/0.41  # Proof object formula conjectures     : 3
% 0.21/0.41  # Proof object initial clauses used    : 26
% 0.21/0.41  # Proof object initial formulas used   : 15
% 0.21/0.41  # Proof object generating inferences   : 22
% 0.21/0.41  # Proof object simplifying inferences  : 32
% 0.21/0.41  # Training examples: 0 positive, 0 negative
% 0.21/0.41  # Parsed axioms                        : 17
% 0.21/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.41  # Initial clauses                      : 45
% 0.21/0.41  # Removed in clause preprocessing      : 0
% 0.21/0.41  # Initial clauses in saturation        : 45
% 0.21/0.41  # Processed clauses                    : 315
% 0.21/0.41  # ...of these trivial                  : 0
% 0.21/0.41  # ...subsumed                          : 41
% 0.21/0.41  # ...remaining for further processing  : 274
% 0.21/0.41  # Other redundant clauses eliminated   : 1
% 0.21/0.41  # Clauses deleted for lack of memory   : 0
% 0.21/0.41  # Backward-subsumed                    : 10
% 0.21/0.41  # Backward-rewritten                   : 151
% 0.21/0.41  # Generated clauses                    : 517
% 0.21/0.41  # ...of the previous two non-trivial   : 534
% 0.21/0.41  # Contextual simplify-reflections      : 7
% 0.21/0.41  # Paramodulations                      : 512
% 0.21/0.41  # Factorizations                       : 0
% 0.21/0.41  # Equation resolutions                 : 5
% 0.21/0.41  # Propositional unsat checks           : 0
% 0.21/0.41  #    Propositional check models        : 0
% 0.21/0.41  #    Propositional check unsatisfiable : 0
% 0.21/0.41  #    Propositional clauses             : 0
% 0.21/0.41  #    Propositional clauses after purity: 0
% 0.21/0.41  #    Propositional unsat core size     : 0
% 0.21/0.41  #    Propositional preprocessing time  : 0.000
% 0.21/0.41  #    Propositional encoding time       : 0.000
% 0.21/0.41  #    Propositional solver time         : 0.000
% 0.21/0.41  #    Success case prop preproc time    : 0.000
% 0.21/0.41  #    Success case prop encoding time   : 0.000
% 0.21/0.41  #    Success case prop solver time     : 0.000
% 0.21/0.41  # Current number of processed clauses  : 67
% 0.21/0.41  #    Positive orientable unit clauses  : 16
% 0.21/0.41  #    Positive unorientable unit clauses: 0
% 0.21/0.41  #    Negative unit clauses             : 3
% 0.21/0.41  #    Non-unit-clauses                  : 48
% 0.21/0.41  # Current number of unprocessed clauses: 273
% 0.21/0.41  # ...number of literals in the above   : 1356
% 0.21/0.41  # Current number of archived formulas  : 0
% 0.21/0.41  # Current number of archived clauses   : 206
% 0.21/0.41  # Clause-clause subsumption calls (NU) : 5505
% 0.21/0.41  # Rec. Clause-clause subsumption calls : 1672
% 0.21/0.41  # Non-unit clause-clause subsumptions  : 57
% 0.21/0.41  # Unit Clause-clause subsumption calls : 124
% 0.21/0.41  # Rewrite failures with RHS unbound    : 0
% 0.21/0.41  # BW rewrite match attempts            : 17
% 0.21/0.41  # BW rewrite match successes           : 9
% 0.21/0.41  # Condensation attempts                : 0
% 0.21/0.41  # Condensation successes               : 0
% 0.21/0.41  # Termbank termtop insertions          : 19681
% 0.21/0.41  
% 0.21/0.41  # -------------------------------------------------
% 0.21/0.41  # User time                : 0.064 s
% 0.21/0.41  # System time              : 0.003 s
% 0.21/0.41  # Total time               : 0.066 s
% 0.21/0.41  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
