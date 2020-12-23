%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:24 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 822 expanded)
%              Number of clauses        :   69 ( 342 expanded)
%              Number of leaves         :   18 ( 196 expanded)
%              Depth                    :   15
%              Number of atoms          :  383 (5258 expanded)
%              Number of equality atoms :   38 ( 137 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   30 (   2 average)
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

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

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

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(d7_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( v1_subset_1(X2,X1)
      <=> X2 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

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

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(c_0_18,negated_conjecture,(
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

fof(c_0_19,plain,(
    ! [X19,X20] :
      ( ~ r2_hidden(X19,X20)
      | m1_subset_1(X19,X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

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
    ! [X41,X42] :
      ( ~ l1_orders_2(X41)
      | m1_subset_1(k1_yellow_0(X41,X42),u1_struct_0(X41)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_yellow_0])])).

fof(c_0_22,negated_conjecture,
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
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_18])])])])).

fof(c_0_23,plain,(
    ! [X30,X31,X32,X33] :
      ( ( ~ r2_lattice3(X30,X31,X32)
        | ~ m1_subset_1(X33,u1_struct_0(X30))
        | ~ r2_hidden(X33,X31)
        | r1_orders_2(X30,X33,X32)
        | ~ m1_subset_1(X32,u1_struct_0(X30))
        | ~ l1_orders_2(X30) )
      & ( m1_subset_1(esk2_3(X30,X31,X32),u1_struct_0(X30))
        | r2_lattice3(X30,X31,X32)
        | ~ m1_subset_1(X32,u1_struct_0(X30))
        | ~ l1_orders_2(X30) )
      & ( r2_hidden(esk2_3(X30,X31,X32),X31)
        | r2_lattice3(X30,X31,X32)
        | ~ m1_subset_1(X32,u1_struct_0(X30))
        | ~ l1_orders_2(X30) )
      & ( ~ r1_orders_2(X30,esk2_3(X30,X31,X32),X32)
        | r2_lattice3(X30,X31,X32)
        | ~ m1_subset_1(X32,u1_struct_0(X30))
        | ~ l1_orders_2(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).

cnf(c_0_24,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( l1_orders_2(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( m1_subset_1(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

fof(c_0_30,plain,(
    ! [X36,X37,X38,X39] :
      ( ( r2_lattice3(X36,X37,X38)
        | X38 != k1_yellow_0(X36,X37)
        | ~ r1_yellow_0(X36,X37)
        | ~ m1_subset_1(X38,u1_struct_0(X36))
        | ~ l1_orders_2(X36) )
      & ( ~ m1_subset_1(X39,u1_struct_0(X36))
        | ~ r2_lattice3(X36,X37,X39)
        | r1_orders_2(X36,X38,X39)
        | X38 != k1_yellow_0(X36,X37)
        | ~ r1_yellow_0(X36,X37)
        | ~ m1_subset_1(X38,u1_struct_0(X36))
        | ~ l1_orders_2(X36) )
      & ( m1_subset_1(esk3_3(X36,X37,X38),u1_struct_0(X36))
        | ~ r2_lattice3(X36,X37,X38)
        | X38 = k1_yellow_0(X36,X37)
        | ~ r1_yellow_0(X36,X37)
        | ~ m1_subset_1(X38,u1_struct_0(X36))
        | ~ l1_orders_2(X36) )
      & ( r2_lattice3(X36,X37,esk3_3(X36,X37,X38))
        | ~ r2_lattice3(X36,X37,X38)
        | X38 = k1_yellow_0(X36,X37)
        | ~ r1_yellow_0(X36,X37)
        | ~ m1_subset_1(X38,u1_struct_0(X36))
        | ~ l1_orders_2(X36) )
      & ( ~ r1_orders_2(X36,X38,esk3_3(X36,X37,X38))
        | ~ r2_lattice3(X36,X37,X38)
        | X38 = k1_yellow_0(X36,X37)
        | ~ r1_yellow_0(X36,X37)
        | ~ m1_subset_1(X38,u1_struct_0(X36))
        | ~ l1_orders_2(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_yellow_0])])])])])).

fof(c_0_31,plain,(
    ! [X28,X29] :
      ( ~ r2_hidden(X28,X29)
      | ~ r1_tarski(X29,X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(k1_yellow_0(esk6_0,X1),u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

fof(c_0_33,plain,(
    ! [X23,X24] :
      ( ( ~ m1_subset_1(X23,k1_zfmisc_1(X24))
        | r1_tarski(X23,X24) )
      & ( ~ r1_tarski(X23,X24)
        | m1_subset_1(X23,k1_zfmisc_1(X24)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_34,plain,(
    ! [X18] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X18)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

fof(c_0_35,plain,(
    ! [X51,X52] :
      ( ( ~ v1_subset_1(X52,X51)
        | X52 != X51
        | ~ m1_subset_1(X52,k1_zfmisc_1(X51)) )
      & ( X52 = X51
        | v1_subset_1(X52,X51)
        | ~ m1_subset_1(X52,k1_zfmisc_1(X51)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).

cnf(c_0_36,plain,
    ( r2_lattice3(X1,X2,esk1_2(u1_struct_0(X1),X3))
    | r2_hidden(esk2_3(X1,X2,esk1_2(u1_struct_0(X1),X3)),X2)
    | r1_tarski(u1_struct_0(X1),X3)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

fof(c_0_37,plain,(
    ! [X45,X46,X47,X48] :
      ( ( ~ v13_waybel_0(X46,X45)
        | ~ m1_subset_1(X47,u1_struct_0(X45))
        | ~ m1_subset_1(X48,u1_struct_0(X45))
        | ~ r2_hidden(X47,X46)
        | ~ r1_orders_2(X45,X47,X48)
        | r2_hidden(X48,X46)
        | ~ m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X45)))
        | ~ l1_orders_2(X45) )
      & ( m1_subset_1(esk4_2(X45,X46),u1_struct_0(X45))
        | v13_waybel_0(X46,X45)
        | ~ m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X45)))
        | ~ l1_orders_2(X45) )
      & ( m1_subset_1(esk5_2(X45,X46),u1_struct_0(X45))
        | v13_waybel_0(X46,X45)
        | ~ m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X45)))
        | ~ l1_orders_2(X45) )
      & ( r2_hidden(esk4_2(X45,X46),X46)
        | v13_waybel_0(X46,X45)
        | ~ m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X45)))
        | ~ l1_orders_2(X45) )
      & ( r1_orders_2(X45,esk4_2(X45,X46),esk5_2(X45,X46))
        | v13_waybel_0(X46,X45)
        | ~ m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X45)))
        | ~ l1_orders_2(X45) )
      & ( ~ r2_hidden(esk5_2(X45,X46),X46)
        | v13_waybel_0(X46,X45)
        | ~ m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X45)))
        | ~ l1_orders_2(X45) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d20_waybel_0])])])])])).

fof(c_0_38,plain,(
    ! [X25,X26,X27] :
      ( ~ r2_hidden(X25,X26)
      | ~ m1_subset_1(X26,k1_zfmisc_1(X27))
      | m1_subset_1(X25,X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_39,plain,
    ( r1_orders_2(X2,X4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X1)
    | X4 != k1_yellow_0(X2,X3)
    | ~ r1_yellow_0(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_41,negated_conjecture,
    ( r2_lattice3(esk6_0,X1,k1_yellow_0(esk6_0,X2))
    | r2_hidden(esk2_3(esk6_0,X1,k1_yellow_0(esk6_0,X2)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_32]),c_0_27])])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_43,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_44,plain,(
    ! [X44] :
      ( ( r1_yellow_0(X44,k1_xboole_0)
        | v2_struct_0(X44)
        | ~ v5_orders_2(X44)
        | ~ v1_yellow_0(X44)
        | ~ l1_orders_2(X44) )
      & ( r2_yellow_0(X44,u1_struct_0(X44))
        | v2_struct_0(X44)
        | ~ v5_orders_2(X44)
        | ~ v1_yellow_0(X44)
        | ~ l1_orders_2(X44) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t42_yellow_0])])])])).

cnf(c_0_45,plain,
    ( X1 = X2
    | v1_subset_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_47,negated_conjecture,
    ( r2_lattice3(esk6_0,X1,esk1_2(u1_struct_0(esk6_0),X2))
    | r2_hidden(esk2_3(esk6_0,X1,esk1_2(u1_struct_0(esk6_0),X2)),X1)
    | r1_tarski(u1_struct_0(esk6_0),X2) ),
    inference(spm,[status(thm)],[c_0_36,c_0_27])).

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

cnf(c_0_50,negated_conjecture,
    ( r1_orders_2(esk6_0,k1_yellow_0(esk6_0,X1),X2)
    | k1_yellow_0(esk6_0,X1) != k1_yellow_0(esk6_0,X3)
    | ~ r1_yellow_0(esk6_0,X3)
    | ~ r2_lattice3(esk6_0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_32]),c_0_27])])).

cnf(c_0_51,negated_conjecture,
    ( r2_lattice3(esk6_0,X1,k1_yellow_0(esk6_0,X2))
    | ~ r1_tarski(X1,esk2_3(esk6_0,X1,k1_yellow_0(esk6_0,X2))) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_52,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_53,plain,
    ( r1_yellow_0(X1,k1_xboole_0)
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_yellow_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_54,negated_conjecture,
    ( v1_yellow_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_55,negated_conjecture,
    ( v5_orders_2(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_56,negated_conjecture,
    ( ~ v2_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(k3_yellow_0(esk6_0),esk7_0)
    | ~ v1_subset_1(esk7_0,u1_struct_0(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_58,negated_conjecture,
    ( u1_struct_0(esk6_0) = esk7_0
    | v1_subset_1(esk7_0,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

fof(c_0_59,plain,(
    ! [X35] :
      ( ~ l1_orders_2(X35)
      | k3_yellow_0(X35) = k1_yellow_0(X35,k1_xboole_0) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_yellow_0])])).

cnf(c_0_60,negated_conjecture,
    ( r2_lattice3(esk6_0,X1,esk1_2(u1_struct_0(esk6_0),X2))
    | r1_tarski(u1_struct_0(esk6_0),X2)
    | ~ r1_tarski(X1,esk2_3(esk6_0,X1,esk1_2(u1_struct_0(esk6_0),X2))) ),
    inference(spm,[status(thm)],[c_0_40,c_0_47])).

cnf(c_0_61,plain,
    ( r2_hidden(X1,X2)
    | ~ v13_waybel_0(X2,X3)
    | ~ r1_orders_2(X3,X4,X1)
    | ~ l1_orders_2(X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ r2_hidden(X4,X2) ),
    inference(csr,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_62,negated_conjecture,
    ( v13_waybel_0(esk7_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_63,negated_conjecture,
    ( r1_orders_2(esk6_0,k1_yellow_0(esk6_0,X1),k1_yellow_0(esk6_0,X2))
    | k1_yellow_0(esk6_0,X1) != k1_yellow_0(esk6_0,X3)
    | ~ r1_yellow_0(esk6_0,X3)
    | ~ r2_lattice3(esk6_0,X3,k1_yellow_0(esk6_0,X2)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_32])).

cnf(c_0_64,negated_conjecture,
    ( r2_lattice3(esk6_0,k1_xboole_0,k1_yellow_0(esk6_0,X1)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_65,negated_conjecture,
    ( r1_yellow_0(esk6_0,k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55]),c_0_27])]),c_0_56])).

cnf(c_0_66,negated_conjecture,
    ( u1_struct_0(esk6_0) = esk7_0
    | r2_hidden(k3_yellow_0(esk6_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_67,plain,
    ( k3_yellow_0(X1) = k1_yellow_0(X1,k1_xboole_0)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_68,negated_conjecture,
    ( r1_orders_2(esk6_0,k1_yellow_0(esk6_0,X1),esk1_2(u1_struct_0(esk6_0),X2))
    | r1_tarski(u1_struct_0(esk6_0),X2)
    | k1_yellow_0(esk6_0,X1) != k1_yellow_0(esk6_0,X3)
    | ~ r1_yellow_0(esk6_0,X3)
    | ~ r2_lattice3(esk6_0,X3,esk1_2(u1_struct_0(esk6_0),X2)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_29])).

cnf(c_0_69,negated_conjecture,
    ( r2_lattice3(esk6_0,k1_xboole_0,esk1_2(u1_struct_0(esk6_0),X1))
    | r1_tarski(u1_struct_0(esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_60,c_0_52])).

cnf(c_0_70,negated_conjecture,
    ( r2_hidden(X1,esk7_0)
    | ~ r1_orders_2(esk6_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0))
    | ~ r2_hidden(X2,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_46]),c_0_62]),c_0_27])])).

cnf(c_0_71,negated_conjecture,
    ( r1_orders_2(esk6_0,k1_yellow_0(esk6_0,X1),k1_yellow_0(esk6_0,X2))
    | k1_yellow_0(esk6_0,X1) != k1_yellow_0(esk6_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65])])).

fof(c_0_72,plain,(
    ! [X21,X22] :
      ( ~ m1_subset_1(X21,X22)
      | v1_xboole_0(X22)
      | r2_hidden(X21,X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_73,negated_conjecture,
    ( u1_struct_0(esk6_0) = esk7_0
    | m1_subset_1(k3_yellow_0(esk6_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_66])).

cnf(c_0_74,negated_conjecture,
    ( k3_yellow_0(esk6_0) = k1_yellow_0(esk6_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_67,c_0_27])).

cnf(c_0_75,negated_conjecture,
    ( r1_orders_2(esk6_0,k1_yellow_0(esk6_0,X1),esk1_2(u1_struct_0(esk6_0),X2))
    | r1_tarski(u1_struct_0(esk6_0),X2)
    | k1_yellow_0(esk6_0,X1) != k1_yellow_0(esk6_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_65])])).

cnf(c_0_76,negated_conjecture,
    ( r2_hidden(k1_yellow_0(esk6_0,X1),esk7_0)
    | ~ r1_orders_2(esk6_0,X2,k1_yellow_0(esk6_0,X1))
    | ~ r2_hidden(X2,esk7_0) ),
    inference(spm,[status(thm)],[c_0_70,c_0_32])).

cnf(c_0_77,negated_conjecture,
    ( r1_orders_2(esk6_0,k1_yellow_0(esk6_0,k1_xboole_0),k1_yellow_0(esk6_0,X1)) ),
    inference(er,[status(thm)],[c_0_71])).

cnf(c_0_78,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_79,negated_conjecture,
    ( u1_struct_0(esk6_0) = esk7_0
    | m1_subset_1(k1_yellow_0(esk6_0,k1_xboole_0),esk7_0) ),
    inference(rw,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_80,negated_conjecture,
    ( ~ v1_xboole_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_81,negated_conjecture,
    ( r2_hidden(esk1_2(u1_struct_0(esk6_0),X1),esk7_0)
    | r1_tarski(u1_struct_0(esk6_0),X1)
    | ~ r1_orders_2(esk6_0,X2,esk1_2(u1_struct_0(esk6_0),X1))
    | ~ r2_hidden(X2,esk7_0) ),
    inference(spm,[status(thm)],[c_0_70,c_0_29])).

cnf(c_0_82,negated_conjecture,
    ( r1_orders_2(esk6_0,k1_yellow_0(esk6_0,k1_xboole_0),esk1_2(u1_struct_0(esk6_0),X1))
    | r1_tarski(u1_struct_0(esk6_0),X1) ),
    inference(er,[status(thm)],[c_0_75])).

cnf(c_0_83,negated_conjecture,
    ( r2_hidden(k1_yellow_0(esk6_0,X1),esk7_0)
    | ~ r2_hidden(k1_yellow_0(esk6_0,k1_xboole_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_84,negated_conjecture,
    ( u1_struct_0(esk6_0) = esk7_0
    | r2_hidden(k1_yellow_0(esk6_0,k1_xboole_0),esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_80])).

fof(c_0_85,plain,(
    ! [X11,X12] :
      ( ( r1_tarski(X11,X12)
        | X11 != X12 )
      & ( r1_tarski(X12,X11)
        | X11 != X12 )
      & ( ~ r1_tarski(X11,X12)
        | ~ r1_tarski(X12,X11)
        | X11 = X12 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_86,plain,(
    ! [X14] : m1_subset_1(k2_subset_1(X14),k1_zfmisc_1(X14)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_87,plain,(
    ! [X13] : k2_subset_1(X13) = X13 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

cnf(c_0_88,negated_conjecture,
    ( r2_hidden(esk1_2(u1_struct_0(esk6_0),X1),esk7_0)
    | r1_tarski(u1_struct_0(esk6_0),X1)
    | ~ r2_hidden(k1_yellow_0(esk6_0,k1_xboole_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_89,negated_conjecture,
    ( u1_struct_0(esk6_0) = esk7_0
    | r2_hidden(k1_yellow_0(esk6_0,X1),esk7_0) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_90,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

cnf(c_0_91,negated_conjecture,
    ( r1_tarski(esk7_0,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_46])).

cnf(c_0_92,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_86])).

cnf(c_0_93,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_87])).

cnf(c_0_94,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_95,negated_conjecture,
    ( u1_struct_0(esk6_0) = esk7_0
    | r2_hidden(esk1_2(u1_struct_0(esk6_0),X1),esk7_0)
    | r1_tarski(u1_struct_0(esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_96,negated_conjecture,
    ( u1_struct_0(esk6_0) = esk7_0
    | ~ r1_tarski(u1_struct_0(esk6_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_97,negated_conjecture,
    ( v1_subset_1(esk7_0,u1_struct_0(esk6_0))
    | ~ r2_hidden(k3_yellow_0(esk6_0),esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_98,plain,
    ( ~ v1_subset_1(X1,X2)
    | X1 != X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_99,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_92,c_0_93])).

cnf(c_0_100,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk6_0))
    | r2_hidden(k1_yellow_0(esk6_0,X1),u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_78,c_0_32])).

cnf(c_0_101,negated_conjecture,
    ( u1_struct_0(esk6_0) = esk7_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_96])).

cnf(c_0_102,negated_conjecture,
    ( v1_subset_1(esk7_0,u1_struct_0(esk6_0))
    | ~ r2_hidden(k1_yellow_0(esk6_0,k1_xboole_0),esk7_0) ),
    inference(rw,[status(thm)],[c_0_97,c_0_74])).

cnf(c_0_103,plain,
    ( ~ v1_subset_1(X1,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_98]),c_0_99])])).

cnf(c_0_104,negated_conjecture,
    ( r2_hidden(k1_yellow_0(esk6_0,X1),esk7_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_100,c_0_101]),c_0_101]),c_0_80])).

cnf(c_0_105,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_102,c_0_101]),c_0_103]),c_0_104])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:30:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.21/0.53  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_PS_S0S
% 0.21/0.53  # and selection function SelectComplexG.
% 0.21/0.53  #
% 0.21/0.53  # Preprocessing time       : 0.029 s
% 0.21/0.53  # Presaturation interreduction done
% 0.21/0.53  
% 0.21/0.53  # Proof found!
% 0.21/0.53  # SZS status Theorem
% 0.21/0.53  # SZS output start CNFRefutation
% 0.21/0.53  fof(t8_waybel_7, conjecture, ![X1]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&v1_yellow_0(X1))&l1_orders_2(X1))=>![X2]:((((~(v1_xboole_0(X2))&v2_waybel_0(X2,X1))&v13_waybel_0(X2,X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v1_subset_1(X2,u1_struct_0(X1))<=>~(r2_hidden(k3_yellow_0(X1),X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_waybel_7)).
% 0.21/0.53  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 0.21/0.53  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.21/0.53  fof(dt_k1_yellow_0, axiom, ![X1, X2]:(l1_orders_2(X1)=>m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_yellow_0)).
% 0.21/0.53  fof(d9_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X2)=>r1_orders_2(X1,X4,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_lattice3)).
% 0.21/0.53  fof(d9_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_yellow_0(X1,X2)=>(X3=k1_yellow_0(X1,X2)<=>(r2_lattice3(X1,X2,X3)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X4)=>r1_orders_2(X1,X3,X4)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_yellow_0)).
% 0.21/0.53  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.21/0.53  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.21/0.53  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 0.21/0.53  fof(d7_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(v1_subset_1(X2,X1)<=>X2!=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 0.21/0.53  fof(d20_waybel_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v13_waybel_0(X2,X1)<=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((r2_hidden(X3,X2)&r1_orders_2(X1,X3,X4))=>r2_hidden(X4,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d20_waybel_0)).
% 0.21/0.53  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 0.21/0.53  fof(t42_yellow_0, axiom, ![X1]:((((~(v2_struct_0(X1))&v5_orders_2(X1))&v1_yellow_0(X1))&l1_orders_2(X1))=>(r1_yellow_0(X1,k1_xboole_0)&r2_yellow_0(X1,u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_yellow_0)).
% 0.21/0.53  fof(d11_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>k3_yellow_0(X1)=k1_yellow_0(X1,k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_yellow_0)).
% 0.21/0.53  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 0.21/0.53  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.21/0.53  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.21/0.53  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 0.21/0.53  fof(c_0_18, negated_conjecture, ~(![X1]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&v1_yellow_0(X1))&l1_orders_2(X1))=>![X2]:((((~(v1_xboole_0(X2))&v2_waybel_0(X2,X1))&v13_waybel_0(X2,X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v1_subset_1(X2,u1_struct_0(X1))<=>~(r2_hidden(k3_yellow_0(X1),X2)))))), inference(assume_negation,[status(cth)],[t8_waybel_7])).
% 0.21/0.53  fof(c_0_19, plain, ![X19, X20]:(~r2_hidden(X19,X20)|m1_subset_1(X19,X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.21/0.53  fof(c_0_20, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.21/0.53  fof(c_0_21, plain, ![X41, X42]:(~l1_orders_2(X41)|m1_subset_1(k1_yellow_0(X41,X42),u1_struct_0(X41))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_yellow_0])])).
% 0.21/0.53  fof(c_0_22, negated_conjecture, ((((((~v2_struct_0(esk6_0)&v3_orders_2(esk6_0))&v4_orders_2(esk6_0))&v5_orders_2(esk6_0))&v1_yellow_0(esk6_0))&l1_orders_2(esk6_0))&((((~v1_xboole_0(esk7_0)&v2_waybel_0(esk7_0,esk6_0))&v13_waybel_0(esk7_0,esk6_0))&m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk6_0))))&((~v1_subset_1(esk7_0,u1_struct_0(esk6_0))|r2_hidden(k3_yellow_0(esk6_0),esk7_0))&(v1_subset_1(esk7_0,u1_struct_0(esk6_0))|~r2_hidden(k3_yellow_0(esk6_0),esk7_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_18])])])])).
% 0.21/0.53  fof(c_0_23, plain, ![X30, X31, X32, X33]:((~r2_lattice3(X30,X31,X32)|(~m1_subset_1(X33,u1_struct_0(X30))|(~r2_hidden(X33,X31)|r1_orders_2(X30,X33,X32)))|~m1_subset_1(X32,u1_struct_0(X30))|~l1_orders_2(X30))&((m1_subset_1(esk2_3(X30,X31,X32),u1_struct_0(X30))|r2_lattice3(X30,X31,X32)|~m1_subset_1(X32,u1_struct_0(X30))|~l1_orders_2(X30))&((r2_hidden(esk2_3(X30,X31,X32),X31)|r2_lattice3(X30,X31,X32)|~m1_subset_1(X32,u1_struct_0(X30))|~l1_orders_2(X30))&(~r1_orders_2(X30,esk2_3(X30,X31,X32),X32)|r2_lattice3(X30,X31,X32)|~m1_subset_1(X32,u1_struct_0(X30))|~l1_orders_2(X30))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).
% 0.21/0.53  cnf(c_0_24, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.53  cnf(c_0_25, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.53  cnf(c_0_26, plain, (m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.53  cnf(c_0_27, negated_conjecture, (l1_orders_2(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.53  cnf(c_0_28, plain, (r2_hidden(esk2_3(X1,X2,X3),X2)|r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.53  cnf(c_0_29, plain, (m1_subset_1(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.21/0.53  fof(c_0_30, plain, ![X36, X37, X38, X39]:(((r2_lattice3(X36,X37,X38)|X38!=k1_yellow_0(X36,X37)|~r1_yellow_0(X36,X37)|~m1_subset_1(X38,u1_struct_0(X36))|~l1_orders_2(X36))&(~m1_subset_1(X39,u1_struct_0(X36))|(~r2_lattice3(X36,X37,X39)|r1_orders_2(X36,X38,X39))|X38!=k1_yellow_0(X36,X37)|~r1_yellow_0(X36,X37)|~m1_subset_1(X38,u1_struct_0(X36))|~l1_orders_2(X36)))&((m1_subset_1(esk3_3(X36,X37,X38),u1_struct_0(X36))|~r2_lattice3(X36,X37,X38)|X38=k1_yellow_0(X36,X37)|~r1_yellow_0(X36,X37)|~m1_subset_1(X38,u1_struct_0(X36))|~l1_orders_2(X36))&((r2_lattice3(X36,X37,esk3_3(X36,X37,X38))|~r2_lattice3(X36,X37,X38)|X38=k1_yellow_0(X36,X37)|~r1_yellow_0(X36,X37)|~m1_subset_1(X38,u1_struct_0(X36))|~l1_orders_2(X36))&(~r1_orders_2(X36,X38,esk3_3(X36,X37,X38))|~r2_lattice3(X36,X37,X38)|X38=k1_yellow_0(X36,X37)|~r1_yellow_0(X36,X37)|~m1_subset_1(X38,u1_struct_0(X36))|~l1_orders_2(X36))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_yellow_0])])])])])).
% 0.21/0.53  fof(c_0_31, plain, ![X28, X29]:(~r2_hidden(X28,X29)|~r1_tarski(X29,X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.21/0.53  cnf(c_0_32, negated_conjecture, (m1_subset_1(k1_yellow_0(esk6_0,X1),u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.21/0.53  fof(c_0_33, plain, ![X23, X24]:((~m1_subset_1(X23,k1_zfmisc_1(X24))|r1_tarski(X23,X24))&(~r1_tarski(X23,X24)|m1_subset_1(X23,k1_zfmisc_1(X24)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.21/0.53  fof(c_0_34, plain, ![X18]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X18)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.21/0.53  fof(c_0_35, plain, ![X51, X52]:((~v1_subset_1(X52,X51)|X52!=X51|~m1_subset_1(X52,k1_zfmisc_1(X51)))&(X52=X51|v1_subset_1(X52,X51)|~m1_subset_1(X52,k1_zfmisc_1(X51)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).
% 0.21/0.53  cnf(c_0_36, plain, (r2_lattice3(X1,X2,esk1_2(u1_struct_0(X1),X3))|r2_hidden(esk2_3(X1,X2,esk1_2(u1_struct_0(X1),X3)),X2)|r1_tarski(u1_struct_0(X1),X3)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.21/0.53  fof(c_0_37, plain, ![X45, X46, X47, X48]:((~v13_waybel_0(X46,X45)|(~m1_subset_1(X47,u1_struct_0(X45))|(~m1_subset_1(X48,u1_struct_0(X45))|(~r2_hidden(X47,X46)|~r1_orders_2(X45,X47,X48)|r2_hidden(X48,X46))))|~m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X45)))|~l1_orders_2(X45))&((m1_subset_1(esk4_2(X45,X46),u1_struct_0(X45))|v13_waybel_0(X46,X45)|~m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X45)))|~l1_orders_2(X45))&((m1_subset_1(esk5_2(X45,X46),u1_struct_0(X45))|v13_waybel_0(X46,X45)|~m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X45)))|~l1_orders_2(X45))&(((r2_hidden(esk4_2(X45,X46),X46)|v13_waybel_0(X46,X45)|~m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X45)))|~l1_orders_2(X45))&(r1_orders_2(X45,esk4_2(X45,X46),esk5_2(X45,X46))|v13_waybel_0(X46,X45)|~m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X45)))|~l1_orders_2(X45)))&(~r2_hidden(esk5_2(X45,X46),X46)|v13_waybel_0(X46,X45)|~m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X45)))|~l1_orders_2(X45)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d20_waybel_0])])])])])).
% 0.21/0.53  fof(c_0_38, plain, ![X25, X26, X27]:(~r2_hidden(X25,X26)|~m1_subset_1(X26,k1_zfmisc_1(X27))|m1_subset_1(X25,X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.21/0.53  cnf(c_0_39, plain, (r1_orders_2(X2,X4,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~r2_lattice3(X2,X3,X1)|X4!=k1_yellow_0(X2,X3)|~r1_yellow_0(X2,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.21/0.53  cnf(c_0_40, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.21/0.53  cnf(c_0_41, negated_conjecture, (r2_lattice3(esk6_0,X1,k1_yellow_0(esk6_0,X2))|r2_hidden(esk2_3(esk6_0,X1,k1_yellow_0(esk6_0,X2)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_32]), c_0_27])])).
% 0.21/0.53  cnf(c_0_42, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.21/0.53  cnf(c_0_43, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.21/0.53  fof(c_0_44, plain, ![X44]:((r1_yellow_0(X44,k1_xboole_0)|(v2_struct_0(X44)|~v5_orders_2(X44)|~v1_yellow_0(X44)|~l1_orders_2(X44)))&(r2_yellow_0(X44,u1_struct_0(X44))|(v2_struct_0(X44)|~v5_orders_2(X44)|~v1_yellow_0(X44)|~l1_orders_2(X44)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t42_yellow_0])])])])).
% 0.21/0.53  cnf(c_0_45, plain, (X1=X2|v1_subset_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.21/0.53  cnf(c_0_46, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.53  cnf(c_0_47, negated_conjecture, (r2_lattice3(esk6_0,X1,esk1_2(u1_struct_0(esk6_0),X2))|r2_hidden(esk2_3(esk6_0,X1,esk1_2(u1_struct_0(esk6_0),X2)),X1)|r1_tarski(u1_struct_0(esk6_0),X2)), inference(spm,[status(thm)],[c_0_36, c_0_27])).
% 0.21/0.53  cnf(c_0_48, plain, (r2_hidden(X4,X1)|~v13_waybel_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X2))|~m1_subset_1(X4,u1_struct_0(X2))|~r2_hidden(X3,X1)|~r1_orders_2(X2,X3,X4)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.21/0.53  cnf(c_0_49, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.21/0.53  cnf(c_0_50, negated_conjecture, (r1_orders_2(esk6_0,k1_yellow_0(esk6_0,X1),X2)|k1_yellow_0(esk6_0,X1)!=k1_yellow_0(esk6_0,X3)|~r1_yellow_0(esk6_0,X3)|~r2_lattice3(esk6_0,X3,X2)|~m1_subset_1(X2,u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_32]), c_0_27])])).
% 0.21/0.53  cnf(c_0_51, negated_conjecture, (r2_lattice3(esk6_0,X1,k1_yellow_0(esk6_0,X2))|~r1_tarski(X1,esk2_3(esk6_0,X1,k1_yellow_0(esk6_0,X2)))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.21/0.53  cnf(c_0_52, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.21/0.53  cnf(c_0_53, plain, (r1_yellow_0(X1,k1_xboole_0)|v2_struct_0(X1)|~v5_orders_2(X1)|~v1_yellow_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.21/0.53  cnf(c_0_54, negated_conjecture, (v1_yellow_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.53  cnf(c_0_55, negated_conjecture, (v5_orders_2(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.53  cnf(c_0_56, negated_conjecture, (~v2_struct_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.53  cnf(c_0_57, negated_conjecture, (r2_hidden(k3_yellow_0(esk6_0),esk7_0)|~v1_subset_1(esk7_0,u1_struct_0(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.53  cnf(c_0_58, negated_conjecture, (u1_struct_0(esk6_0)=esk7_0|v1_subset_1(esk7_0,u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.21/0.53  fof(c_0_59, plain, ![X35]:(~l1_orders_2(X35)|k3_yellow_0(X35)=k1_yellow_0(X35,k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_yellow_0])])).
% 0.21/0.53  cnf(c_0_60, negated_conjecture, (r2_lattice3(esk6_0,X1,esk1_2(u1_struct_0(esk6_0),X2))|r1_tarski(u1_struct_0(esk6_0),X2)|~r1_tarski(X1,esk2_3(esk6_0,X1,esk1_2(u1_struct_0(esk6_0),X2)))), inference(spm,[status(thm)],[c_0_40, c_0_47])).
% 0.21/0.53  cnf(c_0_61, plain, (r2_hidden(X1,X2)|~v13_waybel_0(X2,X3)|~r1_orders_2(X3,X4,X1)|~l1_orders_2(X3)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~m1_subset_1(X1,u1_struct_0(X3))|~r2_hidden(X4,X2)), inference(csr,[status(thm)],[c_0_48, c_0_49])).
% 0.21/0.53  cnf(c_0_62, negated_conjecture, (v13_waybel_0(esk7_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.53  cnf(c_0_63, negated_conjecture, (r1_orders_2(esk6_0,k1_yellow_0(esk6_0,X1),k1_yellow_0(esk6_0,X2))|k1_yellow_0(esk6_0,X1)!=k1_yellow_0(esk6_0,X3)|~r1_yellow_0(esk6_0,X3)|~r2_lattice3(esk6_0,X3,k1_yellow_0(esk6_0,X2))), inference(spm,[status(thm)],[c_0_50, c_0_32])).
% 0.21/0.53  cnf(c_0_64, negated_conjecture, (r2_lattice3(esk6_0,k1_xboole_0,k1_yellow_0(esk6_0,X1))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.21/0.53  cnf(c_0_65, negated_conjecture, (r1_yellow_0(esk6_0,k1_xboole_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55]), c_0_27])]), c_0_56])).
% 0.21/0.53  cnf(c_0_66, negated_conjecture, (u1_struct_0(esk6_0)=esk7_0|r2_hidden(k3_yellow_0(esk6_0),esk7_0)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.21/0.53  cnf(c_0_67, plain, (k3_yellow_0(X1)=k1_yellow_0(X1,k1_xboole_0)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.21/0.53  cnf(c_0_68, negated_conjecture, (r1_orders_2(esk6_0,k1_yellow_0(esk6_0,X1),esk1_2(u1_struct_0(esk6_0),X2))|r1_tarski(u1_struct_0(esk6_0),X2)|k1_yellow_0(esk6_0,X1)!=k1_yellow_0(esk6_0,X3)|~r1_yellow_0(esk6_0,X3)|~r2_lattice3(esk6_0,X3,esk1_2(u1_struct_0(esk6_0),X2))), inference(spm,[status(thm)],[c_0_50, c_0_29])).
% 0.21/0.53  cnf(c_0_69, negated_conjecture, (r2_lattice3(esk6_0,k1_xboole_0,esk1_2(u1_struct_0(esk6_0),X1))|r1_tarski(u1_struct_0(esk6_0),X1)), inference(spm,[status(thm)],[c_0_60, c_0_52])).
% 0.21/0.53  cnf(c_0_70, negated_conjecture, (r2_hidden(X1,esk7_0)|~r1_orders_2(esk6_0,X2,X1)|~m1_subset_1(X1,u1_struct_0(esk6_0))|~r2_hidden(X2,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_46]), c_0_62]), c_0_27])])).
% 0.21/0.53  cnf(c_0_71, negated_conjecture, (r1_orders_2(esk6_0,k1_yellow_0(esk6_0,X1),k1_yellow_0(esk6_0,X2))|k1_yellow_0(esk6_0,X1)!=k1_yellow_0(esk6_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_65])])).
% 0.21/0.53  fof(c_0_72, plain, ![X21, X22]:(~m1_subset_1(X21,X22)|(v1_xboole_0(X22)|r2_hidden(X21,X22))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.21/0.53  cnf(c_0_73, negated_conjecture, (u1_struct_0(esk6_0)=esk7_0|m1_subset_1(k3_yellow_0(esk6_0),esk7_0)), inference(spm,[status(thm)],[c_0_24, c_0_66])).
% 0.21/0.53  cnf(c_0_74, negated_conjecture, (k3_yellow_0(esk6_0)=k1_yellow_0(esk6_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_67, c_0_27])).
% 0.21/0.53  cnf(c_0_75, negated_conjecture, (r1_orders_2(esk6_0,k1_yellow_0(esk6_0,X1),esk1_2(u1_struct_0(esk6_0),X2))|r1_tarski(u1_struct_0(esk6_0),X2)|k1_yellow_0(esk6_0,X1)!=k1_yellow_0(esk6_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_65])])).
% 0.21/0.53  cnf(c_0_76, negated_conjecture, (r2_hidden(k1_yellow_0(esk6_0,X1),esk7_0)|~r1_orders_2(esk6_0,X2,k1_yellow_0(esk6_0,X1))|~r2_hidden(X2,esk7_0)), inference(spm,[status(thm)],[c_0_70, c_0_32])).
% 0.21/0.53  cnf(c_0_77, negated_conjecture, (r1_orders_2(esk6_0,k1_yellow_0(esk6_0,k1_xboole_0),k1_yellow_0(esk6_0,X1))), inference(er,[status(thm)],[c_0_71])).
% 0.21/0.53  cnf(c_0_78, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.21/0.53  cnf(c_0_79, negated_conjecture, (u1_struct_0(esk6_0)=esk7_0|m1_subset_1(k1_yellow_0(esk6_0,k1_xboole_0),esk7_0)), inference(rw,[status(thm)],[c_0_73, c_0_74])).
% 0.21/0.53  cnf(c_0_80, negated_conjecture, (~v1_xboole_0(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.53  cnf(c_0_81, negated_conjecture, (r2_hidden(esk1_2(u1_struct_0(esk6_0),X1),esk7_0)|r1_tarski(u1_struct_0(esk6_0),X1)|~r1_orders_2(esk6_0,X2,esk1_2(u1_struct_0(esk6_0),X1))|~r2_hidden(X2,esk7_0)), inference(spm,[status(thm)],[c_0_70, c_0_29])).
% 0.21/0.53  cnf(c_0_82, negated_conjecture, (r1_orders_2(esk6_0,k1_yellow_0(esk6_0,k1_xboole_0),esk1_2(u1_struct_0(esk6_0),X1))|r1_tarski(u1_struct_0(esk6_0),X1)), inference(er,[status(thm)],[c_0_75])).
% 0.21/0.53  cnf(c_0_83, negated_conjecture, (r2_hidden(k1_yellow_0(esk6_0,X1),esk7_0)|~r2_hidden(k1_yellow_0(esk6_0,k1_xboole_0),esk7_0)), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 0.21/0.53  cnf(c_0_84, negated_conjecture, (u1_struct_0(esk6_0)=esk7_0|r2_hidden(k1_yellow_0(esk6_0,k1_xboole_0),esk7_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_80])).
% 0.21/0.53  fof(c_0_85, plain, ![X11, X12]:(((r1_tarski(X11,X12)|X11!=X12)&(r1_tarski(X12,X11)|X11!=X12))&(~r1_tarski(X11,X12)|~r1_tarski(X12,X11)|X11=X12)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.21/0.53  fof(c_0_86, plain, ![X14]:m1_subset_1(k2_subset_1(X14),k1_zfmisc_1(X14)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.21/0.53  fof(c_0_87, plain, ![X13]:k2_subset_1(X13)=X13, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.21/0.53  cnf(c_0_88, negated_conjecture, (r2_hidden(esk1_2(u1_struct_0(esk6_0),X1),esk7_0)|r1_tarski(u1_struct_0(esk6_0),X1)|~r2_hidden(k1_yellow_0(esk6_0,k1_xboole_0),esk7_0)), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 0.21/0.53  cnf(c_0_89, negated_conjecture, (u1_struct_0(esk6_0)=esk7_0|r2_hidden(k1_yellow_0(esk6_0,X1),esk7_0)), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 0.21/0.53  cnf(c_0_90, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_85])).
% 0.21/0.53  cnf(c_0_91, negated_conjecture, (r1_tarski(esk7_0,u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_42, c_0_46])).
% 0.21/0.53  cnf(c_0_92, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_86])).
% 0.21/0.53  cnf(c_0_93, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_87])).
% 0.21/0.53  cnf(c_0_94, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.53  cnf(c_0_95, negated_conjecture, (u1_struct_0(esk6_0)=esk7_0|r2_hidden(esk1_2(u1_struct_0(esk6_0),X1),esk7_0)|r1_tarski(u1_struct_0(esk6_0),X1)), inference(spm,[status(thm)],[c_0_88, c_0_89])).
% 0.21/0.53  cnf(c_0_96, negated_conjecture, (u1_struct_0(esk6_0)=esk7_0|~r1_tarski(u1_struct_0(esk6_0),esk7_0)), inference(spm,[status(thm)],[c_0_90, c_0_91])).
% 0.21/0.53  cnf(c_0_97, negated_conjecture, (v1_subset_1(esk7_0,u1_struct_0(esk6_0))|~r2_hidden(k3_yellow_0(esk6_0),esk7_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.53  cnf(c_0_98, plain, (~v1_subset_1(X1,X2)|X1!=X2|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.21/0.53  cnf(c_0_99, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_92, c_0_93])).
% 0.21/0.53  cnf(c_0_100, negated_conjecture, (v1_xboole_0(u1_struct_0(esk6_0))|r2_hidden(k1_yellow_0(esk6_0,X1),u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_78, c_0_32])).
% 0.21/0.53  cnf(c_0_101, negated_conjecture, (u1_struct_0(esk6_0)=esk7_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_95]), c_0_96])).
% 0.21/0.53  cnf(c_0_102, negated_conjecture, (v1_subset_1(esk7_0,u1_struct_0(esk6_0))|~r2_hidden(k1_yellow_0(esk6_0,k1_xboole_0),esk7_0)), inference(rw,[status(thm)],[c_0_97, c_0_74])).
% 0.21/0.53  cnf(c_0_103, plain, (~v1_subset_1(X1,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_98]), c_0_99])])).
% 0.21/0.53  cnf(c_0_104, negated_conjecture, (r2_hidden(k1_yellow_0(esk6_0,X1),esk7_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_100, c_0_101]), c_0_101]), c_0_80])).
% 0.21/0.53  cnf(c_0_105, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_102, c_0_101]), c_0_103]), c_0_104])]), ['proof']).
% 0.21/0.53  # SZS output end CNFRefutation
% 0.21/0.53  # Proof object total steps             : 106
% 0.21/0.53  # Proof object clause steps            : 69
% 0.21/0.53  # Proof object formula steps           : 37
% 0.21/0.53  # Proof object conjectures             : 47
% 0.21/0.53  # Proof object clause conjectures      : 44
% 0.21/0.53  # Proof object formula conjectures     : 3
% 0.21/0.53  # Proof object initial clauses used    : 28
% 0.21/0.53  # Proof object initial formulas used   : 18
% 0.21/0.53  # Proof object generating inferences   : 34
% 0.21/0.53  # Proof object simplifying inferences  : 31
% 0.21/0.53  # Training examples: 0 positive, 0 negative
% 0.21/0.53  # Parsed axioms                        : 20
% 0.21/0.53  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.53  # Initial clauses                      : 50
% 0.21/0.53  # Removed in clause preprocessing      : 1
% 0.21/0.53  # Initial clauses in saturation        : 49
% 0.21/0.53  # Processed clauses                    : 1328
% 0.21/0.53  # ...of these trivial                  : 5
% 0.21/0.53  # ...subsumed                          : 548
% 0.21/0.53  # ...remaining for further processing  : 774
% 0.21/0.53  # Other redundant clauses eliminated   : 3
% 0.21/0.53  # Clauses deleted for lack of memory   : 0
% 0.21/0.53  # Backward-subsumed                    : 41
% 0.21/0.53  # Backward-rewritten                   : 348
% 0.21/0.53  # Generated clauses                    : 3368
% 0.21/0.53  # ...of the previous two non-trivial   : 3373
% 0.21/0.53  # Contextual simplify-reflections      : 12
% 0.21/0.53  # Paramodulations                      : 3355
% 0.21/0.53  # Factorizations                       : 1
% 0.21/0.53  # Equation resolutions                 : 12
% 0.21/0.53  # Propositional unsat checks           : 0
% 0.21/0.53  #    Propositional check models        : 0
% 0.21/0.53  #    Propositional check unsatisfiable : 0
% 0.21/0.53  #    Propositional clauses             : 0
% 0.21/0.53  #    Propositional clauses after purity: 0
% 0.21/0.53  #    Propositional unsat core size     : 0
% 0.21/0.53  #    Propositional preprocessing time  : 0.000
% 0.21/0.53  #    Propositional encoding time       : 0.000
% 0.21/0.53  #    Propositional solver time         : 0.000
% 0.21/0.53  #    Success case prop preproc time    : 0.000
% 0.21/0.53  #    Success case prop encoding time   : 0.000
% 0.21/0.53  #    Success case prop solver time     : 0.000
% 0.21/0.53  # Current number of processed clauses  : 334
% 0.21/0.53  #    Positive orientable unit clauses  : 19
% 0.21/0.53  #    Positive unorientable unit clauses: 0
% 0.21/0.53  #    Negative unit clauses             : 3
% 0.21/0.53  #    Non-unit-clauses                  : 312
% 0.21/0.53  # Current number of unprocessed clauses: 2081
% 0.21/0.53  # ...number of literals in the above   : 11000
% 0.21/0.53  # Current number of archived formulas  : 0
% 0.21/0.53  # Current number of archived clauses   : 438
% 0.21/0.53  # Clause-clause subsumption calls (NU) : 52701
% 0.21/0.53  # Rec. Clause-clause subsumption calls : 10023
% 0.21/0.53  # Non-unit clause-clause subsumptions  : 601
% 0.21/0.53  # Unit Clause-clause subsumption calls : 246
% 0.21/0.53  # Rewrite failures with RHS unbound    : 0
% 0.21/0.53  # BW rewrite match attempts            : 22
% 0.21/0.53  # BW rewrite match successes           : 7
% 0.21/0.53  # Condensation attempts                : 0
% 0.21/0.53  # Condensation successes               : 0
% 0.21/0.53  # Termbank termtop insertions          : 100201
% 0.21/0.53  
% 0.21/0.53  # -------------------------------------------------
% 0.21/0.53  # User time                : 0.183 s
% 0.21/0.53  # System time              : 0.008 s
% 0.21/0.53  # Total time               : 0.191 s
% 0.21/0.53  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
