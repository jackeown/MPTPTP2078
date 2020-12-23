%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:26 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 789 expanded)
%              Number of clauses        :   65 ( 334 expanded)
%              Number of leaves         :   17 ( 197 expanded)
%              Depth                    :   14
%              Number of atoms          :  387 (4250 expanded)
%              Number of equality atoms :   44 ( 279 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(rc3_subset_1,axiom,(
    ! [X1] :
    ? [X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
      & ~ v1_subset_1(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_subset_1)).

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

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(dt_k1_yellow_0,axiom,(
    ! [X1,X2] :
      ( l1_orders_2(X1)
     => m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_0)).

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

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

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

fof(t42_yellow_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v5_orders_2(X1)
        & v1_yellow_0(X1)
        & l1_orders_2(X1) )
     => ( r1_yellow_0(X1,k1_xboole_0)
        & r2_yellow_0(X1,u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_yellow_0)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(d11_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => k3_yellow_0(X1) = k1_yellow_0(X1,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_yellow_0)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(c_0_17,plain,(
    ! [X51,X52] :
      ( ( ~ v1_subset_1(X52,X51)
        | X52 != X51
        | ~ m1_subset_1(X52,k1_zfmisc_1(X51)) )
      & ( X52 = X51
        | v1_subset_1(X52,X51)
        | ~ m1_subset_1(X52,k1_zfmisc_1(X51)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).

fof(c_0_18,plain,(
    ! [X19] :
      ( m1_subset_1(esk3_1(X19),k1_zfmisc_1(X19))
      & ~ v1_subset_1(esk3_1(X19),X19) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[rc3_subset_1])])])).

cnf(c_0_19,plain,
    ( X1 = X2
    | v1_subset_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_20,plain,
    ( m1_subset_1(esk3_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_21,plain,
    ( ~ v1_subset_1(esk3_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_22,plain,(
    ! [X15,X16,X17] :
      ( ( m1_subset_1(esk2_3(X15,X16,X17),X15)
        | X16 = X17
        | ~ m1_subset_1(X17,k1_zfmisc_1(X15))
        | ~ m1_subset_1(X16,k1_zfmisc_1(X15)) )
      & ( ~ r2_hidden(esk2_3(X15,X16,X17),X16)
        | ~ r2_hidden(esk2_3(X15,X16,X17),X17)
        | X16 = X17
        | ~ m1_subset_1(X17,k1_zfmisc_1(X15))
        | ~ m1_subset_1(X16,k1_zfmisc_1(X15)) )
      & ( r2_hidden(esk2_3(X15,X16,X17),X16)
        | r2_hidden(esk2_3(X15,X16,X17),X17)
        | X16 = X17
        | ~ m1_subset_1(X17,k1_zfmisc_1(X15))
        | ~ m1_subset_1(X16,k1_zfmisc_1(X15)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_subset_1])])])])])).

cnf(c_0_23,plain,
    ( esk3_1(X1) = X1 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])).

fof(c_0_24,negated_conjecture,(
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

fof(c_0_25,plain,(
    ! [X11,X12,X13] :
      ( ~ m1_subset_1(X12,k1_zfmisc_1(X11))
      | ~ r2_hidden(X13,X12)
      | r2_hidden(X13,X11) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

fof(c_0_26,plain,(
    ! [X14] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X14)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_27,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),X1)
    | X2 = X3
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_20,c_0_23])).

fof(c_0_29,negated_conjecture,
    ( ~ v2_struct_0(esk8_0)
    & v3_orders_2(esk8_0)
    & v4_orders_2(esk8_0)
    & v5_orders_2(esk8_0)
    & v1_yellow_0(esk8_0)
    & l1_orders_2(esk8_0)
    & ~ v1_xboole_0(esk9_0)
    & v2_waybel_0(esk9_0,esk8_0)
    & v13_waybel_0(esk9_0,esk8_0)
    & m1_subset_1(esk9_0,k1_zfmisc_1(u1_struct_0(esk8_0)))
    & ( ~ v1_subset_1(esk9_0,u1_struct_0(esk8_0))
      | r2_hidden(k3_yellow_0(esk8_0),esk9_0) )
    & ( v1_subset_1(esk9_0,u1_struct_0(esk8_0))
      | ~ r2_hidden(k3_yellow_0(esk8_0),esk9_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_24])])])])).

cnf(c_0_30,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_32,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_33,plain,(
    ! [X41,X42] :
      ( ~ l1_orders_2(X41)
      | m1_subset_1(k1_yellow_0(X41,X42),u1_struct_0(X41)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_yellow_0])])).

fof(c_0_34,plain,(
    ! [X30,X31,X32,X33] :
      ( ( ~ r2_lattice3(X30,X31,X32)
        | ~ m1_subset_1(X33,u1_struct_0(X30))
        | ~ r2_hidden(X33,X31)
        | r1_orders_2(X30,X33,X32)
        | ~ m1_subset_1(X32,u1_struct_0(X30))
        | ~ l1_orders_2(X30) )
      & ( m1_subset_1(esk4_3(X30,X31,X32),u1_struct_0(X30))
        | r2_lattice3(X30,X31,X32)
        | ~ m1_subset_1(X32,u1_struct_0(X30))
        | ~ l1_orders_2(X30) )
      & ( r2_hidden(esk4_3(X30,X31,X32),X31)
        | r2_lattice3(X30,X31,X32)
        | ~ m1_subset_1(X32,u1_struct_0(X30))
        | ~ l1_orders_2(X30) )
      & ( ~ r1_orders_2(X30,esk4_3(X30,X31,X32),X32)
        | r2_lattice3(X30,X31,X32)
        | ~ m1_subset_1(X32,u1_struct_0(X30))
        | ~ l1_orders_2(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).

cnf(c_0_35,plain,
    ( X1 = X2
    | m1_subset_1(esk2_3(X2,X1,X2),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_37,plain,(
    ! [X28,X29] :
      ( ~ r2_hidden(X28,X29)
      | ~ r1_tarski(X29,X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_39,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_40,plain,(
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
      & ( m1_subset_1(esk5_3(X36,X37,X38),u1_struct_0(X36))
        | ~ r2_lattice3(X36,X37,X38)
        | X38 = k1_yellow_0(X36,X37)
        | ~ r1_yellow_0(X36,X37)
        | ~ m1_subset_1(X38,u1_struct_0(X36))
        | ~ l1_orders_2(X36) )
      & ( r2_lattice3(X36,X37,esk5_3(X36,X37,X38))
        | ~ r2_lattice3(X36,X37,X38)
        | X38 = k1_yellow_0(X36,X37)
        | ~ r1_yellow_0(X36,X37)
        | ~ m1_subset_1(X38,u1_struct_0(X36))
        | ~ l1_orders_2(X36) )
      & ( ~ r1_orders_2(X36,X38,esk5_3(X36,X37,X38))
        | ~ r2_lattice3(X36,X37,X38)
        | X38 = k1_yellow_0(X36,X37)
        | ~ r1_yellow_0(X36,X37)
        | ~ m1_subset_1(X38,u1_struct_0(X36))
        | ~ l1_orders_2(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_yellow_0])])])])])).

cnf(c_0_41,plain,
    ( m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_42,negated_conjecture,
    ( l1_orders_2(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_43,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),X2)
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_44,negated_conjecture,
    ( u1_struct_0(esk8_0) = esk9_0
    | m1_subset_1(esk2_3(u1_struct_0(esk8_0),esk9_0,u1_struct_0(esk8_0)),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_45,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_46,plain,
    ( r2_hidden(esk1_2(k1_xboole_0,X1),X2)
    | r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_47,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_48,plain,(
    ! [X45,X46,X47,X48] :
      ( ( ~ v13_waybel_0(X46,X45)
        | ~ m1_subset_1(X47,u1_struct_0(X45))
        | ~ m1_subset_1(X48,u1_struct_0(X45))
        | ~ r2_hidden(X47,X46)
        | ~ r1_orders_2(X45,X47,X48)
        | r2_hidden(X48,X46)
        | ~ m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X45)))
        | ~ l1_orders_2(X45) )
      & ( m1_subset_1(esk6_2(X45,X46),u1_struct_0(X45))
        | v13_waybel_0(X46,X45)
        | ~ m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X45)))
        | ~ l1_orders_2(X45) )
      & ( m1_subset_1(esk7_2(X45,X46),u1_struct_0(X45))
        | v13_waybel_0(X46,X45)
        | ~ m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X45)))
        | ~ l1_orders_2(X45) )
      & ( r2_hidden(esk6_2(X45,X46),X46)
        | v13_waybel_0(X46,X45)
        | ~ m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X45)))
        | ~ l1_orders_2(X45) )
      & ( r1_orders_2(X45,esk6_2(X45,X46),esk7_2(X45,X46))
        | v13_waybel_0(X46,X45)
        | ~ m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X45)))
        | ~ l1_orders_2(X45) )
      & ( ~ r2_hidden(esk7_2(X45,X46),X46)
        | v13_waybel_0(X46,X45)
        | ~ m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X45)))
        | ~ l1_orders_2(X45) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d20_waybel_0])])])])])).

fof(c_0_49,plain,(
    ! [X25,X26,X27] :
      ( ~ r2_hidden(X25,X26)
      | ~ m1_subset_1(X26,k1_zfmisc_1(X27))
      | m1_subset_1(X25,X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_50,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X2 = X3
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_51,plain,
    ( r1_orders_2(X2,X4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X1)
    | X4 != k1_yellow_0(X2,X3)
    | ~ r1_yellow_0(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(k1_yellow_0(esk8_0,X1),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_53,negated_conjecture,
    ( u1_struct_0(esk8_0) = esk9_0
    | r2_lattice3(esk8_0,X1,esk2_3(u1_struct_0(esk8_0),esk9_0,u1_struct_0(esk8_0)))
    | r2_hidden(esk4_3(esk8_0,X1,esk2_3(u1_struct_0(esk8_0),esk9_0,u1_struct_0(esk8_0))),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_42])])).

cnf(c_0_54,plain,
    ( r1_tarski(k1_xboole_0,X1)
    | ~ r1_tarski(X2,esk1_2(k1_xboole_0,X1)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_55,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_39])).

fof(c_0_56,plain,(
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

fof(c_0_57,plain,(
    ! [X21,X22] :
      ( ~ r2_hidden(X21,X22)
      | m1_subset_1(X21,X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(k3_yellow_0(esk8_0),esk9_0)
    | ~ v1_subset_1(esk9_0,u1_struct_0(esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_59,negated_conjecture,
    ( u1_struct_0(esk8_0) = esk9_0
    | v1_subset_1(esk9_0,u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_36])).

fof(c_0_60,plain,(
    ! [X35] :
      ( ~ l1_orders_2(X35)
      | k3_yellow_0(X35) = k1_yellow_0(X35,k1_xboole_0) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_yellow_0])])).

cnf(c_0_61,plain,
    ( r2_hidden(X4,X1)
    | ~ v13_waybel_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r2_hidden(X3,X1)
    | ~ r1_orders_2(X2,X3,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_62,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_63,plain,
    ( X1 = X2
    | r2_hidden(esk2_3(X2,X1,X2),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_28]),c_0_30])).

cnf(c_0_64,negated_conjecture,
    ( r1_orders_2(esk8_0,k1_yellow_0(esk8_0,X1),X2)
    | k1_yellow_0(esk8_0,X1) != k1_yellow_0(esk8_0,X3)
    | ~ r1_yellow_0(esk8_0,X3)
    | ~ r2_lattice3(esk8_0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_42])])).

cnf(c_0_65,negated_conjecture,
    ( u1_struct_0(esk8_0) = esk9_0
    | r2_lattice3(esk8_0,X1,esk2_3(u1_struct_0(esk8_0),esk9_0,u1_struct_0(esk8_0)))
    | ~ r1_tarski(X1,esk4_3(esk8_0,X1,esk2_3(u1_struct_0(esk8_0),esk9_0,u1_struct_0(esk8_0)))) ),
    inference(spm,[status(thm)],[c_0_45,c_0_53])).

cnf(c_0_66,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_67,plain,
    ( r1_yellow_0(X1,k1_xboole_0)
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_yellow_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_68,negated_conjecture,
    ( v1_yellow_0(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_69,negated_conjecture,
    ( v5_orders_2(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_70,negated_conjecture,
    ( ~ v2_struct_0(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_71,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_72,negated_conjecture,
    ( u1_struct_0(esk8_0) = esk9_0
    | r2_hidden(k3_yellow_0(esk8_0),esk9_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_73,plain,
    ( k3_yellow_0(X1) = k1_yellow_0(X1,k1_xboole_0)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_74,plain,
    ( r2_hidden(X1,X2)
    | ~ v13_waybel_0(X2,X3)
    | ~ r1_orders_2(X3,X4,X1)
    | ~ l1_orders_2(X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ r2_hidden(X4,X2) ),
    inference(csr,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_75,negated_conjecture,
    ( v13_waybel_0(esk9_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_76,plain,
    ( X2 = X3
    | ~ r2_hidden(esk2_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_77,negated_conjecture,
    ( u1_struct_0(esk8_0) = esk9_0
    | r2_hidden(esk2_3(u1_struct_0(esk8_0),esk9_0,u1_struct_0(esk8_0)),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_36])).

cnf(c_0_78,negated_conjecture,
    ( u1_struct_0(esk8_0) = esk9_0
    | r1_orders_2(esk8_0,k1_yellow_0(esk8_0,X1),esk2_3(u1_struct_0(esk8_0),esk9_0,u1_struct_0(esk8_0)))
    | k1_yellow_0(esk8_0,X1) != k1_yellow_0(esk8_0,X2)
    | ~ r1_yellow_0(esk8_0,X2)
    | ~ r2_lattice3(esk8_0,X2,esk2_3(u1_struct_0(esk8_0),esk9_0,u1_struct_0(esk8_0))) ),
    inference(spm,[status(thm)],[c_0_64,c_0_44])).

cnf(c_0_79,negated_conjecture,
    ( u1_struct_0(esk8_0) = esk9_0
    | r2_lattice3(esk8_0,k1_xboole_0,esk2_3(u1_struct_0(esk8_0),esk9_0,u1_struct_0(esk8_0))) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_80,negated_conjecture,
    ( r1_yellow_0(esk8_0,k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_69]),c_0_42])]),c_0_70])).

fof(c_0_81,plain,(
    ! [X23,X24] :
      ( ~ m1_subset_1(X23,X24)
      | v1_xboole_0(X24)
      | r2_hidden(X23,X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_82,negated_conjecture,
    ( u1_struct_0(esk8_0) = esk9_0
    | m1_subset_1(k3_yellow_0(esk8_0),esk9_0) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_83,negated_conjecture,
    ( k3_yellow_0(esk8_0) = k1_yellow_0(esk8_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_73,c_0_42])).

cnf(c_0_84,negated_conjecture,
    ( r2_hidden(X1,esk9_0)
    | ~ r1_orders_2(esk8_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0))
    | ~ r2_hidden(X2,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_36]),c_0_75]),c_0_42])])).

cnf(c_0_85,negated_conjecture,
    ( u1_struct_0(esk8_0) = esk9_0
    | ~ r2_hidden(esk2_3(u1_struct_0(esk8_0),esk9_0,u1_struct_0(esk8_0)),esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_28]),c_0_36])])).

cnf(c_0_86,negated_conjecture,
    ( u1_struct_0(esk8_0) = esk9_0
    | r1_orders_2(esk8_0,k1_yellow_0(esk8_0,X1),esk2_3(u1_struct_0(esk8_0),esk9_0,u1_struct_0(esk8_0)))
    | k1_yellow_0(esk8_0,X1) != k1_yellow_0(esk8_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_80])])).

cnf(c_0_87,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_88,negated_conjecture,
    ( u1_struct_0(esk8_0) = esk9_0
    | m1_subset_1(k1_yellow_0(esk8_0,k1_xboole_0),esk9_0) ),
    inference(rw,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_89,negated_conjecture,
    ( ~ v1_xboole_0(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_90,negated_conjecture,
    ( u1_struct_0(esk8_0) = esk9_0
    | ~ r1_orders_2(esk8_0,X1,esk2_3(u1_struct_0(esk8_0),esk9_0,u1_struct_0(esk8_0)))
    | ~ r2_hidden(X1,esk9_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_44]),c_0_85])).

cnf(c_0_91,negated_conjecture,
    ( u1_struct_0(esk8_0) = esk9_0
    | r1_orders_2(esk8_0,k1_yellow_0(esk8_0,k1_xboole_0),esk2_3(u1_struct_0(esk8_0),esk9_0,u1_struct_0(esk8_0))) ),
    inference(er,[status(thm)],[c_0_86])).

cnf(c_0_92,negated_conjecture,
    ( u1_struct_0(esk8_0) = esk9_0
    | r2_hidden(k1_yellow_0(esk8_0,k1_xboole_0),esk9_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_89])).

cnf(c_0_93,negated_conjecture,
    ( v1_subset_1(esk9_0,u1_struct_0(esk8_0))
    | ~ r2_hidden(k3_yellow_0(esk8_0),esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_94,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk8_0))
    | r2_hidden(k1_yellow_0(esk8_0,X1),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_87,c_0_52])).

cnf(c_0_95,negated_conjecture,
    ( u1_struct_0(esk8_0) = esk9_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_92])).

cnf(c_0_96,negated_conjecture,
    ( v1_subset_1(esk9_0,u1_struct_0(esk8_0))
    | ~ r2_hidden(k1_yellow_0(esk8_0,k1_xboole_0),esk9_0) ),
    inference(rw,[status(thm)],[c_0_93,c_0_83])).

cnf(c_0_97,plain,
    ( ~ v1_subset_1(X1,X1) ),
    inference(rw,[status(thm)],[c_0_21,c_0_23])).

cnf(c_0_98,negated_conjecture,
    ( r2_hidden(k1_yellow_0(esk8_0,X1),esk9_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_94,c_0_95]),c_0_95]),c_0_89])).

cnf(c_0_99,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_96,c_0_95]),c_0_97]),c_0_98])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:33:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.52  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_PS_S0S
% 0.19/0.52  # and selection function SelectComplexG.
% 0.19/0.52  #
% 0.19/0.52  # Preprocessing time       : 0.031 s
% 0.19/0.52  # Presaturation interreduction done
% 0.19/0.52  
% 0.19/0.52  # Proof found!
% 0.19/0.52  # SZS status Theorem
% 0.19/0.52  # SZS output start CNFRefutation
% 0.19/0.52  fof(d7_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(v1_subset_1(X2,X1)<=>X2!=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 0.19/0.52  fof(rc3_subset_1, axiom, ![X1]:?[X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))&~(v1_subset_1(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc3_subset_1)).
% 0.19/0.52  fof(t8_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(![X4]:(m1_subset_1(X4,X1)=>(r2_hidden(X4,X2)<=>r2_hidden(X4,X3)))=>X2=X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_subset_1)).
% 0.19/0.52  fof(t8_waybel_7, conjecture, ![X1]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&v1_yellow_0(X1))&l1_orders_2(X1))=>![X2]:((((~(v1_xboole_0(X2))&v2_waybel_0(X2,X1))&v13_waybel_0(X2,X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v1_subset_1(X2,u1_struct_0(X1))<=>~(r2_hidden(k3_yellow_0(X1),X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_waybel_7)).
% 0.19/0.52  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 0.19/0.52  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 0.19/0.52  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.52  fof(dt_k1_yellow_0, axiom, ![X1, X2]:(l1_orders_2(X1)=>m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_yellow_0)).
% 0.19/0.52  fof(d9_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X2)=>r1_orders_2(X1,X4,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_lattice3)).
% 0.19/0.52  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.19/0.52  fof(d9_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_yellow_0(X1,X2)=>(X3=k1_yellow_0(X1,X2)<=>(r2_lattice3(X1,X2,X3)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X4)=>r1_orders_2(X1,X3,X4)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_yellow_0)).
% 0.19/0.52  fof(d20_waybel_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v13_waybel_0(X2,X1)<=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((r2_hidden(X3,X2)&r1_orders_2(X1,X3,X4))=>r2_hidden(X4,X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d20_waybel_0)).
% 0.19/0.52  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.19/0.52  fof(t42_yellow_0, axiom, ![X1]:((((~(v2_struct_0(X1))&v5_orders_2(X1))&v1_yellow_0(X1))&l1_orders_2(X1))=>(r1_yellow_0(X1,k1_xboole_0)&r2_yellow_0(X1,u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_yellow_0)).
% 0.19/0.52  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 0.19/0.52  fof(d11_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>k3_yellow_0(X1)=k1_yellow_0(X1,k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_yellow_0)).
% 0.19/0.52  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 0.19/0.52  fof(c_0_17, plain, ![X51, X52]:((~v1_subset_1(X52,X51)|X52!=X51|~m1_subset_1(X52,k1_zfmisc_1(X51)))&(X52=X51|v1_subset_1(X52,X51)|~m1_subset_1(X52,k1_zfmisc_1(X51)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).
% 0.19/0.52  fof(c_0_18, plain, ![X19]:(m1_subset_1(esk3_1(X19),k1_zfmisc_1(X19))&~v1_subset_1(esk3_1(X19),X19)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[rc3_subset_1])])])).
% 0.19/0.52  cnf(c_0_19, plain, (X1=X2|v1_subset_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.52  cnf(c_0_20, plain, (m1_subset_1(esk3_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.52  cnf(c_0_21, plain, (~v1_subset_1(esk3_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.52  fof(c_0_22, plain, ![X15, X16, X17]:((m1_subset_1(esk2_3(X15,X16,X17),X15)|X16=X17|~m1_subset_1(X17,k1_zfmisc_1(X15))|~m1_subset_1(X16,k1_zfmisc_1(X15)))&((~r2_hidden(esk2_3(X15,X16,X17),X16)|~r2_hidden(esk2_3(X15,X16,X17),X17)|X16=X17|~m1_subset_1(X17,k1_zfmisc_1(X15))|~m1_subset_1(X16,k1_zfmisc_1(X15)))&(r2_hidden(esk2_3(X15,X16,X17),X16)|r2_hidden(esk2_3(X15,X16,X17),X17)|X16=X17|~m1_subset_1(X17,k1_zfmisc_1(X15))|~m1_subset_1(X16,k1_zfmisc_1(X15))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_subset_1])])])])])).
% 0.19/0.52  cnf(c_0_23, plain, (esk3_1(X1)=X1), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21])).
% 0.19/0.52  fof(c_0_24, negated_conjecture, ~(![X1]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&v1_yellow_0(X1))&l1_orders_2(X1))=>![X2]:((((~(v1_xboole_0(X2))&v2_waybel_0(X2,X1))&v13_waybel_0(X2,X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v1_subset_1(X2,u1_struct_0(X1))<=>~(r2_hidden(k3_yellow_0(X1),X2)))))), inference(assume_negation,[status(cth)],[t8_waybel_7])).
% 0.19/0.52  fof(c_0_25, plain, ![X11, X12, X13]:(~m1_subset_1(X12,k1_zfmisc_1(X11))|(~r2_hidden(X13,X12)|r2_hidden(X13,X11))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.19/0.52  fof(c_0_26, plain, ![X14]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X14)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.19/0.52  cnf(c_0_27, plain, (m1_subset_1(esk2_3(X1,X2,X3),X1)|X2=X3|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.52  cnf(c_0_28, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_20, c_0_23])).
% 0.19/0.52  fof(c_0_29, negated_conjecture, ((((((~v2_struct_0(esk8_0)&v3_orders_2(esk8_0))&v4_orders_2(esk8_0))&v5_orders_2(esk8_0))&v1_yellow_0(esk8_0))&l1_orders_2(esk8_0))&((((~v1_xboole_0(esk9_0)&v2_waybel_0(esk9_0,esk8_0))&v13_waybel_0(esk9_0,esk8_0))&m1_subset_1(esk9_0,k1_zfmisc_1(u1_struct_0(esk8_0))))&((~v1_subset_1(esk9_0,u1_struct_0(esk8_0))|r2_hidden(k3_yellow_0(esk8_0),esk9_0))&(v1_subset_1(esk9_0,u1_struct_0(esk8_0))|~r2_hidden(k3_yellow_0(esk8_0),esk9_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_24])])])])).
% 0.19/0.52  cnf(c_0_30, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.52  cnf(c_0_31, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.52  fof(c_0_32, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.52  fof(c_0_33, plain, ![X41, X42]:(~l1_orders_2(X41)|m1_subset_1(k1_yellow_0(X41,X42),u1_struct_0(X41))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_yellow_0])])).
% 0.19/0.52  fof(c_0_34, plain, ![X30, X31, X32, X33]:((~r2_lattice3(X30,X31,X32)|(~m1_subset_1(X33,u1_struct_0(X30))|(~r2_hidden(X33,X31)|r1_orders_2(X30,X33,X32)))|~m1_subset_1(X32,u1_struct_0(X30))|~l1_orders_2(X30))&((m1_subset_1(esk4_3(X30,X31,X32),u1_struct_0(X30))|r2_lattice3(X30,X31,X32)|~m1_subset_1(X32,u1_struct_0(X30))|~l1_orders_2(X30))&((r2_hidden(esk4_3(X30,X31,X32),X31)|r2_lattice3(X30,X31,X32)|~m1_subset_1(X32,u1_struct_0(X30))|~l1_orders_2(X30))&(~r1_orders_2(X30,esk4_3(X30,X31,X32),X32)|r2_lattice3(X30,X31,X32)|~m1_subset_1(X32,u1_struct_0(X30))|~l1_orders_2(X30))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).
% 0.19/0.52  cnf(c_0_35, plain, (X1=X2|m1_subset_1(esk2_3(X2,X1,X2),X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.19/0.52  cnf(c_0_36, negated_conjecture, (m1_subset_1(esk9_0,k1_zfmisc_1(u1_struct_0(esk8_0)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.52  fof(c_0_37, plain, ![X28, X29]:(~r2_hidden(X28,X29)|~r1_tarski(X29,X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.19/0.52  cnf(c_0_38, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.19/0.52  cnf(c_0_39, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.52  fof(c_0_40, plain, ![X36, X37, X38, X39]:(((r2_lattice3(X36,X37,X38)|X38!=k1_yellow_0(X36,X37)|~r1_yellow_0(X36,X37)|~m1_subset_1(X38,u1_struct_0(X36))|~l1_orders_2(X36))&(~m1_subset_1(X39,u1_struct_0(X36))|(~r2_lattice3(X36,X37,X39)|r1_orders_2(X36,X38,X39))|X38!=k1_yellow_0(X36,X37)|~r1_yellow_0(X36,X37)|~m1_subset_1(X38,u1_struct_0(X36))|~l1_orders_2(X36)))&((m1_subset_1(esk5_3(X36,X37,X38),u1_struct_0(X36))|~r2_lattice3(X36,X37,X38)|X38=k1_yellow_0(X36,X37)|~r1_yellow_0(X36,X37)|~m1_subset_1(X38,u1_struct_0(X36))|~l1_orders_2(X36))&((r2_lattice3(X36,X37,esk5_3(X36,X37,X38))|~r2_lattice3(X36,X37,X38)|X38=k1_yellow_0(X36,X37)|~r1_yellow_0(X36,X37)|~m1_subset_1(X38,u1_struct_0(X36))|~l1_orders_2(X36))&(~r1_orders_2(X36,X38,esk5_3(X36,X37,X38))|~r2_lattice3(X36,X37,X38)|X38=k1_yellow_0(X36,X37)|~r1_yellow_0(X36,X37)|~m1_subset_1(X38,u1_struct_0(X36))|~l1_orders_2(X36))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_yellow_0])])])])])).
% 0.19/0.52  cnf(c_0_41, plain, (m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.52  cnf(c_0_42, negated_conjecture, (l1_orders_2(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.52  cnf(c_0_43, plain, (r2_hidden(esk4_3(X1,X2,X3),X2)|r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.52  cnf(c_0_44, negated_conjecture, (u1_struct_0(esk8_0)=esk9_0|m1_subset_1(esk2_3(u1_struct_0(esk8_0),esk9_0,u1_struct_0(esk8_0)),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.19/0.52  cnf(c_0_45, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.52  cnf(c_0_46, plain, (r2_hidden(esk1_2(k1_xboole_0,X1),X2)|r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.19/0.52  cnf(c_0_47, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.52  fof(c_0_48, plain, ![X45, X46, X47, X48]:((~v13_waybel_0(X46,X45)|(~m1_subset_1(X47,u1_struct_0(X45))|(~m1_subset_1(X48,u1_struct_0(X45))|(~r2_hidden(X47,X46)|~r1_orders_2(X45,X47,X48)|r2_hidden(X48,X46))))|~m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X45)))|~l1_orders_2(X45))&((m1_subset_1(esk6_2(X45,X46),u1_struct_0(X45))|v13_waybel_0(X46,X45)|~m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X45)))|~l1_orders_2(X45))&((m1_subset_1(esk7_2(X45,X46),u1_struct_0(X45))|v13_waybel_0(X46,X45)|~m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X45)))|~l1_orders_2(X45))&(((r2_hidden(esk6_2(X45,X46),X46)|v13_waybel_0(X46,X45)|~m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X45)))|~l1_orders_2(X45))&(r1_orders_2(X45,esk6_2(X45,X46),esk7_2(X45,X46))|v13_waybel_0(X46,X45)|~m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X45)))|~l1_orders_2(X45)))&(~r2_hidden(esk7_2(X45,X46),X46)|v13_waybel_0(X46,X45)|~m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X45)))|~l1_orders_2(X45)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d20_waybel_0])])])])])).
% 0.19/0.52  fof(c_0_49, plain, ![X25, X26, X27]:(~r2_hidden(X25,X26)|~m1_subset_1(X26,k1_zfmisc_1(X27))|m1_subset_1(X25,X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.19/0.52  cnf(c_0_50, plain, (r2_hidden(esk2_3(X1,X2,X3),X2)|r2_hidden(esk2_3(X1,X2,X3),X3)|X2=X3|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.52  cnf(c_0_51, plain, (r1_orders_2(X2,X4,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~r2_lattice3(X2,X3,X1)|X4!=k1_yellow_0(X2,X3)|~r1_yellow_0(X2,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.52  cnf(c_0_52, negated_conjecture, (m1_subset_1(k1_yellow_0(esk8_0,X1),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.19/0.52  cnf(c_0_53, negated_conjecture, (u1_struct_0(esk8_0)=esk9_0|r2_lattice3(esk8_0,X1,esk2_3(u1_struct_0(esk8_0),esk9_0,u1_struct_0(esk8_0)))|r2_hidden(esk4_3(esk8_0,X1,esk2_3(u1_struct_0(esk8_0),esk9_0,u1_struct_0(esk8_0))),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_42])])).
% 0.19/0.52  cnf(c_0_54, plain, (r1_tarski(k1_xboole_0,X1)|~r1_tarski(X2,esk1_2(k1_xboole_0,X1))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.19/0.52  cnf(c_0_55, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_47, c_0_39])).
% 0.19/0.52  fof(c_0_56, plain, ![X44]:((r1_yellow_0(X44,k1_xboole_0)|(v2_struct_0(X44)|~v5_orders_2(X44)|~v1_yellow_0(X44)|~l1_orders_2(X44)))&(r2_yellow_0(X44,u1_struct_0(X44))|(v2_struct_0(X44)|~v5_orders_2(X44)|~v1_yellow_0(X44)|~l1_orders_2(X44)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t42_yellow_0])])])])).
% 0.19/0.52  fof(c_0_57, plain, ![X21, X22]:(~r2_hidden(X21,X22)|m1_subset_1(X21,X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.19/0.52  cnf(c_0_58, negated_conjecture, (r2_hidden(k3_yellow_0(esk8_0),esk9_0)|~v1_subset_1(esk9_0,u1_struct_0(esk8_0))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.52  cnf(c_0_59, negated_conjecture, (u1_struct_0(esk8_0)=esk9_0|v1_subset_1(esk9_0,u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_19, c_0_36])).
% 0.19/0.52  fof(c_0_60, plain, ![X35]:(~l1_orders_2(X35)|k3_yellow_0(X35)=k1_yellow_0(X35,k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_yellow_0])])).
% 0.19/0.52  cnf(c_0_61, plain, (r2_hidden(X4,X1)|~v13_waybel_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X2))|~m1_subset_1(X4,u1_struct_0(X2))|~r2_hidden(X3,X1)|~r1_orders_2(X2,X3,X4)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.19/0.52  cnf(c_0_62, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.19/0.52  cnf(c_0_63, plain, (X1=X2|r2_hidden(esk2_3(X2,X1,X2),X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_28]), c_0_30])).
% 0.19/0.52  cnf(c_0_64, negated_conjecture, (r1_orders_2(esk8_0,k1_yellow_0(esk8_0,X1),X2)|k1_yellow_0(esk8_0,X1)!=k1_yellow_0(esk8_0,X3)|~r1_yellow_0(esk8_0,X3)|~r2_lattice3(esk8_0,X3,X2)|~m1_subset_1(X2,u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_42])])).
% 0.19/0.52  cnf(c_0_65, negated_conjecture, (u1_struct_0(esk8_0)=esk9_0|r2_lattice3(esk8_0,X1,esk2_3(u1_struct_0(esk8_0),esk9_0,u1_struct_0(esk8_0)))|~r1_tarski(X1,esk4_3(esk8_0,X1,esk2_3(u1_struct_0(esk8_0),esk9_0,u1_struct_0(esk8_0))))), inference(spm,[status(thm)],[c_0_45, c_0_53])).
% 0.19/0.52  cnf(c_0_66, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.19/0.52  cnf(c_0_67, plain, (r1_yellow_0(X1,k1_xboole_0)|v2_struct_0(X1)|~v5_orders_2(X1)|~v1_yellow_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.19/0.52  cnf(c_0_68, negated_conjecture, (v1_yellow_0(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.52  cnf(c_0_69, negated_conjecture, (v5_orders_2(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.52  cnf(c_0_70, negated_conjecture, (~v2_struct_0(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.52  cnf(c_0_71, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.19/0.52  cnf(c_0_72, negated_conjecture, (u1_struct_0(esk8_0)=esk9_0|r2_hidden(k3_yellow_0(esk8_0),esk9_0)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.19/0.52  cnf(c_0_73, plain, (k3_yellow_0(X1)=k1_yellow_0(X1,k1_xboole_0)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.19/0.52  cnf(c_0_74, plain, (r2_hidden(X1,X2)|~v13_waybel_0(X2,X3)|~r1_orders_2(X3,X4,X1)|~l1_orders_2(X3)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~m1_subset_1(X1,u1_struct_0(X3))|~r2_hidden(X4,X2)), inference(csr,[status(thm)],[c_0_61, c_0_62])).
% 0.19/0.52  cnf(c_0_75, negated_conjecture, (v13_waybel_0(esk9_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.52  cnf(c_0_76, plain, (X2=X3|~r2_hidden(esk2_3(X1,X2,X3),X2)|~r2_hidden(esk2_3(X1,X2,X3),X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.52  cnf(c_0_77, negated_conjecture, (u1_struct_0(esk8_0)=esk9_0|r2_hidden(esk2_3(u1_struct_0(esk8_0),esk9_0,u1_struct_0(esk8_0)),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_63, c_0_36])).
% 0.19/0.52  cnf(c_0_78, negated_conjecture, (u1_struct_0(esk8_0)=esk9_0|r1_orders_2(esk8_0,k1_yellow_0(esk8_0,X1),esk2_3(u1_struct_0(esk8_0),esk9_0,u1_struct_0(esk8_0)))|k1_yellow_0(esk8_0,X1)!=k1_yellow_0(esk8_0,X2)|~r1_yellow_0(esk8_0,X2)|~r2_lattice3(esk8_0,X2,esk2_3(u1_struct_0(esk8_0),esk9_0,u1_struct_0(esk8_0)))), inference(spm,[status(thm)],[c_0_64, c_0_44])).
% 0.19/0.52  cnf(c_0_79, negated_conjecture, (u1_struct_0(esk8_0)=esk9_0|r2_lattice3(esk8_0,k1_xboole_0,esk2_3(u1_struct_0(esk8_0),esk9_0,u1_struct_0(esk8_0)))), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.19/0.52  cnf(c_0_80, negated_conjecture, (r1_yellow_0(esk8_0,k1_xboole_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_69]), c_0_42])]), c_0_70])).
% 0.19/0.52  fof(c_0_81, plain, ![X23, X24]:(~m1_subset_1(X23,X24)|(v1_xboole_0(X24)|r2_hidden(X23,X24))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.19/0.52  cnf(c_0_82, negated_conjecture, (u1_struct_0(esk8_0)=esk9_0|m1_subset_1(k3_yellow_0(esk8_0),esk9_0)), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.19/0.52  cnf(c_0_83, negated_conjecture, (k3_yellow_0(esk8_0)=k1_yellow_0(esk8_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_73, c_0_42])).
% 0.19/0.52  cnf(c_0_84, negated_conjecture, (r2_hidden(X1,esk9_0)|~r1_orders_2(esk8_0,X2,X1)|~m1_subset_1(X1,u1_struct_0(esk8_0))|~r2_hidden(X2,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_36]), c_0_75]), c_0_42])])).
% 0.19/0.52  cnf(c_0_85, negated_conjecture, (u1_struct_0(esk8_0)=esk9_0|~r2_hidden(esk2_3(u1_struct_0(esk8_0),esk9_0,u1_struct_0(esk8_0)),esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_28]), c_0_36])])).
% 0.19/0.52  cnf(c_0_86, negated_conjecture, (u1_struct_0(esk8_0)=esk9_0|r1_orders_2(esk8_0,k1_yellow_0(esk8_0,X1),esk2_3(u1_struct_0(esk8_0),esk9_0,u1_struct_0(esk8_0)))|k1_yellow_0(esk8_0,X1)!=k1_yellow_0(esk8_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_80])])).
% 0.19/0.52  cnf(c_0_87, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_81])).
% 0.19/0.52  cnf(c_0_88, negated_conjecture, (u1_struct_0(esk8_0)=esk9_0|m1_subset_1(k1_yellow_0(esk8_0,k1_xboole_0),esk9_0)), inference(rw,[status(thm)],[c_0_82, c_0_83])).
% 0.19/0.52  cnf(c_0_89, negated_conjecture, (~v1_xboole_0(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.52  cnf(c_0_90, negated_conjecture, (u1_struct_0(esk8_0)=esk9_0|~r1_orders_2(esk8_0,X1,esk2_3(u1_struct_0(esk8_0),esk9_0,u1_struct_0(esk8_0)))|~r2_hidden(X1,esk9_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_44]), c_0_85])).
% 0.19/0.52  cnf(c_0_91, negated_conjecture, (u1_struct_0(esk8_0)=esk9_0|r1_orders_2(esk8_0,k1_yellow_0(esk8_0,k1_xboole_0),esk2_3(u1_struct_0(esk8_0),esk9_0,u1_struct_0(esk8_0)))), inference(er,[status(thm)],[c_0_86])).
% 0.19/0.52  cnf(c_0_92, negated_conjecture, (u1_struct_0(esk8_0)=esk9_0|r2_hidden(k1_yellow_0(esk8_0,k1_xboole_0),esk9_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_89])).
% 0.19/0.52  cnf(c_0_93, negated_conjecture, (v1_subset_1(esk9_0,u1_struct_0(esk8_0))|~r2_hidden(k3_yellow_0(esk8_0),esk9_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.52  cnf(c_0_94, negated_conjecture, (v1_xboole_0(u1_struct_0(esk8_0))|r2_hidden(k1_yellow_0(esk8_0,X1),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_87, c_0_52])).
% 0.19/0.52  cnf(c_0_95, negated_conjecture, (u1_struct_0(esk8_0)=esk9_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_91]), c_0_92])).
% 0.19/0.52  cnf(c_0_96, negated_conjecture, (v1_subset_1(esk9_0,u1_struct_0(esk8_0))|~r2_hidden(k1_yellow_0(esk8_0,k1_xboole_0),esk9_0)), inference(rw,[status(thm)],[c_0_93, c_0_83])).
% 0.19/0.52  cnf(c_0_97, plain, (~v1_subset_1(X1,X1)), inference(rw,[status(thm)],[c_0_21, c_0_23])).
% 0.19/0.52  cnf(c_0_98, negated_conjecture, (r2_hidden(k1_yellow_0(esk8_0,X1),esk9_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_94, c_0_95]), c_0_95]), c_0_89])).
% 0.19/0.52  cnf(c_0_99, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_96, c_0_95]), c_0_97]), c_0_98])]), ['proof']).
% 0.19/0.52  # SZS output end CNFRefutation
% 0.19/0.52  # Proof object total steps             : 100
% 0.19/0.52  # Proof object clause steps            : 65
% 0.19/0.52  # Proof object formula steps           : 35
% 0.19/0.52  # Proof object conjectures             : 37
% 0.19/0.52  # Proof object clause conjectures      : 34
% 0.19/0.52  # Proof object formula conjectures     : 3
% 0.19/0.52  # Proof object initial clauses used    : 29
% 0.19/0.52  # Proof object initial formulas used   : 17
% 0.19/0.52  # Proof object generating inferences   : 29
% 0.19/0.52  # Proof object simplifying inferences  : 33
% 0.19/0.52  # Training examples: 0 positive, 0 negative
% 0.19/0.52  # Parsed axioms                        : 18
% 0.19/0.52  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.52  # Initial clauses                      : 48
% 0.19/0.52  # Removed in clause preprocessing      : 0
% 0.19/0.52  # Initial clauses in saturation        : 48
% 0.19/0.52  # Processed clauses                    : 1010
% 0.19/0.52  # ...of these trivial                  : 5
% 0.19/0.52  # ...subsumed                          : 284
% 0.19/0.52  # ...remaining for further processing  : 720
% 0.19/0.52  # Other redundant clauses eliminated   : 1
% 0.19/0.52  # Clauses deleted for lack of memory   : 0
% 0.19/0.52  # Backward-subsumed                    : 37
% 0.19/0.52  # Backward-rewritten                   : 363
% 0.19/0.52  # Generated clauses                    : 2914
% 0.19/0.52  # ...of the previous two non-trivial   : 3059
% 0.19/0.52  # Contextual simplify-reflections      : 14
% 0.19/0.52  # Paramodulations                      : 2908
% 0.19/0.52  # Factorizations                       : 0
% 0.19/0.52  # Equation resolutions                 : 6
% 0.19/0.52  # Propositional unsat checks           : 0
% 0.19/0.52  #    Propositional check models        : 0
% 0.19/0.52  #    Propositional check unsatisfiable : 0
% 0.19/0.52  #    Propositional clauses             : 0
% 0.19/0.52  #    Propositional clauses after purity: 0
% 0.19/0.52  #    Propositional unsat core size     : 0
% 0.19/0.52  #    Propositional preprocessing time  : 0.000
% 0.19/0.52  #    Propositional encoding time       : 0.000
% 0.19/0.52  #    Propositional solver time         : 0.000
% 0.19/0.52  #    Success case prop preproc time    : 0.000
% 0.19/0.52  #    Success case prop encoding time   : 0.000
% 0.19/0.52  #    Success case prop solver time     : 0.000
% 0.19/0.52  # Current number of processed clauses  : 271
% 0.19/0.52  #    Positive orientable unit clauses  : 19
% 0.19/0.52  #    Positive unorientable unit clauses: 0
% 0.19/0.52  #    Negative unit clauses             : 5
% 0.19/0.52  #    Non-unit-clauses                  : 247
% 0.19/0.52  # Current number of unprocessed clauses: 2064
% 0.19/0.52  # ...number of literals in the above   : 10424
% 0.19/0.52  # Current number of archived formulas  : 0
% 0.19/0.52  # Current number of archived clauses   : 448
% 0.19/0.52  # Clause-clause subsumption calls (NU) : 65266
% 0.19/0.52  # Rec. Clause-clause subsumption calls : 18383
% 0.19/0.52  # Non-unit clause-clause subsumptions  : 334
% 0.19/0.52  # Unit Clause-clause subsumption calls : 524
% 0.19/0.52  # Rewrite failures with RHS unbound    : 0
% 0.19/0.52  # BW rewrite match attempts            : 18
% 0.19/0.52  # BW rewrite match successes           : 7
% 0.19/0.52  # Condensation attempts                : 0
% 0.19/0.52  # Condensation successes               : 0
% 0.19/0.52  # Termbank termtop insertions          : 99393
% 0.19/0.52  
% 0.19/0.52  # -------------------------------------------------
% 0.19/0.52  # User time                : 0.169 s
% 0.19/0.52  # System time              : 0.009 s
% 0.19/0.52  # Total time               : 0.178 s
% 0.19/0.52  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
