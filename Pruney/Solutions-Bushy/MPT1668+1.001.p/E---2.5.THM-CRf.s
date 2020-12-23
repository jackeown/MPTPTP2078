%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1668+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:33 EST 2020

% Result     : Theorem 7.98s
% Output     : CNFRefutation 7.98s
% Verified   : 
% Statistics : Number of formulae       :  136 (220650 expanded)
%              Number of clauses        :  113 (73416 expanded)
%              Number of leaves         :   11 (53386 expanded)
%              Depth                    :   39
%              Number of atoms          :  581 (1970081 expanded)
%              Number of equality atoms :   20 (165997 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   42 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t48_waybel_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v1_waybel_0(X2,X1)
            & v12_waybel_0(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => ( v14_waybel_0(X2,X1)
          <=> ? [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
                & X2 = k5_waybel_0(X1,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_waybel_0)).

fof(d21_waybel_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v1_waybel_0(X2,X1)
            & v12_waybel_0(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => ( v14_waybel_0(X2,X1)
          <=> ? [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
                & r2_hidden(X3,X2)
                & r2_lattice3(X1,X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d21_waybel_0)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(dt_k5_waybel_0,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => m1_subset_1(k5_waybel_0(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_waybel_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t17_waybel_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r2_hidden(X3,k5_waybel_0(X1,X2))
              <=> r1_orders_2(X1,X3,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_waybel_0)).

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

fof(d19_waybel_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v12_waybel_0(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( ( r2_hidden(X3,X2)
                        & r1_orders_2(X1,X4,X3) )
                     => r2_hidden(X4,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_waybel_0)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(reflexivity_r3_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => r3_orders_2(X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).

fof(redefinition_r3_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( r3_orders_2(X1,X2,X3)
      <=> r1_orders_2(X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( ( ~ v1_xboole_0(X2)
              & v1_waybel_0(X2,X1)
              & v12_waybel_0(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
           => ( v14_waybel_0(X2,X1)
            <=> ? [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                  & X2 = k5_waybel_0(X1,X3) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t48_waybel_0])).

fof(c_0_12,plain,(
    ! [X13,X14,X16] :
      ( ( m1_subset_1(esk3_2(X13,X14),u1_struct_0(X13))
        | ~ v14_waybel_0(X14,X13)
        | v1_xboole_0(X14)
        | ~ v1_waybel_0(X14,X13)
        | ~ v12_waybel_0(X14,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( r2_hidden(esk3_2(X13,X14),X14)
        | ~ v14_waybel_0(X14,X13)
        | v1_xboole_0(X14)
        | ~ v1_waybel_0(X14,X13)
        | ~ v12_waybel_0(X14,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( r2_lattice3(X13,X14,esk3_2(X13,X14))
        | ~ v14_waybel_0(X14,X13)
        | v1_xboole_0(X14)
        | ~ v1_waybel_0(X14,X13)
        | ~ v12_waybel_0(X14,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ m1_subset_1(X16,u1_struct_0(X13))
        | ~ r2_hidden(X16,X14)
        | ~ r2_lattice3(X13,X14,X16)
        | v14_waybel_0(X14,X13)
        | v1_xboole_0(X14)
        | ~ v1_waybel_0(X14,X13)
        | ~ v12_waybel_0(X14,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d21_waybel_0])])])])])])).

fof(c_0_13,negated_conjecture,(
    ! [X46] :
      ( ~ v2_struct_0(esk6_0)
      & v3_orders_2(esk6_0)
      & v4_orders_2(esk6_0)
      & l1_orders_2(esk6_0)
      & ~ v1_xboole_0(esk7_0)
      & v1_waybel_0(esk7_0,esk6_0)
      & v12_waybel_0(esk7_0,esk6_0)
      & m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk6_0)))
      & ( ~ v14_waybel_0(esk7_0,esk6_0)
        | ~ m1_subset_1(X46,u1_struct_0(esk6_0))
        | esk7_0 != k5_waybel_0(esk6_0,X46) )
      & ( m1_subset_1(esk8_0,u1_struct_0(esk6_0))
        | v14_waybel_0(esk7_0,esk6_0) )
      & ( esk7_0 = k5_waybel_0(esk6_0,esk8_0)
        | v14_waybel_0(esk7_0,esk6_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])])])).

cnf(c_0_14,plain,
    ( m1_subset_1(esk3_2(X1,X2),u1_struct_0(X1))
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ v14_waybel_0(X2,X1)
    | ~ v1_waybel_0(X2,X1)
    | ~ v12_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_16,negated_conjecture,
    ( v1_waybel_0(esk7_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( v4_orders_2(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( v3_orders_2(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( v12_waybel_0(esk7_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( l1_orders_2(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,negated_conjecture,
    ( ~ v1_xboole_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,negated_conjecture,
    ( ~ v2_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_23,plain,(
    ! [X41,X42,X43] :
      ( ~ r2_hidden(X41,X42)
      | ~ m1_subset_1(X42,k1_zfmisc_1(X43))
      | m1_subset_1(X41,X43) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_24,plain,(
    ! [X28,X29] :
      ( v2_struct_0(X28)
      | ~ l1_orders_2(X28)
      | ~ m1_subset_1(X29,u1_struct_0(X28))
      | m1_subset_1(k5_waybel_0(X28,X29),k1_zfmisc_1(u1_struct_0(X28))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_waybel_0])])])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))
    | ~ v14_waybel_0(esk7_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16]),c_0_17]),c_0_18]),c_0_19]),c_0_20])]),c_0_21]),c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk8_0,u1_struct_0(esk6_0))
    | v14_waybel_0(esk7_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_27,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_28,plain,(
    ! [X17,X18,X19,X20,X21] :
      ( ( ~ r1_tarski(X17,X18)
        | ~ r2_hidden(X19,X17)
        | r2_hidden(X19,X18) )
      & ( r2_hidden(esk4_2(X20,X21),X20)
        | r1_tarski(X20,X21) )
      & ( ~ r2_hidden(esk4_2(X20,X21),X21)
        | r1_tarski(X20,X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_29,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k5_waybel_0(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))
    | m1_subset_1(esk8_0,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

fof(c_0_31,plain,(
    ! [X36,X37,X38] :
      ( ( ~ r2_hidden(X38,k5_waybel_0(X36,X37))
        | r1_orders_2(X36,X38,X37)
        | ~ m1_subset_1(X38,u1_struct_0(X36))
        | ~ m1_subset_1(X37,u1_struct_0(X36))
        | v2_struct_0(X36)
        | ~ l1_orders_2(X36) )
      & ( ~ r1_orders_2(X36,X38,X37)
        | r2_hidden(X38,k5_waybel_0(X36,X37))
        | ~ m1_subset_1(X38,u1_struct_0(X36))
        | ~ m1_subset_1(X37,u1_struct_0(X36))
        | v2_struct_0(X36)
        | ~ l1_orders_2(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t17_waybel_0])])])])])).

fof(c_0_32,plain,(
    ! [X23,X24,X25,X26] :
      ( ( ~ r2_lattice3(X23,X24,X25)
        | ~ m1_subset_1(X26,u1_struct_0(X23))
        | ~ r2_hidden(X26,X24)
        | r1_orders_2(X23,X26,X25)
        | ~ m1_subset_1(X25,u1_struct_0(X23))
        | ~ l1_orders_2(X23) )
      & ( m1_subset_1(esk5_3(X23,X24,X25),u1_struct_0(X23))
        | r2_lattice3(X23,X24,X25)
        | ~ m1_subset_1(X25,u1_struct_0(X23))
        | ~ l1_orders_2(X23) )
      & ( r2_hidden(esk5_3(X23,X24,X25),X24)
        | r2_lattice3(X23,X24,X25)
        | ~ m1_subset_1(X25,u1_struct_0(X23))
        | ~ l1_orders_2(X23) )
      & ( ~ r1_orders_2(X23,esk5_3(X23,X24,X25),X25)
        | r2_lattice3(X23,X24,X25)
        | ~ m1_subset_1(X25,u1_struct_0(X23))
        | ~ l1_orders_2(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk6_0))
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_15])).

cnf(c_0_34,plain,
    ( r2_hidden(esk4_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,plain,
    ( r2_lattice3(X1,X2,esk3_2(X1,X2))
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ v14_waybel_0(X2,X1)
    | ~ v1_waybel_0(X2,X1)
    | ~ v12_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_36,plain,(
    ! [X7,X8,X9,X10] :
      ( ( ~ v12_waybel_0(X8,X7)
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | ~ m1_subset_1(X10,u1_struct_0(X7))
        | ~ r2_hidden(X9,X8)
        | ~ r1_orders_2(X7,X10,X9)
        | r2_hidden(X10,X8)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))
        | ~ l1_orders_2(X7) )
      & ( m1_subset_1(esk1_2(X7,X8),u1_struct_0(X7))
        | v12_waybel_0(X8,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))
        | ~ l1_orders_2(X7) )
      & ( m1_subset_1(esk2_2(X7,X8),u1_struct_0(X7))
        | v12_waybel_0(X8,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))
        | ~ l1_orders_2(X7) )
      & ( r2_hidden(esk1_2(X7,X8),X8)
        | v12_waybel_0(X8,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))
        | ~ l1_orders_2(X7) )
      & ( r1_orders_2(X7,esk2_2(X7,X8),esk1_2(X7,X8))
        | v12_waybel_0(X8,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))
        | ~ l1_orders_2(X7) )
      & ( ~ r2_hidden(esk2_2(X7,X8),X8)
        | v12_waybel_0(X8,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))
        | ~ l1_orders_2(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_waybel_0])])])])])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(k5_waybel_0(esk6_0,esk3_2(esk6_0,esk7_0)),k1_zfmisc_1(u1_struct_0(esk6_0)))
    | m1_subset_1(esk8_0,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_20])]),c_0_22])).

cnf(c_0_38,plain,
    ( r2_hidden(X2,k5_waybel_0(X1,X3))
    | v2_struct_0(X1)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,plain,
    ( r1_orders_2(X1,X4,X3)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(esk4_2(esk7_0,X1),u1_struct_0(esk6_0))
    | r1_tarski(esk7_0,X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_41,negated_conjecture,
    ( r2_lattice3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))
    | ~ v14_waybel_0(esk7_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_15]),c_0_16]),c_0_17]),c_0_18]),c_0_19]),c_0_20])]),c_0_21]),c_0_22])).

cnf(c_0_42,plain,
    ( r2_hidden(X4,X1)
    | ~ v12_waybel_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r2_hidden(X3,X1)
    | ~ r1_orders_2(X2,X4,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(esk8_0,u1_struct_0(esk6_0))
    | m1_subset_1(X1,u1_struct_0(esk6_0))
    | ~ r2_hidden(X1,k5_waybel_0(esk6_0,esk3_2(esk6_0,esk7_0))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_37])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(X1,k5_waybel_0(esk6_0,esk3_2(esk6_0,esk7_0)))
    | m1_subset_1(esk8_0,u1_struct_0(esk6_0))
    | ~ r1_orders_2(esk6_0,X1,esk3_2(esk6_0,esk7_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_30]),c_0_20])]),c_0_22])).

cnf(c_0_45,negated_conjecture,
    ( r1_orders_2(esk6_0,esk4_2(esk7_0,X1),X2)
    | r1_tarski(esk7_0,X1)
    | ~ r2_lattice3(esk6_0,X3,X2)
    | ~ r2_hidden(esk4_2(esk7_0,X1),X3)
    | ~ m1_subset_1(X2,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_20])])).

cnf(c_0_46,negated_conjecture,
    ( r2_lattice3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))
    | m1_subset_1(esk8_0,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_26])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_orders_2(X3,X1,X4)
    | ~ r2_hidden(X4,X2)
    | ~ v12_waybel_0(X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(csr,[status(thm)],[c_0_42,c_0_27])).

cnf(c_0_48,negated_conjecture,
    ( m1_subset_1(esk4_2(k5_waybel_0(esk6_0,esk3_2(esk6_0,esk7_0)),X1),u1_struct_0(esk6_0))
    | m1_subset_1(esk8_0,u1_struct_0(esk6_0))
    | r1_tarski(k5_waybel_0(esk6_0,esk3_2(esk6_0,esk7_0)),X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_34])).

cnf(c_0_49,plain,
    ( r2_hidden(esk3_2(X1,X2),X2)
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ v14_waybel_0(X2,X1)
    | ~ v1_waybel_0(X2,X1)
    | ~ v12_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_50,plain,
    ( r1_orders_2(X2,X1,X3)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,k5_waybel_0(X2,X3))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(esk4_2(esk7_0,X1),k5_waybel_0(esk6_0,esk3_2(esk6_0,esk7_0)))
    | m1_subset_1(esk8_0,u1_struct_0(esk6_0))
    | r1_tarski(esk7_0,X1)
    | ~ r1_orders_2(esk6_0,esk4_2(esk7_0,X1),esk3_2(esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_40])).

cnf(c_0_52,negated_conjecture,
    ( r1_orders_2(esk6_0,esk4_2(esk7_0,X1),esk3_2(esk6_0,esk7_0))
    | m1_subset_1(esk8_0,u1_struct_0(esk6_0))
    | r1_tarski(esk7_0,X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_30]),c_0_34])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(esk4_2(k5_waybel_0(esk6_0,esk3_2(esk6_0,esk7_0)),X1),X2)
    | m1_subset_1(esk8_0,u1_struct_0(esk6_0))
    | r1_tarski(k5_waybel_0(esk6_0,esk3_2(esk6_0,esk7_0)),X1)
    | ~ r1_orders_2(esk6_0,esk4_2(k5_waybel_0(esk6_0,esk3_2(esk6_0,esk7_0)),X1),X3)
    | ~ r2_hidden(X3,X2)
    | ~ v12_waybel_0(X2,esk6_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_20])])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk3_2(esk6_0,esk7_0),esk7_0)
    | ~ v14_waybel_0(esk7_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_15]),c_0_16]),c_0_17]),c_0_18]),c_0_19]),c_0_20])]),c_0_21]),c_0_22])).

cnf(c_0_55,negated_conjecture,
    ( r1_orders_2(esk6_0,X1,esk3_2(esk6_0,esk7_0))
    | m1_subset_1(esk8_0,u1_struct_0(esk6_0))
    | ~ r2_hidden(X1,k5_waybel_0(esk6_0,esk3_2(esk6_0,esk7_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_30]),c_0_20])]),c_0_22])).

fof(c_0_56,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_57,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk4_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(esk4_2(esk7_0,X1),k5_waybel_0(esk6_0,esk3_2(esk6_0,esk7_0)))
    | m1_subset_1(esk8_0,u1_struct_0(esk6_0))
    | r1_tarski(esk7_0,X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(esk4_2(k5_waybel_0(esk6_0,esk3_2(esk6_0,esk7_0)),X1),esk7_0)
    | m1_subset_1(esk8_0,u1_struct_0(esk6_0))
    | r1_tarski(k5_waybel_0(esk6_0,esk3_2(esk6_0,esk7_0)),X1)
    | ~ r1_orders_2(esk6_0,esk4_2(k5_waybel_0(esk6_0,esk3_2(esk6_0,esk7_0)),X1),X2)
    | ~ r2_hidden(X2,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_19]),c_0_15])])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(esk3_2(esk6_0,esk7_0),esk7_0)
    | m1_subset_1(esk8_0,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_26])).

cnf(c_0_61,negated_conjecture,
    ( r1_orders_2(esk6_0,esk4_2(k5_waybel_0(esk6_0,esk3_2(esk6_0,esk7_0)),X1),esk3_2(esk6_0,esk7_0))
    | m1_subset_1(esk8_0,u1_struct_0(esk6_0))
    | r1_tarski(k5_waybel_0(esk6_0,esk3_2(esk6_0,esk7_0)),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_48]),c_0_34])).

cnf(c_0_62,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_63,negated_conjecture,
    ( m1_subset_1(esk8_0,u1_struct_0(esk6_0))
    | r1_tarski(esk7_0,k5_waybel_0(esk6_0,esk3_2(esk6_0,esk7_0))) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(esk4_2(k5_waybel_0(esk6_0,esk3_2(esk6_0,esk7_0)),X1),esk7_0)
    | m1_subset_1(esk8_0,u1_struct_0(esk6_0))
    | r1_tarski(k5_waybel_0(esk6_0,esk3_2(esk6_0,esk7_0)),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61])).

cnf(c_0_65,negated_conjecture,
    ( ~ v14_waybel_0(esk7_0,esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0))
    | esk7_0 != k5_waybel_0(esk6_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_66,negated_conjecture,
    ( k5_waybel_0(esk6_0,esk3_2(esk6_0,esk7_0)) = esk7_0
    | m1_subset_1(esk8_0,u1_struct_0(esk6_0))
    | ~ r1_tarski(k5_waybel_0(esk6_0,esk3_2(esk6_0,esk7_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_67,negated_conjecture,
    ( m1_subset_1(esk8_0,u1_struct_0(esk6_0))
    | r1_tarski(k5_waybel_0(esk6_0,esk3_2(esk6_0,esk7_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_64])).

fof(c_0_68,plain,(
    ! [X33,X34,X35] :
      ( v2_struct_0(X33)
      | ~ v3_orders_2(X33)
      | ~ l1_orders_2(X33)
      | ~ m1_subset_1(X34,u1_struct_0(X33))
      | ~ m1_subset_1(X35,u1_struct_0(X33))
      | r3_orders_2(X33,X34,X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[reflexivity_r3_orders_2])])])).

fof(c_0_69,plain,(
    ! [X30,X31,X32] :
      ( ( ~ r3_orders_2(X30,X31,X32)
        | r1_orders_2(X30,X31,X32)
        | v2_struct_0(X30)
        | ~ v3_orders_2(X30)
        | ~ l1_orders_2(X30)
        | ~ m1_subset_1(X31,u1_struct_0(X30))
        | ~ m1_subset_1(X32,u1_struct_0(X30)) )
      & ( ~ r1_orders_2(X30,X31,X32)
        | r3_orders_2(X30,X31,X32)
        | v2_struct_0(X30)
        | ~ v3_orders_2(X30)
        | ~ l1_orders_2(X30)
        | ~ m1_subset_1(X31,u1_struct_0(X30))
        | ~ m1_subset_1(X32,u1_struct_0(X30)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).

cnf(c_0_70,negated_conjecture,
    ( m1_subset_1(esk8_0,u1_struct_0(esk6_0))
    | k5_waybel_0(esk6_0,X1) != esk7_0
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_26])).

cnf(c_0_71,negated_conjecture,
    ( k5_waybel_0(esk6_0,esk3_2(esk6_0,esk7_0)) = esk7_0
    | m1_subset_1(esk8_0,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_72,plain,
    ( v2_struct_0(X1)
    | r3_orders_2(X1,X2,X2)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_73,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_74,negated_conjecture,
    ( m1_subset_1(esk8_0,u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_30])).

cnf(c_0_75,plain,
    ( r3_orders_2(X1,X2,X2)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(condense,[status(thm)],[c_0_72])).

cnf(c_0_76,negated_conjecture,
    ( r1_orders_2(esk6_0,X1,esk8_0)
    | ~ r3_orders_2(esk6_0,X1,esk8_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_18]),c_0_20])]),c_0_22])).

cnf(c_0_77,negated_conjecture,
    ( r3_orders_2(esk6_0,esk8_0,esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_74]),c_0_18]),c_0_20])]),c_0_22])).

cnf(c_0_78,negated_conjecture,
    ( r2_hidden(X1,k5_waybel_0(esk6_0,esk8_0))
    | ~ r1_orders_2(esk6_0,X1,esk8_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_74]),c_0_20])]),c_0_22])).

cnf(c_0_79,negated_conjecture,
    ( r1_orders_2(esk6_0,esk8_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_74])])).

cnf(c_0_80,negated_conjecture,
    ( r2_hidden(esk8_0,k5_waybel_0(esk6_0,esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_74])])).

cnf(c_0_81,negated_conjecture,
    ( esk7_0 = k5_waybel_0(esk6_0,esk8_0)
    | v14_waybel_0(esk7_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_82,negated_conjecture,
    ( v14_waybel_0(esk7_0,esk6_0)
    | r2_hidden(esk8_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_83,negated_conjecture,
    ( r2_hidden(esk8_0,esk7_0)
    | m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_82])).

cnf(c_0_84,negated_conjecture,
    ( r2_hidden(esk8_0,esk7_0)
    | m1_subset_1(k5_waybel_0(esk6_0,esk3_2(esk6_0,esk7_0)),k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_83]),c_0_20])]),c_0_22])).

cnf(c_0_85,negated_conjecture,
    ( r2_hidden(esk8_0,esk7_0)
    | m1_subset_1(X1,u1_struct_0(esk6_0))
    | ~ r2_hidden(X1,k5_waybel_0(esk6_0,esk3_2(esk6_0,esk7_0))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_84])).

cnf(c_0_86,negated_conjecture,
    ( r2_lattice3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))
    | r2_hidden(esk8_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_82])).

cnf(c_0_87,negated_conjecture,
    ( r2_hidden(esk8_0,esk7_0)
    | m1_subset_1(esk4_2(k5_waybel_0(esk6_0,esk3_2(esk6_0,esk7_0)),X1),u1_struct_0(esk6_0))
    | r1_tarski(k5_waybel_0(esk6_0,esk3_2(esk6_0,esk7_0)),X1) ),
    inference(spm,[status(thm)],[c_0_85,c_0_34])).

cnf(c_0_88,negated_conjecture,
    ( r2_hidden(X1,k5_waybel_0(esk6_0,esk3_2(esk6_0,esk7_0)))
    | r2_hidden(esk8_0,esk7_0)
    | ~ r1_orders_2(esk6_0,X1,esk3_2(esk6_0,esk7_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_83]),c_0_20])]),c_0_22])).

cnf(c_0_89,negated_conjecture,
    ( r1_orders_2(esk6_0,esk4_2(esk7_0,X1),esk3_2(esk6_0,esk7_0))
    | r2_hidden(esk8_0,esk7_0)
    | r1_tarski(esk7_0,X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_86]),c_0_83]),c_0_34])).

cnf(c_0_90,negated_conjecture,
    ( r2_hidden(esk4_2(k5_waybel_0(esk6_0,esk3_2(esk6_0,esk7_0)),X1),X2)
    | r2_hidden(esk8_0,esk7_0)
    | r1_tarski(k5_waybel_0(esk6_0,esk3_2(esk6_0,esk7_0)),X1)
    | ~ r1_orders_2(esk6_0,esk4_2(k5_waybel_0(esk6_0,esk3_2(esk6_0,esk7_0)),X1),X3)
    | ~ r2_hidden(X3,X2)
    | ~ v12_waybel_0(X2,esk6_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_87]),c_0_20])])).

cnf(c_0_91,negated_conjecture,
    ( r1_orders_2(esk6_0,X1,esk3_2(esk6_0,esk7_0))
    | r2_hidden(esk8_0,esk7_0)
    | ~ r2_hidden(X1,k5_waybel_0(esk6_0,esk3_2(esk6_0,esk7_0))) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_83]),c_0_20])]),c_0_22]),c_0_85])).

cnf(c_0_92,negated_conjecture,
    ( r2_hidden(esk4_2(esk7_0,X1),k5_waybel_0(esk6_0,esk3_2(esk6_0,esk7_0)))
    | r2_hidden(esk8_0,esk7_0)
    | r1_tarski(esk7_0,X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_40]),c_0_89])).

cnf(c_0_93,negated_conjecture,
    ( r2_hidden(esk4_2(k5_waybel_0(esk6_0,esk3_2(esk6_0,esk7_0)),X1),esk7_0)
    | r2_hidden(esk8_0,esk7_0)
    | r1_tarski(k5_waybel_0(esk6_0,esk3_2(esk6_0,esk7_0)),X1)
    | ~ r1_orders_2(esk6_0,esk4_2(k5_waybel_0(esk6_0,esk3_2(esk6_0,esk7_0)),X1),X2)
    | ~ r2_hidden(X2,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_19]),c_0_15])])).

cnf(c_0_94,negated_conjecture,
    ( r2_hidden(esk3_2(esk6_0,esk7_0),esk7_0)
    | r2_hidden(esk8_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_82])).

cnf(c_0_95,negated_conjecture,
    ( r1_orders_2(esk6_0,esk4_2(k5_waybel_0(esk6_0,esk3_2(esk6_0,esk7_0)),X1),esk3_2(esk6_0,esk7_0))
    | r2_hidden(esk8_0,esk7_0)
    | r1_tarski(k5_waybel_0(esk6_0,esk3_2(esk6_0,esk7_0)),X1) ),
    inference(spm,[status(thm)],[c_0_91,c_0_34])).

cnf(c_0_96,negated_conjecture,
    ( m1_subset_1(k5_waybel_0(esk6_0,esk8_0),k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_74]),c_0_20])]),c_0_22])).

cnf(c_0_97,negated_conjecture,
    ( r2_hidden(esk8_0,esk7_0)
    | r1_tarski(esk7_0,k5_waybel_0(esk6_0,esk3_2(esk6_0,esk7_0))) ),
    inference(spm,[status(thm)],[c_0_57,c_0_92])).

cnf(c_0_98,negated_conjecture,
    ( r2_hidden(esk4_2(k5_waybel_0(esk6_0,esk3_2(esk6_0,esk7_0)),X1),esk7_0)
    | r2_hidden(esk8_0,esk7_0)
    | r1_tarski(k5_waybel_0(esk6_0,esk3_2(esk6_0,esk7_0)),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_95])).

cnf(c_0_99,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk6_0))
    | ~ r2_hidden(X1,k5_waybel_0(esk6_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_96])).

cnf(c_0_100,plain,
    ( v14_waybel_0(X3,X2)
    | v1_xboole_0(X3)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_hidden(X1,X3)
    | ~ r2_lattice3(X2,X3,X1)
    | ~ v1_waybel_0(X3,X2)
    | ~ v12_waybel_0(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_101,negated_conjecture,
    ( k5_waybel_0(esk6_0,esk3_2(esk6_0,esk7_0)) = esk7_0
    | r2_hidden(esk8_0,esk7_0)
    | ~ r1_tarski(k5_waybel_0(esk6_0,esk3_2(esk6_0,esk7_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_97])).

cnf(c_0_102,negated_conjecture,
    ( r2_hidden(esk8_0,esk7_0)
    | r1_tarski(k5_waybel_0(esk6_0,esk3_2(esk6_0,esk7_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_98])).

cnf(c_0_103,negated_conjecture,
    ( r1_orders_2(esk6_0,X1,esk8_0)
    | ~ r2_hidden(X1,k5_waybel_0(esk6_0,esk8_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_74]),c_0_20])]),c_0_22]),c_0_99])).

cnf(c_0_104,plain,
    ( r2_hidden(esk5_3(X1,X2,X3),X2)
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_105,plain,
    ( r2_lattice3(X1,X2,X3)
    | ~ r1_orders_2(X1,esk5_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_106,plain,
    ( v14_waybel_0(X1,X2)
    | v1_xboole_0(X1)
    | v2_struct_0(X2)
    | ~ r2_lattice3(X2,X1,X3)
    | ~ v1_waybel_0(X1,X2)
    | ~ v4_orders_2(X2)
    | ~ v3_orders_2(X2)
    | ~ r2_hidden(X3,X1)
    | ~ v12_waybel_0(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[c_0_100,c_0_27])).

cnf(c_0_107,negated_conjecture,
    ( r2_hidden(esk8_0,esk7_0)
    | k5_waybel_0(esk6_0,X1) != esk7_0
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_82])).

cnf(c_0_108,negated_conjecture,
    ( k5_waybel_0(esk6_0,esk3_2(esk6_0,esk7_0)) = esk7_0
    | r2_hidden(esk8_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_101,c_0_102])).

cnf(c_0_109,negated_conjecture,
    ( v14_waybel_0(esk7_0,esk6_0)
    | r1_orders_2(esk6_0,X1,esk8_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_103,c_0_81])).

cnf(c_0_110,negated_conjecture,
    ( r2_lattice3(esk6_0,X1,esk8_0)
    | r2_hidden(esk5_3(esk6_0,X1,esk8_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_74]),c_0_20])])).

cnf(c_0_111,negated_conjecture,
    ( r2_lattice3(esk6_0,X1,esk8_0)
    | ~ r1_orders_2(esk6_0,esk5_3(esk6_0,X1,esk8_0),esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_74]),c_0_20])])).

cnf(c_0_112,negated_conjecture,
    ( v14_waybel_0(esk7_0,esk6_0)
    | ~ r2_lattice3(esk6_0,esk7_0,X1)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_15]),c_0_16]),c_0_17]),c_0_18]),c_0_19]),c_0_20])]),c_0_21]),c_0_22])).

cnf(c_0_113,negated_conjecture,
    ( r2_hidden(esk8_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_108]),c_0_83])).

cnf(c_0_114,negated_conjecture,
    ( r2_lattice3(esk6_0,esk7_0,esk8_0)
    | v14_waybel_0(esk7_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_110]),c_0_111])).

cnf(c_0_115,negated_conjecture,
    ( v14_waybel_0(esk7_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_113]),c_0_114])).

cnf(c_0_116,negated_conjecture,
    ( m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_115])])).

cnf(c_0_117,negated_conjecture,
    ( m1_subset_1(k5_waybel_0(esk6_0,esk3_2(esk6_0,esk7_0)),k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_116]),c_0_20])]),c_0_22])).

cnf(c_0_118,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk6_0))
    | ~ r2_hidden(X1,k5_waybel_0(esk6_0,esk3_2(esk6_0,esk7_0))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_117])).

cnf(c_0_119,negated_conjecture,
    ( r2_lattice3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_115])])).

cnf(c_0_120,negated_conjecture,
    ( m1_subset_1(esk4_2(k5_waybel_0(esk6_0,esk3_2(esk6_0,esk7_0)),X1),u1_struct_0(esk6_0))
    | r1_tarski(k5_waybel_0(esk6_0,esk3_2(esk6_0,esk7_0)),X1) ),
    inference(spm,[status(thm)],[c_0_118,c_0_34])).

cnf(c_0_121,negated_conjecture,
    ( r2_hidden(X1,k5_waybel_0(esk6_0,esk3_2(esk6_0,esk7_0)))
    | ~ r1_orders_2(esk6_0,X1,esk3_2(esk6_0,esk7_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_116]),c_0_20])]),c_0_22])).

cnf(c_0_122,negated_conjecture,
    ( r1_orders_2(esk6_0,esk4_2(esk7_0,X1),esk3_2(esk6_0,esk7_0))
    | r1_tarski(esk7_0,X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_119]),c_0_116])]),c_0_34])).

cnf(c_0_123,negated_conjecture,
    ( r2_hidden(esk4_2(k5_waybel_0(esk6_0,esk3_2(esk6_0,esk7_0)),X1),X2)
    | r1_tarski(k5_waybel_0(esk6_0,esk3_2(esk6_0,esk7_0)),X1)
    | ~ r1_orders_2(esk6_0,esk4_2(k5_waybel_0(esk6_0,esk3_2(esk6_0,esk7_0)),X1),X3)
    | ~ r2_hidden(X3,X2)
    | ~ v12_waybel_0(X2,esk6_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_120]),c_0_20])])).

cnf(c_0_124,negated_conjecture,
    ( r1_orders_2(esk6_0,X1,esk3_2(esk6_0,esk7_0))
    | ~ r2_hidden(X1,k5_waybel_0(esk6_0,esk3_2(esk6_0,esk7_0))) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_116]),c_0_20])]),c_0_22]),c_0_118])).

cnf(c_0_125,negated_conjecture,
    ( r2_hidden(esk4_2(esk7_0,X1),k5_waybel_0(esk6_0,esk3_2(esk6_0,esk7_0)))
    | r1_tarski(esk7_0,X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_40]),c_0_122])).

cnf(c_0_126,negated_conjecture,
    ( r2_hidden(esk4_2(k5_waybel_0(esk6_0,esk3_2(esk6_0,esk7_0)),X1),esk7_0)
    | r1_tarski(k5_waybel_0(esk6_0,esk3_2(esk6_0,esk7_0)),X1)
    | ~ r1_orders_2(esk6_0,esk4_2(k5_waybel_0(esk6_0,esk3_2(esk6_0,esk7_0)),X1),X2)
    | ~ r2_hidden(X2,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_19]),c_0_15])])).

cnf(c_0_127,negated_conjecture,
    ( r2_hidden(esk3_2(esk6_0,esk7_0),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_115])])).

cnf(c_0_128,negated_conjecture,
    ( r1_orders_2(esk6_0,esk4_2(k5_waybel_0(esk6_0,esk3_2(esk6_0,esk7_0)),X1),esk3_2(esk6_0,esk7_0))
    | r1_tarski(k5_waybel_0(esk6_0,esk3_2(esk6_0,esk7_0)),X1) ),
    inference(spm,[status(thm)],[c_0_124,c_0_34])).

cnf(c_0_129,negated_conjecture,
    ( r1_tarski(esk7_0,k5_waybel_0(esk6_0,esk3_2(esk6_0,esk7_0))) ),
    inference(spm,[status(thm)],[c_0_57,c_0_125])).

cnf(c_0_130,negated_conjecture,
    ( r2_hidden(esk4_2(k5_waybel_0(esk6_0,esk3_2(esk6_0,esk7_0)),X1),esk7_0)
    | r1_tarski(k5_waybel_0(esk6_0,esk3_2(esk6_0,esk7_0)),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_126,c_0_127]),c_0_128])).

cnf(c_0_131,negated_conjecture,
    ( k5_waybel_0(esk6_0,esk3_2(esk6_0,esk7_0)) = esk7_0
    | ~ r1_tarski(k5_waybel_0(esk6_0,esk3_2(esk6_0,esk7_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_129])).

cnf(c_0_132,negated_conjecture,
    ( r1_tarski(k5_waybel_0(esk6_0,esk3_2(esk6_0,esk7_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_130])).

cnf(c_0_133,negated_conjecture,
    ( k5_waybel_0(esk6_0,X1) != esk7_0
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_115])])).

cnf(c_0_134,negated_conjecture,
    ( k5_waybel_0(esk6_0,esk3_2(esk6_0,esk7_0)) = esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_131,c_0_132])])).

cnf(c_0_135,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_133,c_0_134]),c_0_116])]),
    [proof]).

%------------------------------------------------------------------------------
