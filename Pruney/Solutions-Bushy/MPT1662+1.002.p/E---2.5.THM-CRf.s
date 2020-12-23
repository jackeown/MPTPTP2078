%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1662+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:33 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  107 (4051 expanded)
%              Number of clauses        :   78 (1462 expanded)
%              Number of leaves         :   14 ( 995 expanded)
%              Depth                    :   21
%              Number of atoms          :  557 (41013 expanded)
%              Number of equality atoms :   22 (2604 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal clause size      :   67 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t42_waybel_0,conjecture,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & v1_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v12_waybel_0(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => ( v1_waybel_0(X2,X1)
          <=> ! [X3] :
                ( ( v1_finset_1(X3)
                  & m1_subset_1(X3,k1_zfmisc_1(X2)) )
               => ( X3 != k1_xboole_0
                 => r2_hidden(k1_yellow_0(X1,X3),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_waybel_0)).

fof(cc1_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v1_lattice3(X1)
       => ~ v2_struct_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattice3)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t1_waybel_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v4_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( ( ~ v1_xboole_0(X2)
              & v1_waybel_0(X2,X1) )
          <=> ! [X3] :
                ( ( v1_finset_1(X3)
                  & m1_subset_1(X3,k1_zfmisc_1(X2)) )
               => ? [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                    & r2_hidden(X4,X2)
                    & r2_lattice3(X1,X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_waybel_0)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(t54_yellow_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ( v1_lattice3(X1)
      <=> ! [X2] :
            ( ( ~ v1_xboole_0(X2)
              & v1_finset_1(X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
           => r1_yellow_0(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_yellow_0)).

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

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

fof(t6_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( r2_lattice3(X1,k1_xboole_0,X2)
            & r1_lattice3(X1,k1_xboole_0,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_yellow_0)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_waybel_0)).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1] :
        ( ( v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & v1_lattice3(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( ( ~ v1_xboole_0(X2)
              & v12_waybel_0(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
           => ( v1_waybel_0(X2,X1)
            <=> ! [X3] :
                  ( ( v1_finset_1(X3)
                    & m1_subset_1(X3,k1_zfmisc_1(X2)) )
                 => ( X3 != k1_xboole_0
                   => r2_hidden(k1_yellow_0(X1,X3),X2) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t42_waybel_0])).

fof(c_0_15,plain,(
    ! [X5] :
      ( ~ l1_orders_2(X5)
      | ~ v1_lattice3(X5)
      | ~ v2_struct_0(X5) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattice3])])])).

fof(c_0_16,negated_conjecture,(
    ! [X47] :
      ( v3_orders_2(esk8_0)
      & v4_orders_2(esk8_0)
      & v5_orders_2(esk8_0)
      & v1_lattice3(esk8_0)
      & l1_orders_2(esk8_0)
      & ~ v1_xboole_0(esk9_0)
      & v12_waybel_0(esk9_0,esk8_0)
      & m1_subset_1(esk9_0,k1_zfmisc_1(u1_struct_0(esk8_0)))
      & ( v1_finset_1(esk10_0)
        | ~ v1_waybel_0(esk9_0,esk8_0) )
      & ( m1_subset_1(esk10_0,k1_zfmisc_1(esk9_0))
        | ~ v1_waybel_0(esk9_0,esk8_0) )
      & ( esk10_0 != k1_xboole_0
        | ~ v1_waybel_0(esk9_0,esk8_0) )
      & ( ~ r2_hidden(k1_yellow_0(esk8_0,esk10_0),esk9_0)
        | ~ v1_waybel_0(esk9_0,esk8_0) )
      & ( v1_waybel_0(esk9_0,esk8_0)
        | ~ v1_finset_1(X47)
        | ~ m1_subset_1(X47,k1_zfmisc_1(esk9_0))
        | X47 = k1_xboole_0
        | r2_hidden(k1_yellow_0(esk8_0,X47),esk9_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])])])).

fof(c_0_17,plain,(
    ! [X33,X34] :
      ( ( ~ m1_subset_1(X33,k1_zfmisc_1(X34))
        | r1_tarski(X33,X34) )
      & ( ~ r1_tarski(X33,X34)
        | m1_subset_1(X33,k1_zfmisc_1(X34)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_18,plain,(
    ! [X16,X17,X18,X21] :
      ( ( m1_subset_1(esk4_3(X16,X17,X18),u1_struct_0(X16))
        | ~ v1_finset_1(X18)
        | ~ m1_subset_1(X18,k1_zfmisc_1(X17))
        | v1_xboole_0(X17)
        | ~ v1_waybel_0(X17,X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
        | v2_struct_0(X16)
        | ~ v4_orders_2(X16)
        | ~ l1_orders_2(X16) )
      & ( r2_hidden(esk4_3(X16,X17,X18),X17)
        | ~ v1_finset_1(X18)
        | ~ m1_subset_1(X18,k1_zfmisc_1(X17))
        | v1_xboole_0(X17)
        | ~ v1_waybel_0(X17,X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
        | v2_struct_0(X16)
        | ~ v4_orders_2(X16)
        | ~ l1_orders_2(X16) )
      & ( r2_lattice3(X16,X18,esk4_3(X16,X17,X18))
        | ~ v1_finset_1(X18)
        | ~ m1_subset_1(X18,k1_zfmisc_1(X17))
        | v1_xboole_0(X17)
        | ~ v1_waybel_0(X17,X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
        | v2_struct_0(X16)
        | ~ v4_orders_2(X16)
        | ~ l1_orders_2(X16) )
      & ( ~ v1_xboole_0(X17)
        | v1_finset_1(esk5_2(X16,X17))
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
        | v2_struct_0(X16)
        | ~ v4_orders_2(X16)
        | ~ l1_orders_2(X16) )
      & ( v1_waybel_0(X17,X16)
        | v1_finset_1(esk5_2(X16,X17))
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
        | v2_struct_0(X16)
        | ~ v4_orders_2(X16)
        | ~ l1_orders_2(X16) )
      & ( ~ v1_xboole_0(X17)
        | m1_subset_1(esk5_2(X16,X17),k1_zfmisc_1(X17))
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
        | v2_struct_0(X16)
        | ~ v4_orders_2(X16)
        | ~ l1_orders_2(X16) )
      & ( v1_waybel_0(X17,X16)
        | m1_subset_1(esk5_2(X16,X17),k1_zfmisc_1(X17))
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
        | v2_struct_0(X16)
        | ~ v4_orders_2(X16)
        | ~ l1_orders_2(X16) )
      & ( ~ v1_xboole_0(X17)
        | ~ m1_subset_1(X21,u1_struct_0(X16))
        | ~ r2_hidden(X21,X17)
        | ~ r2_lattice3(X16,esk5_2(X16,X17),X21)
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
        | v2_struct_0(X16)
        | ~ v4_orders_2(X16)
        | ~ l1_orders_2(X16) )
      & ( v1_waybel_0(X17,X16)
        | ~ m1_subset_1(X21,u1_struct_0(X16))
        | ~ r2_hidden(X21,X17)
        | ~ r2_lattice3(X16,esk5_2(X16,X17),X21)
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
        | v2_struct_0(X16)
        | ~ v4_orders_2(X16)
        | ~ l1_orders_2(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t1_waybel_0])])])])])])).

cnf(c_0_19,plain,
    ( ~ l1_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( v1_lattice3(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( l1_orders_2(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_22,plain,(
    ! [X22,X23,X24] :
      ( ~ r1_tarski(X22,X23)
      | ~ r1_tarski(X23,X24)
      | r1_tarski(X22,X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_23,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( v1_waybel_0(X1,X2)
    | m1_subset_1(esk5_2(X2,X1),k1_zfmisc_1(X1))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v4_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( v4_orders_2(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_27,negated_conjecture,
    ( ~ v2_struct_0(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( r1_tarski(esk9_0,u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( v1_waybel_0(esk9_0,esk8_0)
    | m1_subset_1(esk5_2(esk8_0,esk9_0),k1_zfmisc_1(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_24]),c_0_26]),c_0_21])]),c_0_27])).

fof(c_0_31,plain,(
    ! [X35,X36,X37] :
      ( ~ r2_hidden(X35,X36)
      | ~ m1_subset_1(X36,k1_zfmisc_1(X37))
      | m1_subset_1(X35,X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_32,plain,(
    ! [X38,X39] :
      ( ( ~ v1_lattice3(X38)
        | v1_xboole_0(X39)
        | ~ v1_finset_1(X39)
        | ~ m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38)))
        | r1_yellow_0(X38,X39)
        | v2_struct_0(X38)
        | ~ v3_orders_2(X38)
        | ~ v4_orders_2(X38)
        | ~ v5_orders_2(X38)
        | ~ l1_orders_2(X38) )
      & ( ~ v1_xboole_0(esk7_1(X38))
        | v1_lattice3(X38)
        | v2_struct_0(X38)
        | ~ v3_orders_2(X38)
        | ~ v4_orders_2(X38)
        | ~ v5_orders_2(X38)
        | ~ l1_orders_2(X38) )
      & ( v1_finset_1(esk7_1(X38))
        | v1_lattice3(X38)
        | v2_struct_0(X38)
        | ~ v3_orders_2(X38)
        | ~ v4_orders_2(X38)
        | ~ v5_orders_2(X38)
        | ~ l1_orders_2(X38) )
      & ( m1_subset_1(esk7_1(X38),k1_zfmisc_1(u1_struct_0(X38)))
        | v1_lattice3(X38)
        | v2_struct_0(X38)
        | ~ v3_orders_2(X38)
        | ~ v4_orders_2(X38)
        | ~ v5_orders_2(X38)
        | ~ l1_orders_2(X38) )
      & ( ~ r1_yellow_0(X38,esk7_1(X38))
        | v1_lattice3(X38)
        | v2_struct_0(X38)
        | ~ v3_orders_2(X38)
        | ~ v4_orders_2(X38)
        | ~ v5_orders_2(X38)
        | ~ l1_orders_2(X38) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t54_yellow_0])])])])])])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk8_0))
    | ~ r1_tarski(X1,esk9_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(esk5_2(esk8_0,esk9_0),esk9_0)
    | v1_waybel_0(esk9_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_30])).

cnf(c_0_35,plain,
    ( v1_waybel_0(X1,X2)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ r2_hidden(X3,X1)
    | ~ r2_lattice3(X2,esk5_2(X2,X1),X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v4_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_36,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_37,plain,
    ( v1_waybel_0(X1,X2)
    | v1_finset_1(esk5_2(X2,X1))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v4_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_38,plain,(
    ! [X27,X28,X29,X30,X31] :
      ( ( r2_lattice3(X27,X29,X28)
        | X28 != k1_yellow_0(X27,X29)
        | ~ r1_yellow_0(X27,X29)
        | ~ m1_subset_1(X28,u1_struct_0(X27))
        | ~ v5_orders_2(X27)
        | ~ l1_orders_2(X27) )
      & ( ~ m1_subset_1(X30,u1_struct_0(X27))
        | ~ r2_lattice3(X27,X29,X30)
        | r1_orders_2(X27,X28,X30)
        | X28 != k1_yellow_0(X27,X29)
        | ~ r1_yellow_0(X27,X29)
        | ~ m1_subset_1(X28,u1_struct_0(X27))
        | ~ v5_orders_2(X27)
        | ~ l1_orders_2(X27) )
      & ( X28 = k1_yellow_0(X27,X31)
        | m1_subset_1(esk6_3(X27,X28,X31),u1_struct_0(X27))
        | ~ r2_lattice3(X27,X31,X28)
        | ~ m1_subset_1(X28,u1_struct_0(X27))
        | ~ v5_orders_2(X27)
        | ~ l1_orders_2(X27) )
      & ( r1_yellow_0(X27,X31)
        | m1_subset_1(esk6_3(X27,X28,X31),u1_struct_0(X27))
        | ~ r2_lattice3(X27,X31,X28)
        | ~ m1_subset_1(X28,u1_struct_0(X27))
        | ~ v5_orders_2(X27)
        | ~ l1_orders_2(X27) )
      & ( X28 = k1_yellow_0(X27,X31)
        | r2_lattice3(X27,X31,esk6_3(X27,X28,X31))
        | ~ r2_lattice3(X27,X31,X28)
        | ~ m1_subset_1(X28,u1_struct_0(X27))
        | ~ v5_orders_2(X27)
        | ~ l1_orders_2(X27) )
      & ( r1_yellow_0(X27,X31)
        | r2_lattice3(X27,X31,esk6_3(X27,X28,X31))
        | ~ r2_lattice3(X27,X31,X28)
        | ~ m1_subset_1(X28,u1_struct_0(X27))
        | ~ v5_orders_2(X27)
        | ~ l1_orders_2(X27) )
      & ( X28 = k1_yellow_0(X27,X31)
        | ~ r1_orders_2(X27,X28,esk6_3(X27,X28,X31))
        | ~ r2_lattice3(X27,X31,X28)
        | ~ m1_subset_1(X28,u1_struct_0(X27))
        | ~ v5_orders_2(X27)
        | ~ l1_orders_2(X27) )
      & ( r1_yellow_0(X27,X31)
        | ~ r1_orders_2(X27,X28,esk6_3(X27,X28,X31))
        | ~ r2_lattice3(X27,X31,X28)
        | ~ m1_subset_1(X28,u1_struct_0(X27))
        | ~ v5_orders_2(X27)
        | ~ l1_orders_2(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_yellow_0])])])])])])).

fof(c_0_39,plain,(
    ! [X12,X13] :
      ( ~ l1_orders_2(X12)
      | m1_subset_1(k1_yellow_0(X12,X13),u1_struct_0(X12)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_yellow_0])])).

cnf(c_0_40,plain,
    ( v1_xboole_0(X2)
    | r1_yellow_0(X1,X2)
    | v2_struct_0(X1)
    | ~ v1_lattice3(X1)
    | ~ v1_finset_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_41,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))
    | v1_waybel_0(esk9_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

fof(c_0_43,plain,(
    ! [X25,X26] :
      ( ~ m1_subset_1(X25,X26)
      | v1_xboole_0(X26)
      | r2_hidden(X25,X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_44,plain,(
    ! [X14] : m1_subset_1(esk3_1(X14),X14) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

cnf(c_0_45,plain,
    ( v1_waybel_0(X1,X2)
    | v2_struct_0(X2)
    | ~ r2_lattice3(X2,esk5_2(X2,X1),X3)
    | ~ v4_orders_2(X2)
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_46,negated_conjecture,
    ( v1_waybel_0(esk9_0,esk8_0)
    | X1 = k1_xboole_0
    | r2_hidden(k1_yellow_0(esk8_0,X1),esk9_0)
    | ~ v1_finset_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_47,negated_conjecture,
    ( v1_finset_1(esk5_2(esk8_0,esk9_0))
    | v1_waybel_0(esk9_0,esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_24]),c_0_26]),c_0_21])]),c_0_27])).

cnf(c_0_48,plain,
    ( r2_lattice3(X1,X2,X3)
    | X3 != k1_yellow_0(X1,X2)
    | ~ r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_49,plain,
    ( m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_50,plain,
    ( r1_yellow_0(X1,X2)
    | v1_xboole_0(X2)
    | ~ v3_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_finset_1(X2)
    | ~ v4_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[c_0_40,c_0_19])).

cnf(c_0_51,negated_conjecture,
    ( v1_waybel_0(esk9_0,esk8_0)
    | m1_subset_1(esk5_2(esk8_0,esk9_0),k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_52,negated_conjecture,
    ( v3_orders_2(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_53,negated_conjecture,
    ( v5_orders_2(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_54,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_55,plain,
    ( m1_subset_1(esk3_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_56,negated_conjecture,
    ( v1_waybel_0(esk9_0,esk8_0)
    | ~ r2_lattice3(esk8_0,esk5_2(esk8_0,esk9_0),X1)
    | ~ r2_hidden(X1,esk9_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_24]),c_0_26]),c_0_21])]),c_0_27])).

cnf(c_0_57,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_xboole_0
    | v1_waybel_0(esk9_0,esk8_0)
    | r2_hidden(k1_yellow_0(esk8_0,esk5_2(esk8_0,esk9_0)),esk9_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_30]),c_0_47])).

cnf(c_0_58,plain,
    ( r2_lattice3(X1,X2,k1_yellow_0(X1,X2))
    | ~ r1_yellow_0(X1,X2)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_48]),c_0_49])).

cnf(c_0_59,negated_conjecture,
    ( r1_yellow_0(esk8_0,esk5_2(esk8_0,esk9_0))
    | v1_waybel_0(esk9_0,esk8_0)
    | v1_xboole_0(esk5_2(esk8_0,esk9_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52]),c_0_53]),c_0_26]),c_0_20]),c_0_21])]),c_0_47])).

fof(c_0_60,plain,(
    ! [X41] :
      ( ~ v1_xboole_0(X41)
      | X41 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

fof(c_0_61,plain,(
    ! [X42,X43] :
      ( ( r2_lattice3(X42,k1_xboole_0,X43)
        | ~ m1_subset_1(X43,u1_struct_0(X42))
        | ~ l1_orders_2(X42) )
      & ( r1_lattice3(X42,k1_xboole_0,X43)
        | ~ m1_subset_1(X43,u1_struct_0(X42))
        | ~ l1_orders_2(X42) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_yellow_0])])])])).

cnf(c_0_62,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk8_0))
    | ~ r2_hidden(X1,esk9_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_24])).

cnf(c_0_63,plain,
    ( v1_xboole_0(X1)
    | r2_hidden(esk3_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_64,negated_conjecture,
    ( ~ v1_xboole_0(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_65,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_xboole_0
    | v1_waybel_0(esk9_0,esk8_0)
    | ~ r2_lattice3(esk8_0,esk5_2(esk8_0,esk9_0),k1_yellow_0(esk8_0,esk5_2(esk8_0,esk9_0))) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_66,negated_conjecture,
    ( r2_lattice3(esk8_0,esk5_2(esk8_0,esk9_0),k1_yellow_0(esk8_0,esk5_2(esk8_0,esk9_0)))
    | v1_waybel_0(esk9_0,esk8_0)
    | v1_xboole_0(esk5_2(esk8_0,esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_53]),c_0_21])])).

cnf(c_0_67,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_68,plain,
    ( r2_lattice3(X1,k1_xboole_0,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_69,negated_conjecture,
    ( m1_subset_1(esk3_1(esk9_0),u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64])).

cnf(c_0_70,negated_conjecture,
    ( v1_waybel_0(esk9_0,esk8_0)
    | ~ r2_lattice3(esk8_0,esk5_2(esk8_0,esk9_0),esk3_1(esk9_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_63]),c_0_64])).

cnf(c_0_71,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_xboole_0
    | v1_waybel_0(esk9_0,esk8_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67])).

cnf(c_0_72,negated_conjecture,
    ( r2_lattice3(esk8_0,k1_xboole_0,esk3_1(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_21])])).

cnf(c_0_73,negated_conjecture,
    ( m1_subset_1(esk10_0,k1_zfmisc_1(esk9_0))
    | ~ v1_waybel_0(esk9_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_74,negated_conjecture,
    ( v1_waybel_0(esk9_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_72])])).

cnf(c_0_75,negated_conjecture,
    ( v1_finset_1(esk10_0)
    | ~ v1_waybel_0(esk9_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_76,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),X2)
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ v1_finset_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ v1_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_77,negated_conjecture,
    ( m1_subset_1(esk10_0,k1_zfmisc_1(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_74])])).

cnf(c_0_78,negated_conjecture,
    ( v1_finset_1(esk10_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_74])])).

fof(c_0_79,plain,(
    ! [X6,X7,X8,X9] :
      ( ( ~ v12_waybel_0(X7,X6)
        | ~ m1_subset_1(X8,u1_struct_0(X6))
        | ~ m1_subset_1(X9,u1_struct_0(X6))
        | ~ r2_hidden(X8,X7)
        | ~ r1_orders_2(X6,X9,X8)
        | r2_hidden(X9,X7)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ l1_orders_2(X6) )
      & ( m1_subset_1(esk1_2(X6,X7),u1_struct_0(X6))
        | v12_waybel_0(X7,X6)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ l1_orders_2(X6) )
      & ( m1_subset_1(esk2_2(X6,X7),u1_struct_0(X6))
        | v12_waybel_0(X7,X6)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ l1_orders_2(X6) )
      & ( r2_hidden(esk1_2(X6,X7),X7)
        | v12_waybel_0(X7,X6)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ l1_orders_2(X6) )
      & ( r1_orders_2(X6,esk2_2(X6,X7),esk1_2(X6,X7))
        | v12_waybel_0(X7,X6)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ l1_orders_2(X6) )
      & ( ~ r2_hidden(esk2_2(X6,X7),X7)
        | v12_waybel_0(X7,X6)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ l1_orders_2(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_waybel_0])])])])])).

cnf(c_0_80,negated_conjecture,
    ( r2_hidden(esk4_3(X1,esk9_0,esk10_0),esk9_0)
    | v2_struct_0(X1)
    | ~ v1_waybel_0(esk9_0,X1)
    | ~ v4_orders_2(X1)
    | ~ m1_subset_1(esk9_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_78])]),c_0_64])).

cnf(c_0_81,negated_conjecture,
    ( r1_tarski(esk10_0,esk9_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_77])).

cnf(c_0_82,plain,
    ( r2_hidden(X4,X1)
    | ~ v12_waybel_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r2_hidden(X3,X1)
    | ~ r1_orders_2(X2,X4,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_83,plain,
    ( r1_orders_2(X2,X4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X1)
    | X4 != k1_yellow_0(X2,X3)
    | ~ r1_yellow_0(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_84,negated_conjecture,
    ( r2_hidden(esk4_3(esk8_0,esk9_0,esk10_0),esk9_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_74]),c_0_26]),c_0_24]),c_0_21])]),c_0_27])).

cnf(c_0_85,negated_conjecture,
    ( r1_tarski(esk10_0,u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_81])).

cnf(c_0_86,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_orders_2(X3,X1,X4)
    | ~ r2_hidden(X4,X2)
    | ~ v12_waybel_0(X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(csr,[status(thm)],[c_0_82,c_0_36])).

cnf(c_0_87,plain,
    ( r1_orders_2(X1,k1_yellow_0(X1,X2),X3)
    | ~ r1_yellow_0(X1,X2)
    | ~ v5_orders_2(X1)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_83]),c_0_49])).

cnf(c_0_88,negated_conjecture,
    ( m1_subset_1(esk4_3(esk8_0,esk9_0,esk10_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_84])).

cnf(c_0_89,negated_conjecture,
    ( m1_subset_1(esk10_0,k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_85])).

cnf(c_0_90,plain,
    ( r2_lattice3(X1,X2,esk4_3(X1,X3,X2))
    | v1_xboole_0(X3)
    | v2_struct_0(X1)
    | ~ v1_finset_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_waybel_0(X3,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_91,plain,
    ( r2_hidden(k1_yellow_0(X1,X2),X3)
    | ~ r1_orders_2(X1,k1_yellow_0(X1,X2),X4)
    | ~ r2_hidden(X4,X3)
    | ~ v12_waybel_0(X3,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_86,c_0_49])).

cnf(c_0_92,negated_conjecture,
    ( v12_waybel_0(esk9_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_93,negated_conjecture,
    ( r1_orders_2(esk8_0,k1_yellow_0(esk8_0,X1),esk4_3(esk8_0,esk9_0,esk10_0))
    | ~ r1_yellow_0(esk8_0,X1)
    | ~ r2_lattice3(esk8_0,X1,esk4_3(esk8_0,esk9_0,esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_53]),c_0_21])])).

cnf(c_0_94,negated_conjecture,
    ( r1_yellow_0(esk8_0,esk10_0)
    | v1_xboole_0(esk10_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_89]),c_0_52]),c_0_53]),c_0_78]),c_0_26]),c_0_20]),c_0_21])])).

cnf(c_0_95,negated_conjecture,
    ( r2_lattice3(X1,esk10_0,esk4_3(X1,esk9_0,esk10_0))
    | v2_struct_0(X1)
    | ~ v1_waybel_0(esk9_0,X1)
    | ~ v4_orders_2(X1)
    | ~ m1_subset_1(esk9_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_77]),c_0_78])]),c_0_64])).

cnf(c_0_96,negated_conjecture,
    ( r2_hidden(k1_yellow_0(esk8_0,X1),esk9_0)
    | ~ r1_orders_2(esk8_0,k1_yellow_0(esk8_0,X1),X2)
    | ~ r2_hidden(X2,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_24]),c_0_92]),c_0_21])])).

cnf(c_0_97,negated_conjecture,
    ( v1_xboole_0(esk10_0)
    | r1_orders_2(esk8_0,k1_yellow_0(esk8_0,esk10_0),esk4_3(esk8_0,esk9_0,esk10_0))
    | ~ r2_lattice3(esk8_0,esk10_0,esk4_3(esk8_0,esk9_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_93,c_0_94])).

cnf(c_0_98,negated_conjecture,
    ( r2_lattice3(esk8_0,esk10_0,esk4_3(esk8_0,esk9_0,esk10_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_74]),c_0_26]),c_0_24]),c_0_21])]),c_0_27])).

cnf(c_0_99,negated_conjecture,
    ( ~ r2_hidden(k1_yellow_0(esk8_0,esk10_0),esk9_0)
    | ~ v1_waybel_0(esk9_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_100,negated_conjecture,
    ( r2_hidden(k1_yellow_0(esk8_0,X1),esk9_0)
    | ~ r1_orders_2(esk8_0,k1_yellow_0(esk8_0,X1),esk4_3(esk8_0,esk9_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_96,c_0_84])).

cnf(c_0_101,negated_conjecture,
    ( v1_xboole_0(esk10_0)
    | r1_orders_2(esk8_0,k1_yellow_0(esk8_0,esk10_0),esk4_3(esk8_0,esk9_0,esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_97,c_0_98])])).

cnf(c_0_102,negated_conjecture,
    ( ~ r2_hidden(k1_yellow_0(esk8_0,esk10_0),esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_99,c_0_74])])).

cnf(c_0_103,negated_conjecture,
    ( esk10_0 != k1_xboole_0
    | ~ v1_waybel_0(esk9_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_104,negated_conjecture,
    ( v1_xboole_0(esk10_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_101]),c_0_102])).

cnf(c_0_105,negated_conjecture,
    ( esk10_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_103,c_0_74])])).

cnf(c_0_106,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_104]),c_0_105]),
    [proof]).

%------------------------------------------------------------------------------
