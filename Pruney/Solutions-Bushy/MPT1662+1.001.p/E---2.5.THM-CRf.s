%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1662+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:33 EST 2020

% Result     : Theorem 0.36s
% Output     : CNFRefutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  133 (45921 expanded)
%              Number of clauses        :   98 (16040 expanded)
%              Number of leaves         :   17 (11207 expanded)
%              Depth                    :   34
%              Number of atoms          :  673 (476541 expanded)
%              Number of equality atoms :   28 (31688 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_waybel_0)).

fof(cc1_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v1_lattice3(X1)
       => ~ v2_struct_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattice3)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_waybel_0)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(redefinition_m2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X2,k1_zfmisc_1(X1)) )
     => ! [X3] :
          ( m2_subset_1(X3,X1,X2)
        <=> m1_subset_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_m2_subset_1)).

fof(dt_o_2_7_waybel_0,axiom,(
    ! [X1,X2] :
      ( ( v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & v1_lattice3(X1)
        & l1_orders_2(X1)
        & ~ v1_xboole_0(X2)
        & v12_waybel_0(X2,X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m2_subset_1(o_2_7_waybel_0(X1,X2),u1_struct_0(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_2_7_waybel_0)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_yellow_0)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_yellow_0)).

fof(dt_k1_yellow_0,axiom,(
    ! [X1,X2] :
      ( l1_orders_2(X1)
     => m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_0)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

fof(t6_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( r2_lattice3(X1,k1_xboole_0,X2)
            & r1_lattice3(X1,k1_xboole_0,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_yellow_0)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

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

fof(c_0_17,negated_conjecture,(
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

fof(c_0_18,plain,(
    ! [X5] :
      ( ~ l1_orders_2(X5)
      | ~ v1_lattice3(X5)
      | ~ v2_struct_0(X5) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattice3])])])).

fof(c_0_19,negated_conjecture,(
    ! [X55] :
      ( v3_orders_2(esk7_0)
      & v4_orders_2(esk7_0)
      & v5_orders_2(esk7_0)
      & v1_lattice3(esk7_0)
      & l1_orders_2(esk7_0)
      & ~ v1_xboole_0(esk8_0)
      & v12_waybel_0(esk8_0,esk7_0)
      & m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(esk7_0)))
      & ( v1_finset_1(esk9_0)
        | ~ v1_waybel_0(esk8_0,esk7_0) )
      & ( m1_subset_1(esk9_0,k1_zfmisc_1(esk8_0))
        | ~ v1_waybel_0(esk8_0,esk7_0) )
      & ( esk9_0 != k1_xboole_0
        | ~ v1_waybel_0(esk8_0,esk7_0) )
      & ( ~ r2_hidden(k1_yellow_0(esk7_0,esk9_0),esk8_0)
        | ~ v1_waybel_0(esk8_0,esk7_0) )
      & ( v1_waybel_0(esk8_0,esk7_0)
        | ~ v1_finset_1(X55)
        | ~ m1_subset_1(X55,k1_zfmisc_1(esk8_0))
        | X55 = k1_xboole_0
        | r2_hidden(k1_yellow_0(esk7_0,X55),esk8_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_17])])])])])])).

fof(c_0_20,plain,(
    ! [X41,X42] :
      ( ( ~ m1_subset_1(X41,k1_zfmisc_1(X42))
        | r1_tarski(X41,X42) )
      & ( ~ r1_tarski(X41,X42)
        | m1_subset_1(X41,k1_zfmisc_1(X42)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_21,plain,(
    ! [X24,X25,X26,X29] :
      ( ( m1_subset_1(esk3_3(X24,X25,X26),u1_struct_0(X24))
        | ~ v1_finset_1(X26)
        | ~ m1_subset_1(X26,k1_zfmisc_1(X25))
        | v1_xboole_0(X25)
        | ~ v1_waybel_0(X25,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
        | v2_struct_0(X24)
        | ~ v4_orders_2(X24)
        | ~ l1_orders_2(X24) )
      & ( r2_hidden(esk3_3(X24,X25,X26),X25)
        | ~ v1_finset_1(X26)
        | ~ m1_subset_1(X26,k1_zfmisc_1(X25))
        | v1_xboole_0(X25)
        | ~ v1_waybel_0(X25,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
        | v2_struct_0(X24)
        | ~ v4_orders_2(X24)
        | ~ l1_orders_2(X24) )
      & ( r2_lattice3(X24,X26,esk3_3(X24,X25,X26))
        | ~ v1_finset_1(X26)
        | ~ m1_subset_1(X26,k1_zfmisc_1(X25))
        | v1_xboole_0(X25)
        | ~ v1_waybel_0(X25,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
        | v2_struct_0(X24)
        | ~ v4_orders_2(X24)
        | ~ l1_orders_2(X24) )
      & ( ~ v1_xboole_0(X25)
        | v1_finset_1(esk4_2(X24,X25))
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
        | v2_struct_0(X24)
        | ~ v4_orders_2(X24)
        | ~ l1_orders_2(X24) )
      & ( v1_waybel_0(X25,X24)
        | v1_finset_1(esk4_2(X24,X25))
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
        | v2_struct_0(X24)
        | ~ v4_orders_2(X24)
        | ~ l1_orders_2(X24) )
      & ( ~ v1_xboole_0(X25)
        | m1_subset_1(esk4_2(X24,X25),k1_zfmisc_1(X25))
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
        | v2_struct_0(X24)
        | ~ v4_orders_2(X24)
        | ~ l1_orders_2(X24) )
      & ( v1_waybel_0(X25,X24)
        | m1_subset_1(esk4_2(X24,X25),k1_zfmisc_1(X25))
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
        | v2_struct_0(X24)
        | ~ v4_orders_2(X24)
        | ~ l1_orders_2(X24) )
      & ( ~ v1_xboole_0(X25)
        | ~ m1_subset_1(X29,u1_struct_0(X24))
        | ~ r2_hidden(X29,X25)
        | ~ r2_lattice3(X24,esk4_2(X24,X25),X29)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
        | v2_struct_0(X24)
        | ~ v4_orders_2(X24)
        | ~ l1_orders_2(X24) )
      & ( v1_waybel_0(X25,X24)
        | ~ m1_subset_1(X29,u1_struct_0(X24))
        | ~ r2_hidden(X29,X25)
        | ~ r2_lattice3(X24,esk4_2(X24,X25),X29)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
        | v2_struct_0(X24)
        | ~ v4_orders_2(X24)
        | ~ l1_orders_2(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t1_waybel_0])])])])])])).

cnf(c_0_22,plain,
    ( ~ l1_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( v1_lattice3(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( l1_orders_2(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_25,plain,(
    ! [X30,X31,X32] :
      ( ~ r1_tarski(X30,X31)
      | ~ r1_tarski(X31,X32)
      | r1_tarski(X30,X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( v1_waybel_0(X1,X2)
    | m1_subset_1(esk4_2(X2,X1),k1_zfmisc_1(X1))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v4_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,negated_conjecture,
    ( v4_orders_2(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,negated_conjecture,
    ( ~ v2_struct_0(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(esk8_0,u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( v1_waybel_0(esk8_0,esk7_0)
    | m1_subset_1(esk4_2(esk7_0,esk8_0),k1_zfmisc_1(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_27]),c_0_29]),c_0_24])]),c_0_30])).

fof(c_0_34,plain,(
    ! [X21,X22,X23] :
      ( ( ~ m2_subset_1(X23,X21,X22)
        | m1_subset_1(X23,X22)
        | v1_xboole_0(X21)
        | v1_xboole_0(X22)
        | ~ m1_subset_1(X22,k1_zfmisc_1(X21)) )
      & ( ~ m1_subset_1(X23,X22)
        | m2_subset_1(X23,X21,X22)
        | v1_xboole_0(X21)
        | v1_xboole_0(X22)
        | ~ m1_subset_1(X22,k1_zfmisc_1(X21)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_m2_subset_1])])])])])).

fof(c_0_35,plain,(
    ! [X18,X19] :
      ( ~ v3_orders_2(X18)
      | ~ v4_orders_2(X18)
      | ~ v5_orders_2(X18)
      | ~ v1_lattice3(X18)
      | ~ l1_orders_2(X18)
      | v1_xboole_0(X19)
      | ~ v12_waybel_0(X19,X18)
      | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
      | m2_subset_1(o_2_7_waybel_0(X18,X19),u1_struct_0(X18),X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_o_2_7_waybel_0])])])).

fof(c_0_36,plain,(
    ! [X43,X44,X45] :
      ( ~ r2_hidden(X43,X44)
      | ~ m1_subset_1(X44,k1_zfmisc_1(X45))
      | m1_subset_1(X43,X45) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_37,plain,(
    ! [X46,X47] :
      ( ( ~ v1_lattice3(X46)
        | v1_xboole_0(X47)
        | ~ v1_finset_1(X47)
        | ~ m1_subset_1(X47,k1_zfmisc_1(u1_struct_0(X46)))
        | r1_yellow_0(X46,X47)
        | v2_struct_0(X46)
        | ~ v3_orders_2(X46)
        | ~ v4_orders_2(X46)
        | ~ v5_orders_2(X46)
        | ~ l1_orders_2(X46) )
      & ( ~ v1_xboole_0(esk6_1(X46))
        | v1_lattice3(X46)
        | v2_struct_0(X46)
        | ~ v3_orders_2(X46)
        | ~ v4_orders_2(X46)
        | ~ v5_orders_2(X46)
        | ~ l1_orders_2(X46) )
      & ( v1_finset_1(esk6_1(X46))
        | v1_lattice3(X46)
        | v2_struct_0(X46)
        | ~ v3_orders_2(X46)
        | ~ v4_orders_2(X46)
        | ~ v5_orders_2(X46)
        | ~ l1_orders_2(X46) )
      & ( m1_subset_1(esk6_1(X46),k1_zfmisc_1(u1_struct_0(X46)))
        | v1_lattice3(X46)
        | v2_struct_0(X46)
        | ~ v3_orders_2(X46)
        | ~ v4_orders_2(X46)
        | ~ v5_orders_2(X46)
        | ~ l1_orders_2(X46) )
      & ( ~ r1_yellow_0(X46,esk6_1(X46))
        | v1_lattice3(X46)
        | v2_struct_0(X46)
        | ~ v3_orders_2(X46)
        | ~ v4_orders_2(X46)
        | ~ v5_orders_2(X46)
        | ~ l1_orders_2(X46) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t54_yellow_0])])])])])])).

cnf(c_0_38,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk7_0))
    | ~ r1_tarski(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_39,negated_conjecture,
    ( r1_tarski(esk4_2(esk7_0,esk8_0),esk8_0)
    | v1_waybel_0(esk8_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_33])).

cnf(c_0_40,plain,
    ( m1_subset_1(X1,X3)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ m2_subset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_41,negated_conjecture,
    ( ~ v1_xboole_0(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_42,plain,
    ( v1_xboole_0(X2)
    | m2_subset_1(o_2_7_waybel_0(X1,X2),u1_struct_0(X1),X2)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ v12_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_43,negated_conjecture,
    ( v5_orders_2(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_44,negated_conjecture,
    ( v3_orders_2(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_45,negated_conjecture,
    ( v12_waybel_0(esk8_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_46,plain,
    ( v1_waybel_0(X1,X2)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ r2_hidden(X3,X1)
    | ~ r2_lattice3(X2,esk4_2(X2,X1),X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v4_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_47,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_48,plain,
    ( v1_waybel_0(X1,X2)
    | v1_finset_1(esk4_2(X2,X1))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v4_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_49,plain,(
    ! [X35,X36,X37,X38,X39] :
      ( ( r2_lattice3(X35,X37,X36)
        | X36 != k1_yellow_0(X35,X37)
        | ~ r1_yellow_0(X35,X37)
        | ~ m1_subset_1(X36,u1_struct_0(X35))
        | ~ v5_orders_2(X35)
        | ~ l1_orders_2(X35) )
      & ( ~ m1_subset_1(X38,u1_struct_0(X35))
        | ~ r2_lattice3(X35,X37,X38)
        | r1_orders_2(X35,X36,X38)
        | X36 != k1_yellow_0(X35,X37)
        | ~ r1_yellow_0(X35,X37)
        | ~ m1_subset_1(X36,u1_struct_0(X35))
        | ~ v5_orders_2(X35)
        | ~ l1_orders_2(X35) )
      & ( X36 = k1_yellow_0(X35,X39)
        | m1_subset_1(esk5_3(X35,X36,X39),u1_struct_0(X35))
        | ~ r2_lattice3(X35,X39,X36)
        | ~ m1_subset_1(X36,u1_struct_0(X35))
        | ~ v5_orders_2(X35)
        | ~ l1_orders_2(X35) )
      & ( r1_yellow_0(X35,X39)
        | m1_subset_1(esk5_3(X35,X36,X39),u1_struct_0(X35))
        | ~ r2_lattice3(X35,X39,X36)
        | ~ m1_subset_1(X36,u1_struct_0(X35))
        | ~ v5_orders_2(X35)
        | ~ l1_orders_2(X35) )
      & ( X36 = k1_yellow_0(X35,X39)
        | r2_lattice3(X35,X39,esk5_3(X35,X36,X39))
        | ~ r2_lattice3(X35,X39,X36)
        | ~ m1_subset_1(X36,u1_struct_0(X35))
        | ~ v5_orders_2(X35)
        | ~ l1_orders_2(X35) )
      & ( r1_yellow_0(X35,X39)
        | r2_lattice3(X35,X39,esk5_3(X35,X36,X39))
        | ~ r2_lattice3(X35,X39,X36)
        | ~ m1_subset_1(X36,u1_struct_0(X35))
        | ~ v5_orders_2(X35)
        | ~ l1_orders_2(X35) )
      & ( X36 = k1_yellow_0(X35,X39)
        | ~ r1_orders_2(X35,X36,esk5_3(X35,X36,X39))
        | ~ r2_lattice3(X35,X39,X36)
        | ~ m1_subset_1(X36,u1_struct_0(X35))
        | ~ v5_orders_2(X35)
        | ~ l1_orders_2(X35) )
      & ( r1_yellow_0(X35,X39)
        | ~ r1_orders_2(X35,X36,esk5_3(X35,X36,X39))
        | ~ r2_lattice3(X35,X39,X36)
        | ~ m1_subset_1(X36,u1_struct_0(X35))
        | ~ v5_orders_2(X35)
        | ~ l1_orders_2(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_yellow_0])])])])])])).

fof(c_0_50,plain,(
    ! [X12,X13] :
      ( ~ l1_orders_2(X12)
      | m1_subset_1(k1_yellow_0(X12,X13),u1_struct_0(X12)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_yellow_0])])).

cnf(c_0_51,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_52,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(esk4_2(esk7_0,esk8_0),u1_struct_0(esk7_0))
    | v1_waybel_0(esk8_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

fof(c_0_54,plain,(
    ! [X33,X34] :
      ( ~ m1_subset_1(X33,X34)
      | v1_xboole_0(X34)
      | r2_hidden(X33,X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_55,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk7_0))
    | m1_subset_1(X1,esk8_0)
    | ~ m2_subset_1(X1,u1_struct_0(esk7_0),esk8_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_27]),c_0_41])).

cnf(c_0_56,negated_conjecture,
    ( m2_subset_1(o_2_7_waybel_0(esk7_0,esk8_0),u1_struct_0(esk7_0),esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_27]),c_0_43]),c_0_29]),c_0_44]),c_0_45]),c_0_23]),c_0_24])]),c_0_41])).

cnf(c_0_57,plain,
    ( v1_waybel_0(X1,X2)
    | v2_struct_0(X2)
    | ~ r2_lattice3(X2,esk4_2(X2,X1),X3)
    | ~ v4_orders_2(X2)
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_58,negated_conjecture,
    ( v1_waybel_0(esk8_0,esk7_0)
    | X1 = k1_xboole_0
    | r2_hidden(k1_yellow_0(esk7_0,X1),esk8_0)
    | ~ v1_finset_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_59,negated_conjecture,
    ( v1_finset_1(esk4_2(esk7_0,esk8_0))
    | v1_waybel_0(esk8_0,esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_27]),c_0_29]),c_0_24])]),c_0_30])).

cnf(c_0_60,plain,
    ( r2_lattice3(X1,X2,X3)
    | X3 != k1_yellow_0(X1,X2)
    | ~ r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_61,plain,
    ( m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_62,plain,
    ( r1_yellow_0(X1,X2)
    | v1_xboole_0(X2)
    | ~ v1_finset_1(X2)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[c_0_51,c_0_22])).

cnf(c_0_63,negated_conjecture,
    ( v1_waybel_0(esk8_0,esk7_0)
    | m1_subset_1(esk4_2(esk7_0,esk8_0),k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_64,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_65,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk7_0))
    | m1_subset_1(o_2_7_waybel_0(esk7_0,esk8_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_66,negated_conjecture,
    ( v1_waybel_0(esk8_0,esk7_0)
    | ~ r2_lattice3(esk7_0,esk4_2(esk7_0,esk8_0),X1)
    | ~ r2_hidden(X1,esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_27]),c_0_29]),c_0_24])]),c_0_30])).

cnf(c_0_67,negated_conjecture,
    ( esk4_2(esk7_0,esk8_0) = k1_xboole_0
    | v1_waybel_0(esk8_0,esk7_0)
    | r2_hidden(k1_yellow_0(esk7_0,esk4_2(esk7_0,esk8_0)),esk8_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_33]),c_0_59])).

cnf(c_0_68,plain,
    ( r2_lattice3(X1,X2,k1_yellow_0(X1,X2))
    | ~ r1_yellow_0(X1,X2)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_60]),c_0_61])).

cnf(c_0_69,negated_conjecture,
    ( r1_yellow_0(esk7_0,esk4_2(esk7_0,esk8_0))
    | v1_waybel_0(esk8_0,esk7_0)
    | v1_xboole_0(esk4_2(esk7_0,esk8_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_43]),c_0_29]),c_0_44]),c_0_23]),c_0_24])]),c_0_59])).

fof(c_0_70,plain,(
    ! [X49] :
      ( ~ v1_xboole_0(X49)
      | X49 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

fof(c_0_71,plain,(
    ! [X50,X51] :
      ( ( r2_lattice3(X50,k1_xboole_0,X51)
        | ~ m1_subset_1(X51,u1_struct_0(X50))
        | ~ l1_orders_2(X50) )
      & ( r1_lattice3(X50,k1_xboole_0,X51)
        | ~ m1_subset_1(X51,u1_struct_0(X50))
        | ~ l1_orders_2(X50) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_yellow_0])])])])).

cnf(c_0_72,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk7_0))
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_27])).

cnf(c_0_73,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk7_0))
    | r2_hidden(o_2_7_waybel_0(esk7_0,esk8_0),esk8_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_41])).

cnf(c_0_74,negated_conjecture,
    ( esk4_2(esk7_0,esk8_0) = k1_xboole_0
    | v1_waybel_0(esk8_0,esk7_0)
    | ~ r2_lattice3(esk7_0,esk4_2(esk7_0,esk8_0),k1_yellow_0(esk7_0,esk4_2(esk7_0,esk8_0))) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_75,negated_conjecture,
    ( r2_lattice3(esk7_0,esk4_2(esk7_0,esk8_0),k1_yellow_0(esk7_0,esk4_2(esk7_0,esk8_0)))
    | v1_waybel_0(esk8_0,esk7_0)
    | v1_xboole_0(esk4_2(esk7_0,esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_43]),c_0_24])])).

cnf(c_0_76,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_77,plain,
    ( r2_lattice3(X1,k1_xboole_0,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_78,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk7_0))
    | m1_subset_1(o_2_7_waybel_0(esk7_0,esk8_0),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_79,negated_conjecture,
    ( v1_waybel_0(esk8_0,esk7_0)
    | v1_xboole_0(u1_struct_0(esk7_0))
    | ~ r2_lattice3(esk7_0,esk4_2(esk7_0,esk8_0),o_2_7_waybel_0(esk7_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_73])).

cnf(c_0_80,negated_conjecture,
    ( esk4_2(esk7_0,esk8_0) = k1_xboole_0
    | v1_waybel_0(esk8_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_76])).

cnf(c_0_81,negated_conjecture,
    ( r2_lattice3(esk7_0,k1_xboole_0,o_2_7_waybel_0(esk7_0,esk8_0))
    | v1_xboole_0(u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_24])])).

fof(c_0_82,plain,(
    ! [X20] :
      ( v2_struct_0(X20)
      | ~ l1_struct_0(X20)
      | ~ v1_xboole_0(u1_struct_0(X20)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_83,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(esk8_0))
    | ~ v1_waybel_0(esk8_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_84,negated_conjecture,
    ( v1_waybel_0(esk8_0,esk7_0)
    | v1_xboole_0(u1_struct_0(esk7_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_81])).

cnf(c_0_85,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_86,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk7_0))
    | m1_subset_1(esk9_0,k1_zfmisc_1(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

fof(c_0_87,plain,(
    ! [X14] :
      ( ~ l1_orders_2(X14)
      | l1_struct_0(X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

cnf(c_0_88,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(esk8_0))
    | ~ l1_struct_0(esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_30])).

cnf(c_0_89,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_87])).

cnf(c_0_90,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),X2)
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ v1_finset_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ v1_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_91,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_24])])).

cnf(c_0_92,negated_conjecture,
    ( v1_finset_1(esk9_0)
    | ~ v1_waybel_0(esk8_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_93,negated_conjecture,
    ( r2_hidden(esk3_3(X1,esk8_0,esk9_0),esk8_0)
    | v2_struct_0(X1)
    | ~ v1_finset_1(esk9_0)
    | ~ v1_waybel_0(esk8_0,X1)
    | ~ v4_orders_2(X1)
    | ~ m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_41])).

cnf(c_0_94,negated_conjecture,
    ( v1_finset_1(esk9_0)
    | v1_xboole_0(u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_92,c_0_84])).

cnf(c_0_95,negated_conjecture,
    ( r1_tarski(esk9_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_91])).

fof(c_0_96,plain,(
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

cnf(c_0_97,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk7_0))
    | r2_hidden(esk3_3(X1,esk8_0,esk9_0),esk8_0)
    | v2_struct_0(X1)
    | ~ v1_waybel_0(esk8_0,X1)
    | ~ v4_orders_2(X1)
    | ~ m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_93,c_0_94])).

cnf(c_0_98,negated_conjecture,
    ( r1_tarski(esk9_0,u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_95])).

cnf(c_0_99,plain,
    ( r2_hidden(X4,X1)
    | ~ v12_waybel_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r2_hidden(X3,X1)
    | ~ r1_orders_2(X2,X4,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_96])).

cnf(c_0_100,plain,
    ( r1_orders_2(X2,X4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X1)
    | X4 != k1_yellow_0(X2,X3)
    | ~ r1_yellow_0(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_101,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk7_0))
    | r2_hidden(esk3_3(esk7_0,esk8_0,esk9_0),esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_84]),c_0_29]),c_0_27]),c_0_24])]),c_0_30])).

cnf(c_0_102,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_98])).

cnf(c_0_103,plain,
    ( r2_lattice3(X1,X2,esk3_3(X1,X3,X2))
    | v1_xboole_0(X3)
    | v2_struct_0(X1)
    | ~ v1_finset_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_waybel_0(X3,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_104,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_orders_2(X3,X1,X4)
    | ~ r2_hidden(X4,X2)
    | ~ v12_waybel_0(X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(csr,[status(thm)],[c_0_99,c_0_47])).

cnf(c_0_105,plain,
    ( r1_orders_2(X1,k1_yellow_0(X1,X2),X3)
    | ~ r1_yellow_0(X1,X2)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_100]),c_0_61])).

cnf(c_0_106,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk7_0))
    | m1_subset_1(esk3_3(esk7_0,esk8_0,esk9_0),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_101])).

cnf(c_0_107,negated_conjecture,
    ( r1_yellow_0(esk7_0,esk9_0)
    | v1_xboole_0(esk9_0)
    | ~ v1_finset_1(esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_102]),c_0_43]),c_0_29]),c_0_44]),c_0_23]),c_0_24])])).

cnf(c_0_108,negated_conjecture,
    ( r2_lattice3(X1,esk9_0,esk3_3(X1,esk8_0,esk9_0))
    | v2_struct_0(X1)
    | ~ v1_finset_1(esk9_0)
    | ~ v1_waybel_0(esk8_0,X1)
    | ~ v4_orders_2(X1)
    | ~ m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_91]),c_0_41])).

cnf(c_0_109,plain,
    ( r2_hidden(k1_yellow_0(X1,X2),X3)
    | ~ r1_orders_2(X1,k1_yellow_0(X1,X2),X4)
    | ~ r2_hidden(X4,X3)
    | ~ v12_waybel_0(X3,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_104,c_0_61])).

cnf(c_0_110,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk7_0))
    | r1_orders_2(esk7_0,k1_yellow_0(esk7_0,X1),esk3_3(esk7_0,esk8_0,esk9_0))
    | ~ r1_yellow_0(esk7_0,X1)
    | ~ r2_lattice3(esk7_0,X1,esk3_3(esk7_0,esk8_0,esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_106]),c_0_43]),c_0_24])])).

cnf(c_0_111,negated_conjecture,
    ( r1_yellow_0(esk7_0,esk9_0)
    | v1_xboole_0(u1_struct_0(esk7_0))
    | v1_xboole_0(esk9_0) ),
    inference(spm,[status(thm)],[c_0_107,c_0_94])).

cnf(c_0_112,negated_conjecture,
    ( r2_lattice3(X1,esk9_0,esk3_3(X1,esk8_0,esk9_0))
    | v1_xboole_0(u1_struct_0(esk7_0))
    | v2_struct_0(X1)
    | ~ v1_waybel_0(esk8_0,X1)
    | ~ v4_orders_2(X1)
    | ~ m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_108,c_0_94])).

cnf(c_0_113,negated_conjecture,
    ( r2_hidden(k1_yellow_0(esk7_0,X1),esk8_0)
    | ~ r1_orders_2(esk7_0,k1_yellow_0(esk7_0,X1),X2)
    | ~ r2_hidden(X2,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_27]),c_0_45]),c_0_24])])).

cnf(c_0_114,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk7_0))
    | v1_xboole_0(esk9_0)
    | r1_orders_2(esk7_0,k1_yellow_0(esk7_0,esk9_0),esk3_3(esk7_0,esk8_0,esk9_0))
    | ~ r2_lattice3(esk7_0,esk9_0,esk3_3(esk7_0,esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_110,c_0_111])).

cnf(c_0_115,negated_conjecture,
    ( r2_lattice3(esk7_0,esk9_0,esk3_3(esk7_0,esk8_0,esk9_0))
    | v1_xboole_0(u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_84]),c_0_29]),c_0_27]),c_0_24])]),c_0_30])).

cnf(c_0_116,negated_conjecture,
    ( ~ r2_hidden(k1_yellow_0(esk7_0,esk9_0),esk8_0)
    | ~ v1_waybel_0(esk8_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_117,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk7_0))
    | r2_hidden(k1_yellow_0(esk7_0,X1),esk8_0)
    | ~ r1_orders_2(esk7_0,k1_yellow_0(esk7_0,X1),esk3_3(esk7_0,esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_113,c_0_101])).

cnf(c_0_118,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk7_0))
    | v1_xboole_0(esk9_0)
    | r1_orders_2(esk7_0,k1_yellow_0(esk7_0,esk9_0),esk3_3(esk7_0,esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_114,c_0_115])).

cnf(c_0_119,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk7_0))
    | ~ r2_hidden(k1_yellow_0(esk7_0,esk9_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_116,c_0_84])).

cnf(c_0_120,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk7_0))
    | v1_xboole_0(esk9_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_118]),c_0_119])).

cnf(c_0_121,negated_conjecture,
    ( u1_struct_0(esk7_0) = k1_xboole_0
    | v1_xboole_0(esk9_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_120])).

cnf(c_0_122,negated_conjecture,
    ( u1_struct_0(esk7_0) = k1_xboole_0
    | esk9_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_76,c_0_121])).

cnf(c_0_123,negated_conjecture,
    ( esk9_0 = k1_xboole_0
    | v1_xboole_0(k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_122]),c_0_76])).

cnf(c_0_124,negated_conjecture,
    ( esk9_0 = k1_xboole_0
    | ~ l1_struct_0(esk7_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_122]),c_0_30]),c_0_123])).

cnf(c_0_125,negated_conjecture,
    ( esk9_0 != k1_xboole_0
    | ~ v1_waybel_0(esk8_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_126,negated_conjecture,
    ( esk9_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_89]),c_0_24])])).

cnf(c_0_127,negated_conjecture,
    ( ~ v1_waybel_0(esk8_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_125,c_0_126])])).

cnf(c_0_128,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[c_0_84,c_0_127])).

cnf(c_0_129,negated_conjecture,
    ( u1_struct_0(esk7_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_76,c_0_128])).

cnf(c_0_130,negated_conjecture,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_128,c_0_129])).

cnf(c_0_131,negated_conjecture,
    ( ~ l1_struct_0(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_129]),c_0_30]),c_0_130])])).

cnf(c_0_132,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131,c_0_89]),c_0_24])]),
    [proof]).

%------------------------------------------------------------------------------
