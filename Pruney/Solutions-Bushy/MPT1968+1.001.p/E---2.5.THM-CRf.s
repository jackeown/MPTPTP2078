%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1968+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:05 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :  113 (15204 expanded)
%              Number of clauses        :   84 (6298 expanded)
%              Number of leaves         :   14 (3486 expanded)
%              Depth                    :   21
%              Number of atoms          :  557 (158747 expanded)
%              Number of equality atoms :   75 (16979 expanded)
%              Maximal formula depth    :   24 (   5 average)
%              Maximal clause size      :   70 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(free_g1_orders_2,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
     => ! [X3,X4] :
          ( g1_orders_2(X1,X2) = g1_orders_2(X3,X4)
         => ( X1 = X3
            & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_orders_2)).

fof(dt_u1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(t17_waybel_7,conjecture,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & v1_lattice3(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( v3_orders_2(X2)
            & v4_orders_2(X2)
            & v5_orders_2(X2)
            & v1_lattice3(X2)
            & v2_lattice3(X2)
            & l1_orders_2(X2) )
         => ( g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
           => ! [X3] :
                ( ( ~ v1_xboole_0(X3)
                  & v1_waybel_0(X3,X1)
                  & v12_waybel_0(X3,X1)
                  & v1_waybel_7(X3,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
               => ( ~ v1_xboole_0(X3)
                  & v1_waybel_0(X3,X2)
                  & v12_waybel_0(X3,X2)
                  & v1_waybel_7(X3,X2)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_waybel_7)).

fof(t3_waybel_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( l1_orders_2(X2)
         => ( g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( ( X3 = X4
                        & v1_waybel_0(X3,X1) )
                     => v1_waybel_0(X4,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_waybel_0)).

fof(t25_waybel_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( l1_orders_2(X2)
         => ( g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( X3 = X4
                     => ( ( v12_waybel_0(X3,X1)
                         => v12_waybel_0(X4,X2) )
                        & ( v13_waybel_0(X3,X1)
                         => v13_waybel_0(X4,X2) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_waybel_0)).

fof(d1_waybel_7,axiom,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v1_waybel_0(X2,X1)
            & v12_waybel_0(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => ( v1_waybel_7(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ~ ( r2_hidden(k12_lattice3(X1,X3,X4),X2)
                        & ~ r2_hidden(X3,X2)
                        & ~ r2_hidden(X4,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_waybel_7)).

fof(cc2_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v2_lattice3(X1)
       => ~ v2_struct_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_lattice3)).

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

fof(redefinition_k7_domain_1,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1)
        & m1_subset_1(X3,X1) )
     => k7_domain_1(X1,X2,X3) = k2_tarski(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_domain_1)).

fof(t27_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( l1_orders_2(X2)
         => ( g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
           => ! [X3] :
                ( r2_yellow_0(X1,X3)
               => k2_yellow_0(X1,X3) = k2_yellow_0(X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_yellow_0)).

fof(t21_yellow_0,axiom,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ( v2_lattice3(X1)
      <=> ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => r2_yellow_0(X1,k2_tarski(X2,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_yellow_0)).

fof(t40_yellow_0,axiom,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => k2_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3)) = k12_lattice3(X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_yellow_0)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(c_0_14,plain,(
    ! [X17,X18,X19,X20] :
      ( ( X17 = X19
        | g1_orders_2(X17,X18) != g1_orders_2(X19,X20)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X17,X17))) )
      & ( X18 = X20
        | g1_orders_2(X17,X18) != g1_orders_2(X19,X20)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X17,X17))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_orders_2])])])])).

fof(c_0_15,plain,(
    ! [X15] :
      ( ~ l1_orders_2(X15)
      | m1_subset_1(u1_orders_2(X15),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X15)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1] :
        ( ( v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & v1_lattice3(X1)
          & v2_lattice3(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( ( v3_orders_2(X2)
              & v4_orders_2(X2)
              & v5_orders_2(X2)
              & v1_lattice3(X2)
              & v2_lattice3(X2)
              & l1_orders_2(X2) )
           => ( g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
             => ! [X3] :
                  ( ( ~ v1_xboole_0(X3)
                    & v1_waybel_0(X3,X1)
                    & v12_waybel_0(X3,X1)
                    & v1_waybel_7(X3,X1)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                 => ( ~ v1_xboole_0(X3)
                    & v1_waybel_0(X3,X2)
                    & v12_waybel_0(X3,X2)
                    & v1_waybel_7(X3,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t17_waybel_7])).

cnf(c_0_17,plain,
    ( X1 = X2
    | g1_orders_2(X3,X1) != g1_orders_2(X4,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_19,negated_conjecture,
    ( v3_orders_2(esk5_0)
    & v4_orders_2(esk5_0)
    & v5_orders_2(esk5_0)
    & v1_lattice3(esk5_0)
    & v2_lattice3(esk5_0)
    & l1_orders_2(esk5_0)
    & v3_orders_2(esk6_0)
    & v4_orders_2(esk6_0)
    & v5_orders_2(esk6_0)
    & v1_lattice3(esk6_0)
    & v2_lattice3(esk6_0)
    & l1_orders_2(esk6_0)
    & g1_orders_2(u1_struct_0(esk5_0),u1_orders_2(esk5_0)) = g1_orders_2(u1_struct_0(esk6_0),u1_orders_2(esk6_0))
    & ~ v1_xboole_0(esk7_0)
    & v1_waybel_0(esk7_0,esk5_0)
    & v12_waybel_0(esk7_0,esk5_0)
    & v1_waybel_7(esk7_0,esk5_0)
    & m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk5_0)))
    & ( v1_xboole_0(esk7_0)
      | ~ v1_waybel_0(esk7_0,esk6_0)
      | ~ v12_waybel_0(esk7_0,esk6_0)
      | ~ v1_waybel_7(esk7_0,esk6_0)
      | ~ m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk6_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])).

cnf(c_0_20,plain,
    ( u1_orders_2(X1) = X2
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(X3,X2)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_21,negated_conjecture,
    ( g1_orders_2(u1_struct_0(esk5_0),u1_orders_2(esk5_0)) = g1_orders_2(u1_struct_0(esk6_0),u1_orders_2(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_22,negated_conjecture,
    ( u1_orders_2(X1) = u1_orders_2(esk5_0)
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(esk6_0),u1_orders_2(esk6_0))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_23,negated_conjecture,
    ( l1_orders_2(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( u1_orders_2(esk5_0) = u1_orders_2(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_22]),c_0_23])])).

cnf(c_0_25,negated_conjecture,
    ( l1_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( X1 = X2
    | g1_orders_2(X1,X3) != g1_orders_2(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(u1_orders_2(esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk5_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_24]),c_0_25])])).

cnf(c_0_28,negated_conjecture,
    ( g1_orders_2(u1_struct_0(esk5_0),u1_orders_2(esk6_0)) = g1_orders_2(u1_struct_0(esk6_0),u1_orders_2(esk6_0)) ),
    inference(rw,[status(thm)],[c_0_21,c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( u1_struct_0(esk5_0) = X1
    | g1_orders_2(u1_struct_0(esk6_0),u1_orders_2(esk6_0)) != g1_orders_2(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])).

fof(c_0_30,plain,(
    ! [X36,X37,X38,X39] :
      ( ~ l1_orders_2(X36)
      | ~ l1_orders_2(X37)
      | g1_orders_2(u1_struct_0(X36),u1_orders_2(X36)) != g1_orders_2(u1_struct_0(X37),u1_orders_2(X37))
      | ~ m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X36)))
      | ~ m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X37)))
      | X38 != X39
      | ~ v1_waybel_0(X38,X36)
      | v1_waybel_0(X39,X37) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_waybel_0])])])).

cnf(c_0_31,negated_conjecture,
    ( v1_xboole_0(esk7_0)
    | ~ v1_waybel_0(esk7_0,esk6_0)
    | ~ v12_waybel_0(esk7_0,esk6_0)
    | ~ v1_waybel_7(esk7_0,esk6_0)
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_32,negated_conjecture,
    ( ~ v1_xboole_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_34,negated_conjecture,
    ( u1_struct_0(esk5_0) = u1_struct_0(esk6_0) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_35,plain,
    ( v1_waybel_0(X4,X2)
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X2)
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | X3 != X4
    | ~ v1_waybel_0(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_36,plain,(
    ! [X29,X30,X31,X32] :
      ( ( ~ v12_waybel_0(X31,X29)
        | v12_waybel_0(X32,X30)
        | X31 != X32
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X29)))
        | g1_orders_2(u1_struct_0(X29),u1_orders_2(X29)) != g1_orders_2(u1_struct_0(X30),u1_orders_2(X30))
        | ~ l1_orders_2(X30)
        | ~ l1_orders_2(X29) )
      & ( ~ v13_waybel_0(X31,X29)
        | v13_waybel_0(X32,X30)
        | X31 != X32
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X29)))
        | g1_orders_2(u1_struct_0(X29),u1_orders_2(X29)) != g1_orders_2(u1_struct_0(X30),u1_orders_2(X30))
        | ~ l1_orders_2(X30)
        | ~ l1_orders_2(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_waybel_0])])])])).

fof(c_0_37,plain,(
    ! [X8,X9,X10,X11] :
      ( ( ~ v1_waybel_7(X9,X8)
        | ~ m1_subset_1(X10,u1_struct_0(X8))
        | ~ m1_subset_1(X11,u1_struct_0(X8))
        | ~ r2_hidden(k12_lattice3(X8,X10,X11),X9)
        | r2_hidden(X10,X9)
        | r2_hidden(X11,X9)
        | v1_xboole_0(X9)
        | ~ v1_waybel_0(X9,X8)
        | ~ v12_waybel_0(X9,X8)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ v3_orders_2(X8)
        | ~ v4_orders_2(X8)
        | ~ v5_orders_2(X8)
        | ~ v2_lattice3(X8)
        | ~ l1_orders_2(X8) )
      & ( m1_subset_1(esk1_2(X8,X9),u1_struct_0(X8))
        | v1_waybel_7(X9,X8)
        | v1_xboole_0(X9)
        | ~ v1_waybel_0(X9,X8)
        | ~ v12_waybel_0(X9,X8)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ v3_orders_2(X8)
        | ~ v4_orders_2(X8)
        | ~ v5_orders_2(X8)
        | ~ v2_lattice3(X8)
        | ~ l1_orders_2(X8) )
      & ( m1_subset_1(esk2_2(X8,X9),u1_struct_0(X8))
        | v1_waybel_7(X9,X8)
        | v1_xboole_0(X9)
        | ~ v1_waybel_0(X9,X8)
        | ~ v12_waybel_0(X9,X8)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ v3_orders_2(X8)
        | ~ v4_orders_2(X8)
        | ~ v5_orders_2(X8)
        | ~ v2_lattice3(X8)
        | ~ l1_orders_2(X8) )
      & ( r2_hidden(k12_lattice3(X8,esk1_2(X8,X9),esk2_2(X8,X9)),X9)
        | v1_waybel_7(X9,X8)
        | v1_xboole_0(X9)
        | ~ v1_waybel_0(X9,X8)
        | ~ v12_waybel_0(X9,X8)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ v3_orders_2(X8)
        | ~ v4_orders_2(X8)
        | ~ v5_orders_2(X8)
        | ~ v2_lattice3(X8)
        | ~ l1_orders_2(X8) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | v1_waybel_7(X9,X8)
        | v1_xboole_0(X9)
        | ~ v1_waybel_0(X9,X8)
        | ~ v12_waybel_0(X9,X8)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ v3_orders_2(X8)
        | ~ v4_orders_2(X8)
        | ~ v5_orders_2(X8)
        | ~ v2_lattice3(X8)
        | ~ l1_orders_2(X8) )
      & ( ~ r2_hidden(esk2_2(X8,X9),X9)
        | v1_waybel_7(X9,X8)
        | v1_xboole_0(X9)
        | ~ v1_waybel_0(X9,X8)
        | ~ v12_waybel_0(X9,X8)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ v3_orders_2(X8)
        | ~ v4_orders_2(X8)
        | ~ v5_orders_2(X8)
        | ~ v2_lattice3(X8)
        | ~ l1_orders_2(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_waybel_7])])])])])])).

cnf(c_0_38,negated_conjecture,
    ( ~ v1_waybel_7(esk7_0,esk6_0)
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk6_0)))
    | ~ v12_waybel_0(esk7_0,esk6_0)
    | ~ v1_waybel_0(esk7_0,esk6_0) ),
    inference(sr,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(rw,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_40,plain,
    ( v1_waybel_0(X1,X2)
    | g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v1_waybel_0(X1,X3)
    | ~ l1_orders_2(X2)
    | ~ l1_orders_2(X3) ),
    inference(er,[status(thm)],[c_0_35])).

cnf(c_0_41,plain,
    ( v12_waybel_0(X3,X4)
    | ~ v12_waybel_0(X1,X2)
    | X1 != X3
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) != g1_orders_2(u1_struct_0(X4),u1_orders_2(X4))
    | ~ l1_orders_2(X4)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_42,plain,
    ( m1_subset_1(esk1_2(X1,X2),u1_struct_0(X1))
    | v1_waybel_7(X2,X1)
    | v1_xboole_0(X2)
    | ~ v1_waybel_0(X2,X1)
    | ~ v12_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_43,negated_conjecture,
    ( v5_orders_2(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_44,negated_conjecture,
    ( v4_orders_2(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_45,negated_conjecture,
    ( v3_orders_2(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_46,negated_conjecture,
    ( v2_lattice3(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_47,negated_conjecture,
    ( ~ v1_waybel_7(esk7_0,esk6_0)
    | ~ v12_waybel_0(esk7_0,esk6_0)
    | ~ v1_waybel_0(esk7_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_39])])).

cnf(c_0_48,negated_conjecture,
    ( v1_waybel_0(esk7_0,esk6_0)
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(esk6_0),u1_orders_2(esk6_0))
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_waybel_0(esk7_0,X1)
    | ~ l1_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_39]),c_0_23])])).

cnf(c_0_49,negated_conjecture,
    ( v1_waybel_0(esk7_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_50,plain,
    ( v12_waybel_0(X1,X2)
    | g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v12_waybel_0(X1,X3)
    | ~ l1_orders_2(X2)
    | ~ l1_orders_2(X3) ),
    inference(er,[status(thm)],[c_0_41])).

fof(c_0_51,plain,(
    ! [X5] :
      ( ~ l1_orders_2(X5)
      | ~ v2_lattice3(X5)
      | ~ v2_struct_0(X5) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_lattice3])])])).

fof(c_0_52,plain,(
    ! [X16] :
      ( v2_struct_0(X16)
      | ~ l1_struct_0(X16)
      | ~ v1_xboole_0(u1_struct_0(X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

fof(c_0_53,plain,(
    ! [X14] :
      ( ~ l1_orders_2(X14)
      | l1_struct_0(X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

cnf(c_0_54,plain,
    ( m1_subset_1(esk2_2(X1,X2),u1_struct_0(X1))
    | v1_waybel_7(X2,X1)
    | v1_xboole_0(X2)
    | ~ v1_waybel_0(X2,X1)
    | ~ v12_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_55,negated_conjecture,
    ( m1_subset_1(esk1_2(esk6_0,esk7_0),u1_struct_0(esk6_0))
    | ~ v12_waybel_0(esk7_0,esk6_0)
    | ~ v1_waybel_0(esk7_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_39]),c_0_43]),c_0_44]),c_0_45]),c_0_46]),c_0_23])]),c_0_32]),c_0_47])).

cnf(c_0_56,negated_conjecture,
    ( v1_waybel_0(esk7_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_24]),c_0_34]),c_0_34]),c_0_39]),c_0_49]),c_0_25])])).

cnf(c_0_57,negated_conjecture,
    ( v12_waybel_0(esk7_0,esk6_0)
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(esk6_0),u1_orders_2(esk6_0))
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v12_waybel_0(esk7_0,X1)
    | ~ l1_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_39]),c_0_23])])).

cnf(c_0_58,negated_conjecture,
    ( v12_waybel_0(esk7_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_59,plain,
    ( ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v2_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_60,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_61,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_62,negated_conjecture,
    ( m1_subset_1(esk2_2(esk6_0,esk7_0),u1_struct_0(esk6_0))
    | ~ v12_waybel_0(esk7_0,esk6_0)
    | ~ v1_waybel_0(esk7_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_39]),c_0_43]),c_0_44]),c_0_45]),c_0_46]),c_0_23])]),c_0_32]),c_0_47])).

fof(c_0_63,plain,(
    ! [X21,X22,X23] :
      ( v1_xboole_0(X21)
      | ~ m1_subset_1(X22,X21)
      | ~ m1_subset_1(X23,X21)
      | k7_domain_1(X21,X22,X23) = k2_tarski(X22,X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k7_domain_1])])])).

cnf(c_0_64,negated_conjecture,
    ( m1_subset_1(esk1_2(esk6_0,esk7_0),u1_struct_0(esk6_0))
    | ~ v12_waybel_0(esk7_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_56])])).

cnf(c_0_65,negated_conjecture,
    ( v12_waybel_0(esk7_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_24]),c_0_34]),c_0_34]),c_0_39]),c_0_58]),c_0_25])])).

cnf(c_0_66,plain,
    ( ~ v1_xboole_0(u1_struct_0(X1))
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61])).

cnf(c_0_67,negated_conjecture,
    ( v2_lattice3(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_68,plain,(
    ! [X33,X34,X35] :
      ( ~ l1_orders_2(X33)
      | ~ l1_orders_2(X34)
      | g1_orders_2(u1_struct_0(X33),u1_orders_2(X33)) != g1_orders_2(u1_struct_0(X34),u1_orders_2(X34))
      | ~ r2_yellow_0(X33,X35)
      | k2_yellow_0(X33,X35) = k2_yellow_0(X34,X35) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t27_yellow_0])])])).

fof(c_0_69,plain,(
    ! [X24,X25,X26] :
      ( ( ~ v2_lattice3(X24)
        | ~ m1_subset_1(X25,u1_struct_0(X24))
        | ~ m1_subset_1(X26,u1_struct_0(X24))
        | r2_yellow_0(X24,k2_tarski(X25,X26))
        | ~ v5_orders_2(X24)
        | ~ l1_orders_2(X24) )
      & ( m1_subset_1(esk3_1(X24),u1_struct_0(X24))
        | v2_lattice3(X24)
        | ~ v5_orders_2(X24)
        | ~ l1_orders_2(X24) )
      & ( m1_subset_1(esk4_1(X24),u1_struct_0(X24))
        | v2_lattice3(X24)
        | ~ v5_orders_2(X24)
        | ~ l1_orders_2(X24) )
      & ( ~ r2_yellow_0(X24,k2_tarski(esk3_1(X24),esk4_1(X24)))
        | v2_lattice3(X24)
        | ~ v5_orders_2(X24)
        | ~ l1_orders_2(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_yellow_0])])])])])).

cnf(c_0_70,negated_conjecture,
    ( m1_subset_1(esk2_2(esk6_0,esk7_0),u1_struct_0(esk6_0))
    | ~ v12_waybel_0(esk7_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_56])])).

fof(c_0_71,plain,(
    ! [X40,X41,X42] :
      ( ~ v3_orders_2(X40)
      | ~ v4_orders_2(X40)
      | ~ v5_orders_2(X40)
      | ~ v2_lattice3(X40)
      | ~ l1_orders_2(X40)
      | ~ m1_subset_1(X41,u1_struct_0(X40))
      | ~ m1_subset_1(X42,u1_struct_0(X40))
      | k2_yellow_0(X40,k7_domain_1(u1_struct_0(X40),X41,X42)) = k12_lattice3(X40,X41,X42) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t40_yellow_0])])])).

cnf(c_0_72,plain,
    ( v1_xboole_0(X1)
    | k7_domain_1(X1,X2,X3) = k2_tarski(X2,X3)
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_73,negated_conjecture,
    ( m1_subset_1(esk1_2(esk6_0,esk7_0),u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_65])])).

cnf(c_0_74,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_34]),c_0_67]),c_0_25])])).

cnf(c_0_75,plain,
    ( k2_yellow_0(X1,X3) = k2_yellow_0(X2,X3)
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X2)
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
    | ~ r2_yellow_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_76,plain,
    ( r2_yellow_0(X1,k2_tarski(X2,X3))
    | ~ v2_lattice3(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_77,negated_conjecture,
    ( m1_subset_1(esk2_2(esk6_0,esk7_0),u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_65])])).

cnf(c_0_78,plain,
    ( k2_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3)) = k12_lattice3(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_79,negated_conjecture,
    ( k7_domain_1(u1_struct_0(esk6_0),X1,esk1_2(esk6_0,esk7_0)) = k2_tarski(X1,esk1_2(esk6_0,esk7_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_74])).

fof(c_0_80,plain,(
    ! [X6,X7] : k2_tarski(X6,X7) = k2_tarski(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_81,plain,
    ( k2_yellow_0(X1,k2_tarski(X2,X3)) = k2_yellow_0(X4,k2_tarski(X2,X3))
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(X4),u1_orders_2(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X4)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_82,negated_conjecture,
    ( k7_domain_1(u1_struct_0(esk6_0),X1,esk2_2(esk6_0,esk7_0)) = k2_tarski(X1,esk2_2(esk6_0,esk7_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_77]),c_0_74])).

cnf(c_0_83,negated_conjecture,
    ( k2_yellow_0(esk6_0,k2_tarski(X1,esk1_2(esk6_0,esk7_0))) = k12_lattice3(esk6_0,X1,esk1_2(esk6_0,esk7_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_73]),c_0_43]),c_0_44]),c_0_45]),c_0_46]),c_0_23])])).

cnf(c_0_84,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_85,negated_conjecture,
    ( k2_yellow_0(esk6_0,k2_tarski(X1,esk2_2(esk6_0,esk7_0))) = k2_yellow_0(X2,k2_tarski(X1,esk2_2(esk6_0,esk7_0)))
    | g1_orders_2(u1_struct_0(esk6_0),u1_orders_2(esk6_0)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0))
    | ~ v12_waybel_0(esk7_0,esk6_0)
    | ~ l1_orders_2(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_70]),c_0_43]),c_0_46]),c_0_23])])).

cnf(c_0_86,negated_conjecture,
    ( v5_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_87,negated_conjecture,
    ( v4_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_88,negated_conjecture,
    ( v3_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_89,negated_conjecture,
    ( k2_yellow_0(esk6_0,k2_tarski(X1,esk2_2(esk6_0,esk7_0))) = k12_lattice3(esk6_0,X1,esk2_2(esk6_0,esk7_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_82]),c_0_77]),c_0_43]),c_0_44]),c_0_45]),c_0_46]),c_0_23])])).

cnf(c_0_90,negated_conjecture,
    ( k2_yellow_0(esk6_0,k2_tarski(esk1_2(esk6_0,esk7_0),X1)) = k12_lattice3(esk6_0,X1,esk1_2(esk6_0,esk7_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_91,negated_conjecture,
    ( k2_yellow_0(esk6_0,k2_tarski(X1,esk2_2(esk6_0,esk7_0))) = k2_yellow_0(X2,k2_tarski(X1,esk2_2(esk6_0,esk7_0)))
    | g1_orders_2(u1_struct_0(esk6_0),u1_orders_2(esk6_0)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0))
    | ~ l1_orders_2(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_85,c_0_65])])).

cnf(c_0_92,negated_conjecture,
    ( k2_yellow_0(esk5_0,k7_domain_1(u1_struct_0(esk6_0),X1,X2)) = k12_lattice3(esk5_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_34]),c_0_86]),c_0_87]),c_0_88]),c_0_67]),c_0_25])])).

cnf(c_0_93,negated_conjecture,
    ( k12_lattice3(esk6_0,esk2_2(esk6_0,esk7_0),esk1_2(esk6_0,esk7_0)) = k12_lattice3(esk6_0,esk1_2(esk6_0,esk7_0),esk2_2(esk6_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_73]),c_0_77])])).

cnf(c_0_94,plain,
    ( v1_waybel_7(X2,X1)
    | v1_xboole_0(X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2)
    | ~ v1_waybel_0(X2,X1)
    | ~ v12_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_95,negated_conjecture,
    ( k2_yellow_0(esk6_0,k2_tarski(esk2_2(esk6_0,esk7_0),X1)) = k2_yellow_0(X2,k2_tarski(esk2_2(esk6_0,esk7_0),X1))
    | g1_orders_2(u1_struct_0(esk6_0),u1_orders_2(esk6_0)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0))
    | ~ l1_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_91,c_0_84])).

cnf(c_0_96,negated_conjecture,
    ( k2_yellow_0(esk5_0,k2_tarski(X1,esk1_2(esk6_0,esk7_0))) = k12_lattice3(esk5_0,X1,esk1_2(esk6_0,esk7_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_79]),c_0_73])])).

cnf(c_0_97,negated_conjecture,
    ( k2_yellow_0(esk6_0,k2_tarski(esk1_2(esk6_0,esk7_0),esk2_2(esk6_0,esk7_0))) = k12_lattice3(esk6_0,esk1_2(esk6_0,esk7_0),esk2_2(esk6_0,esk7_0)) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_90]),c_0_73]),c_0_23]),c_0_77])]),c_0_93])).

cnf(c_0_98,plain,
    ( r2_hidden(k12_lattice3(X1,esk1_2(X1,X2),esk2_2(X1,X2)),X2)
    | v1_waybel_7(X2,X1)
    | v1_xboole_0(X2)
    | ~ v1_waybel_0(X2,X1)
    | ~ v12_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_99,negated_conjecture,
    ( ~ v1_waybel_7(esk7_0,esk6_0)
    | ~ v12_waybel_0(esk7_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_56])])).

cnf(c_0_100,negated_conjecture,
    ( ~ r2_hidden(esk1_2(esk6_0,esk7_0),esk7_0)
    | ~ v12_waybel_0(esk7_0,esk6_0)
    | ~ v1_waybel_0(esk7_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_39]),c_0_43]),c_0_44]),c_0_45]),c_0_46]),c_0_23])]),c_0_32]),c_0_47])).

cnf(c_0_101,plain,
    ( v1_waybel_7(X2,X1)
    | v1_xboole_0(X2)
    | ~ r2_hidden(esk2_2(X1,X2),X2)
    | ~ v1_waybel_0(X2,X1)
    | ~ v12_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_102,plain,
    ( r2_hidden(X3,X1)
    | r2_hidden(X4,X1)
    | v1_xboole_0(X1)
    | ~ v1_waybel_7(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r2_hidden(k12_lattice3(X2,X3,X4),X1)
    | ~ v1_waybel_0(X1,X2)
    | ~ v12_waybel_0(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ v2_lattice3(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_103,negated_conjecture,
    ( k12_lattice3(esk5_0,esk2_2(esk6_0,esk7_0),esk1_2(esk6_0,esk7_0)) = k12_lattice3(esk6_0,esk1_2(esk6_0,esk7_0),esk2_2(esk6_0,esk7_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_96]),c_0_34]),c_0_24]),c_0_73]),c_0_25]),c_0_77])]),c_0_84]),c_0_97])).

cnf(c_0_104,negated_conjecture,
    ( r2_hidden(k12_lattice3(esk6_0,esk1_2(esk6_0,esk7_0),esk2_2(esk6_0,esk7_0)),esk7_0)
    | ~ v12_waybel_0(esk7_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_39]),c_0_43]),c_0_44]),c_0_45]),c_0_46]),c_0_23])]),c_0_32]),c_0_56])]),c_0_99])).

cnf(c_0_105,negated_conjecture,
    ( ~ r2_hidden(esk1_2(esk6_0,esk7_0),esk7_0)
    | ~ v12_waybel_0(esk7_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_100,c_0_56])])).

cnf(c_0_106,negated_conjecture,
    ( ~ r2_hidden(esk2_2(esk6_0,esk7_0),esk7_0)
    | ~ v12_waybel_0(esk7_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_39]),c_0_43]),c_0_44]),c_0_45]),c_0_46]),c_0_23])]),c_0_32]),c_0_56])]),c_0_99])).

cnf(c_0_107,negated_conjecture,
    ( r2_hidden(esk1_2(esk6_0,esk7_0),X1)
    | r2_hidden(esk2_2(esk6_0,esk7_0),X1)
    | v1_xboole_0(X1)
    | ~ r2_hidden(k12_lattice3(esk6_0,esk1_2(esk6_0,esk7_0),esk2_2(esk6_0,esk7_0)),X1)
    | ~ v1_waybel_7(X1,esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk6_0)))
    | ~ v12_waybel_0(X1,esk5_0)
    | ~ v1_waybel_0(X1,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_103]),c_0_34]),c_0_34]),c_0_73]),c_0_34]),c_0_77]),c_0_86]),c_0_87]),c_0_88]),c_0_67]),c_0_25])])).

cnf(c_0_108,negated_conjecture,
    ( r2_hidden(k12_lattice3(esk6_0,esk1_2(esk6_0,esk7_0),esk2_2(esk6_0,esk7_0)),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_104,c_0_65])])).

cnf(c_0_109,negated_conjecture,
    ( v1_waybel_7(esk7_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_110,negated_conjecture,
    ( ~ r2_hidden(esk1_2(esk6_0,esk7_0),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_105,c_0_65])])).

cnf(c_0_111,negated_conjecture,
    ( ~ r2_hidden(esk2_2(esk6_0,esk7_0),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_106,c_0_65])])).

cnf(c_0_112,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_108]),c_0_109]),c_0_39]),c_0_58]),c_0_49])]),c_0_110]),c_0_111]),c_0_32]),
    [proof]).

%------------------------------------------------------------------------------
